import Libp2p.Eth2

/-!
# `eth2-probe`: the consensus service against a live network

`eth2-probe <testnet-dir> [--ip <a.b.c.d>] [--port <p>] [--seconds <n>] [--boot-enr <enr>]...`
joins the network of a testnet directory with leanp2p's consensus service
(`Libp2p.Eth2.Service`) and checks what the other clients answer. It needs no chain
model, so it never validates a message: every held gossip message gets IGNORE, which
costs the sender nothing.

The directory holds `config.yaml` and `genesis.ssz`, and it may hold `boot_enr.yaml` or
`bootstrap_nodes.txt`. TCP and discv5 listen on `--port` (default 9000), and QUIC on the
next port. The probe binds `--ip`, default `0.0.0.0`, and names it in its record.

The probe subscribes to the block, the aggregate, every attestation subnet, and every
column subnet. Each peer whose `Status` arrives gets four requests once:

* `BeaconBlocksByRange` for the 8 slots up to its head
* `DataColumnSidecarsByRange` for columns 0 and 1 of the 2 slots up to its head
* `Ping`
* `MetaData` v3

It prints one line per event and per answer, then a count of each. It exits 0 when a peer
sent its `Status`, a block arrived on gossip, and a peer answered the block range with
at least one chunk whose context is our digest.
-/

set_option autoImplicit false

namespace Eth2Probe

open Conc Libp2p.Eth2 Libp2p.Identity

structure Args where
  dir : String := ""
  ip : List Nat := [0, 0, 0, 0]
  port : Nat := 9000
  seconds : Nat := 120
  boot : List String := []

def parse : List String → Args → Except String Args
  | [], a => if a.dir.isEmpty then throw "the testnet directory is required" else pure a
  | "--ip" :: s :: rest, a =>
    let parts := (s.splitOn ".").filterMap (·.toNat?)
    if parts.length == 4 && parts.all (· < 256) then parse rest { a with ip := parts }
    else throw s!"--ip: {s} is no IPv4 address"
  | "--port" :: p :: rest, a => match p.toNat? with
    | some n => parse rest { a with port := n }
    | none => throw s!"--port: {p} is no number"
  | "--seconds" :: n :: rest, a => match n.toNat? with
    | some s => parse rest { a with seconds := s }
    | none => throw s!"--seconds: {n} is no number"
  | "--boot-enr" :: e :: rest, a => parse rest { a with boot := a.boot ++ [e] }
  | flag :: rest, a =>
    if flag.startsWith "--" || !a.dir.isEmpty then throw s!"unexpected argument {flag}"
    else parse rest { a with dir := flag }

/-- The records of a text file: each line's `enr:` text, when it has one. -/
def recordsIn (text : String) : List Enr :=
  text.splitOn "\n" |>.filterMap fun line =>
    match line.splitOn "enr:" with
    | _ :: rest :: _ =>
      let body := ("enr:" ++ rest).trimAscii.toString
      let body := ((body.splitOn "'").headD body).splitOn "\"" |>.headD body
      (Enr.ofText? body).toOption
    | _ => none

def recordsOf (path : String) : IO (List Enr) := do
  if ← System.FilePath.pathExists path then return recordsIn (← IO.FS.readFile path)
  return []

/-- The counts the summary prints. -/
structure Counts where
  peers : Nat := 0
  statuses : Nat := 0
  blocks : Nat := 0
  aggregates : Nat := 0
  attestations : Nat := 0
  columns : Nat := 0
  rangeChunks : Nat := 0
  rangeContextOk : Bool := false
  columnChunks : Nat := 0
  pings : Nat := 0
  metadata : Nat := 0
  goodbyes : Nat := 0

def short (p : PeerId) : String :=
  let s := toString p
  s.drop (s.length - min s.length 8) |>.toString

/-- The four requests to a peer at its head slot. -/
def probePeer (s : Service) (counts : OnceRef Counts) (digest : ByteArray) (peer : PeerId)
    (head : Nat) : Async Unit := do
  match ← s.request peer blocksByRangeMethod (some (blocksByRangeRequest (head - min head 7) 8)) with
  | .ok chunks =>
    let ok := chunks.filter (·.result matches .success)
    IO.println s!"blocks-by-range {short peer}: {ok.length} chunks, contexts \
      {(ok.map (Bytes.toHex ·.context)).eraseDups}"
    (counts.update fun c => { c with
      rangeChunks := c.rangeChunks + ok.length
      rangeContextOk := c.rangeContextOk || ok.any (·.context == digest) } : BaseIO Unit)
  | .error e => IO.println s!"blocks-by-range {short peer}: {repr e}"
  match ← s.request peer columnsByRangeMethod (some (columnsByRangeRequest (head - min head 1) 2 [0, 1])) with
  | .ok chunks =>
    let ok := chunks.filter (·.result matches .success)
    IO.println s!"columns-by-range {short peer}: {ok.length} chunks"
    (counts.update fun c => { c with columnChunks := c.columnChunks + ok.length } : BaseIO Unit)
  | .error e => IO.println s!"columns-by-range {short peer}: {repr e}"
  match ← s.request peer pingMethod (some (Chain.le64 0)) with
  | .ok [c] =>
    IO.println s!"ping {short peer}: seq {le64At c.payload 0}"
    (counts.update fun c => { c with pings := c.pings + 1 } : BaseIO Unit)
  | other => IO.println s!"ping {short peer}: {match other with | .error e => reprStr e | .ok cs => s!"{cs.length} chunks"}"
  match ← s.request peer metadataV3Method none with
  | .ok [c] =>
    let m := MetaData.decodeV3? c.payload
    IO.println s!"metadata {short peer}: cgc {(m.map (·.custodyGroupCount)).getD 0}, attnets \
      {(m.map (Bytes.toHex ·.attnets)).getD "?"}"
    (counts.update fun c => { c with metadata := c.metadata + 1 } : BaseIO Unit)
  | other => IO.println s!"metadata {short peer}: {match other with | .error e => reprStr e | .ok cs => s!"{cs.length} chunks"}"

def run (a : Args) : IO UInt32 := do
  let chain ← IO.ofExcept (Config.chainOf (← IO.FS.readFile s!"{a.dir}/config.yaml")
    (← IO.FS.readBinFile s!"{a.dir}/genesis.ssz"))
  let digest ← digestNow chain
  let boot := a.boot.filterMap (fun t => (Enr.ofText? t).toOption) ++
    (← recordsOf s!"{a.dir}/boot_enr.yaml") ++ (← recordsOf s!"{a.dir}/bootstrap_nodes.txt")
  IO.println s!"eth2-probe: digest {Bytes.toHex digest}, {boot.length} boot records"
  let key ← match ← Crypto.secp256k1Generate.run with
    | .ok k => IO.ofExcept ((PrivKey.ofData? .secp256k1 k.bytes).mapError fun _ => "the key does not build")
    | .error _ => throw (IO.userError "the secp256k1 generator failed")
  let events ← (OnceRef.new (#[] : Array Event) : BaseIO _)
  let s ← Async.run (Service.start {
    chain, key, ip := a.ip, tcpPort := a.port, quicPort := some (a.port + 1), discPort := a.port
    bootEnrs := boot, advert := { cgc := 128 }
    onEvent := fun e => events.update (·.push e) })
  IO.println s!"eth2-probe: listening on {s.listenAddrs.map toString}"
  IO.println s!"eth2-probe: record {(← s.localEnr).toText}"
  -- The subscriptions post to the gossipsub node's control queue of 64 inputs, so a
  -- refused one waits and posts again.
  let kinds : List Kind := [.beaconBlock, .beaconAggregateAndProof] ++
    (List.range Constants.attestationSubnetCount).map .beaconAttestation ++
    (List.range Constants.dataColumnSidecarSubnetCount).map .dataColumnSidecar
  for k in kinds do
    for _ in [0:100] do
      if ← s.subscribe k then break
      IO.sleep 10
  let counts ← (OnceRef.new ({} : Counts) : BaseIO _)
  let probed ← (OnceRef.new ([] : List PeerId) : BaseIO _)
  let tasks ← (TaskSet.new : BaseIO TaskSet)
  let deadline := (← IO.monoMsNow) + a.seconds * 1000
  while (← IO.monoMsNow) < deadline do
    IO.sleep 200
    for e in ← (events.updateGet fun q => (q, #[]) : BaseIO (Array Event)) do
      match e with
      | .connected p out =>
        IO.println s!"peer + {short p} {if out then "out" else "in"}"
        counts.update fun c => { c with peers := c.peers + 1 }
      | .disconnected p => IO.println s!"peer - {short p}"
      | .status p st =>
        IO.println s!"status {short p}: digest {Bytes.toHex st.forkDigest}, head slot {st.headSlot}, \
          finalized epoch {st.finalizedEpoch}"
        counts.update fun c => { c with statuses := c.statuses + 1 }
        let first ← probed.updateGet fun l => (!l.contains p, if l.contains p then l else p :: l)
        if first then tasks.spawn (probePeer s counts digest p st.headSlot)
      | .gossip k id src ssz =>
        discard <| s.report id src .ignore
        counts.update fun c => match k with
          | .beaconBlock => { c with blocks := c.blocks + 1 }
          | .beaconAggregateAndProof => { c with aggregates := c.aggregates + 1 }
          | .beaconAttestation _ => { c with attestations := c.attestations + 1 }
          | .dataColumnSidecar _ => { c with columns := c.columns + 1 }
          | _ => c
        if k matches .beaconBlock then IO.println s!"gossip block from {short src}: {ssz.size} bytes"
      | .goodbye p r =>
        IO.println s!"goodbye {short p}: reason {r}"
        counts.update fun c => { c with goodbyes := c.goodbyes + 1 }
  Async.run tasks.joinAll
  Async.run s.stop
  let c ← counts.get
  IO.println s!"eth2-probe: peers {c.peers}, statuses {c.statuses}, gossip blocks {c.blocks}, \
    aggregates {c.aggregates}, attestations {c.attestations}, columns {c.columns}, \
    range chunks {c.rangeChunks} (context ours: {c.rangeContextOk}), column chunks {c.columnChunks}, \
    pings {c.pings}, metadata {c.metadata}, goodbyes {c.goodbyes}"
  return if c.statuses > 0 && c.blocks > 0 && c.rangeChunks > 0 && c.rangeContextOk then 0 else 1

end Eth2Probe

def main (args : List String) : IO UInt32 := do
  match Eth2Probe.parse args {} with
  | .ok a => Eth2Probe.run a
  | .error e =>
    IO.eprintln s!"eth2-probe: {e}"
    IO.eprintln "usage: eth2-probe <testnet-dir> [--ip <a.b.c.d>] [--port <p>] [--seconds <n>] [--boot-enr <enr>]..."
    return 2
