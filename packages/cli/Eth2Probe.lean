import Libp2p.Eth2

/-!
# `eth2-probe`: the consensus service against a live network

`eth2-probe <testnet-dir> [--ip <a.b.c.d>] [--port <p>] [--seconds <n>] [--boot-enr <enr>]...
[--slot-ms <ms>] [--slots-per-epoch <n>] [--no-scoring] [--no-quic]` joins the network of
a testnet directory with leanp2p's consensus service (`Libp2p.Eth2.Service`) and checks
what the other clients answer. It needs no chain model, so it never validates a message:
every held gossip message gets IGNORE, which costs the sender nothing. The probe then
forwards nothing, so from one epoch on, the peers' mesh delivery term scores it down and
they prune it from many meshes. `--no-scoring` runs the router unscored, and `--no-quic`
leaves QUIC out.

The directory may hold `boot_enr.yaml` or `bootstrap_nodes.txt`. The probe takes its
fork from the `eth2` field of the first boot record: the digest and the `ENRForkID`, as
one schedule entry at epoch 0. So the probe follows no fork. `--slot-ms` (default 12000)
and `--slots-per-epoch` (default 32) set the gossip parameters. TCP and discv5 listen on
`--port` (default 9000), and QUIC on the next port. The probe binds `--ip`, default
`0.0.0.0`, and names it in its record.

The probe stands in for a client, so it writes the few SSZ payloads it sends and reads
the few fields it prints (`StandIn`). leanp2p's library decodes no SSZ.

The probe subscribes to the block, the aggregate, every attestation subnet, and every
column subnet. Each peer whose `Status` arrives gets these requests once:

* `BeaconBlocksByHead` for 4 blocks of the ancestry of its head root
* `BeaconBlocksByRange` for the 8 slots up to its head
* `DataColumnSidecarsByRange` for columns 0 and 1 of the 2 slots up to its head
* `Ping`
* `MetaData` v3
* `GetLightClientFinalityUpdate` and `GetLightClientOptimisticUpdate`
* `GetLightClientBootstrap` for its finalized root

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
  scoring : Bool := true
  quic : Bool := true
  slotMs : Nat := 12000
  slotsPerEpoch : Nat := 32

def parse : List String → Args → Except String Args
  | [], a => if a.dir.isEmpty then throw "the testnet directory is required" else pure a
  | "--no-quic" :: rest, a => parse rest { a with quic := false }
  | "--slot-ms" :: n :: rest, a => match n.toNat? with
    | some s => parse rest { a with slotMs := s }
    | none => throw s!"--slot-ms: {n} is no number"
  | "--slots-per-epoch" :: n :: rest, a => match n.toNat? with
    | some s => parse rest { a with slotsPerEpoch := s }
    | none => throw s!"--slots-per-epoch: {n} is no number"
  | "--no-scoring" :: rest, a => parse rest { a with scoring := false }
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

/-! ## The stand-in client's SSZ

The fixed layouts of the few payloads the probe sends and prints (fulu
`p2p-interface.md`). A client has these from its SSZ library. -/

namespace StandIn

/-- The `Status` v2 of a node at genesis: the digest, then the zero
checkpoint and head (phase0 "Status v1"), and slot 0. -/
def genesisStatus (digest : ByteArray) : ByteArray :=
  digest ++ ⟨Array.replicate (statusLen - 4) 0⟩

/-- The `finalized_root`, `head_root`, and `head_slot` of a `Status` v2. -/
def finalizedRoot (st : ByteArray) : ByteArray := st.extract 4 36
def headRoot (st : ByteArray) : ByteArray := st.extract 44 76
def headSlot (st : ByteArray) : Nat := le64At st 76
def finalizedEpoch (st : ByteArray) : Nat := le64At st 36

/-- Our `MetaData`: `seq_number` 0, no subnets, and the custody group
count. v2 is v3 without the count. -/
def metaData (cgc : Nat) : MetaData :=
  let v3 := le64 0 ++ ⟨Array.replicate 9 0⟩ ++ le64 cgc
  { seq := 0, v3, v2 := v3.extract 0 metaDataV2Len }

/-- The `custody_group_count` and the `attnets` of a `MetaData` v3. -/
def custody (md : ByteArray) : Nat := le64At md 17
def attnets (md : ByteArray) : ByteArray := md.extract 8 16

/-- `BeaconBlocksByRange`: `start_slot`, `count`, and `step` 1. -/
def blocksByRange (startSlot count : Nat) : ByteArray := le64 startSlot ++ le64 count ++ le64 1

/-- `BeaconBlocksByHead`: the root, then `count`. -/
def blocksByHead (root : ByteArray) (count : Nat) : ByteArray := root ++ le64 count

/-- `DataColumnSidecarsByRange`: `start_slot`, `count`, the 4-byte
offset 20 of the column list, then the columns. -/
def columnsByRange (startSlot count : Nat) (columns : List Nat) : ByteArray :=
  columns.foldl (fun b c => b ++ le64 c) (le64 startSlot ++ le64 count ++ (le64 20).extract 0 4)

end StandIn

/-- The schedule of one entry from the `eth2` field of a record. -/
def chainOf (r : Enr) (slotMs slotsPerEpoch : Nat) : Option Chain := do
  let forkId ← enrForkId? r
  return { schedule := [{ epoch := 0, digest := forkId.extract 0 4, enrForkId := forkId }]
           slotDurationMs := slotMs, slotsPerEpoch, genesisTime := 0 }

/-- The events that wait for the loop. -/
def eventSlots : Nat := 4096

/-- The pause between two reports of the gossip so far. -/
def reportEveryMs : Nat := 10000

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
  /-- The light-client requests that a peer answered with data. -/
  lightClient : Nat := 0

def short (p : PeerId) : String :=
  let s := toString p
  s.drop (s.length - min s.length 8) |>.toString

/-- The requests to a peer at its head slot (the module doc lists them). -/
def probePeer (s : Service) (counts : OnceRef Counts) (digest : ByteArray) (peer : PeerId)
    (status : ByteArray) : Async Unit := do
  let head := StandIn.headSlot status
  match ← s.request peer blocksByHeadMethod (some (StandIn.blocksByHead (StandIn.headRoot status) 4)) with
  | .ok chunks =>
    let ok := chunks.filter (·.result matches .success)
    IO.println s!"blocks-by-head {short peer}: {ok.length} chunks"
  | .error e => IO.println s!"blocks-by-head {short peer}: {repr e}"
  match ← s.request peer blocksByRangeMethod (some (StandIn.blocksByRange (head - min head 7) 8)) with
  | .ok chunks =>
    let ok := chunks.filter (·.result matches .success)
    IO.println s!"blocks-by-range {short peer}: {ok.length} chunks, contexts \
      {(ok.map (Bytes.toHex ·.context)).eraseDups}"
    (counts.update fun c => { c with
      rangeChunks := c.rangeChunks + ok.length
      rangeContextOk := c.rangeContextOk || ok.any (·.context == digest) } : BaseIO Unit)
  | .error e => IO.println s!"blocks-by-range {short peer}: {repr e}"
  match ← s.request peer columnsByRangeMethod (some (StandIn.columnsByRange (head - min head 1) 2 [0, 1])) with
  | .ok chunks =>
    let ok := chunks.filter (·.result matches .success)
    IO.println s!"columns-by-range {short peer}: {ok.length} chunks"
    (counts.update fun c => { c with columnChunks := c.columnChunks + ok.length } : BaseIO Unit)
  | .error e => IO.println s!"columns-by-range {short peer}: {repr e}"
  match ← s.request peer pingMethod (some (le64 0)) with
  | .ok [c] =>
    IO.println s!"ping {short peer}: seq {le64At c.payload 0}"
    (counts.update fun c => { c with pings := c.pings + 1 } : BaseIO Unit)
  | other => IO.println s!"ping {short peer}: {match other with | .error e => reprStr e | .ok cs => s!"{cs.length} chunks"}"
  match ← s.request peer metadataV3Method none with
  | .ok [c] =>
    IO.println s!"metadata {short peer}: cgc {StandIn.custody c.payload}, attnets \
      {Bytes.toHex (StandIn.attnets c.payload)}"
    (counts.update fun c => { c with metadata := c.metadata + 1 } : BaseIO Unit)
  | other => IO.println s!"metadata {short peer}: {match other with | .error e => reprStr e | .ok cs => s!"{cs.length} chunks"}"
  -- The light-client methods: one chunk, or an error code.
  let lightClient (name : String) (m : Libp2p.Protocols.ReqResp.Method) (p : Option ByteArray) :
      Async Unit := do
    match ← s.request peer m p with
    | .ok chunks =>
      IO.println s!"{name} {short peer}: {chunks.map fun c => s!"{repr c.result} {c.payload.size} bytes"}"
      if chunks.any (·.result matches .success) then
        (counts.update fun c => { c with lightClient := c.lightClient + 1 } : BaseIO Unit)
    | .error e => IO.println s!"{name} {short peer}: {repr e}"
  lightClient "light-client-finality-update" lightClientFinalityUpdateMethod none
  lightClient "light-client-optimistic-update" lightClientOptimisticUpdateMethod none
  lightClient "light-client-bootstrap" lightClientBootstrapMethod (some (StandIn.finalizedRoot status))

def run (a : Args) : IO UInt32 := do
  let boot := a.boot.filterMap (fun t => (Enr.ofText? t).toOption) ++
    (← recordsOf s!"{a.dir}/boot_enr.yaml") ++ (← recordsOf s!"{a.dir}/bootstrap_nodes.txt")
  let some chain := boot.findSome? (chainOf · a.slotMs a.slotsPerEpoch)
    | throw (IO.userError "no boot record has an eth2 field of 16 bytes")
  let digest ← digestNow chain
  IO.println s!"eth2-probe: digest {Bytes.toHex digest}, {boot.length} boot records"
  let key ← match ← Crypto.secp256k1Generate.run with
    | .ok k => IO.ofExcept ((PrivKey.ofData? .secp256k1 k.bytes).mapError fun _ => "the key does not build")
    | .error _ => throw (IO.userError "the secp256k1 generator failed")
  -- The service's callback must not park, so it offers each event to a
  -- bounded queue, and a full queue drops the event and counts it.
  let events ← (Chan.new eventSlots (by decide) : BaseIO (Chan Event))
  let dropped ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let s ← Async.run (Service.start {
    chain, key, ip := a.ip, tcpPort := a.port
    status := StandIn.genesisStatus digest, metaData := StandIn.metaData 128
    -- QUIC on the next port, as Lighthouse's default does.
    quicPort := if a.quic then some (a.port + 1) else none
    discPort := a.port
    bootEnrs := boot, advert := { cgc := 128 }, scoring := a.scoring
    onEvent := fun e => do
      unless ← events.trySend e do dropped.update (· + 1) })
  IO.println s!"eth2-probe: listening on {s.listenAddrs.map toString}"
  IO.println s!"eth2-probe: record {(← s.localEnr).toText}"
  let kinds : List Kind := [.beaconBlock, .beaconAggregateAndProof] ++
    (List.range Constants.attestationSubnetCount).map .beaconAttestation ++
    (List.range Constants.dataColumnSidecarSubnetCount).map .dataColumnSidecar
  for k in kinds do
    unless ← Async.run (s.subscribe k) do IO.eprintln s!"eth2-probe: the subscribe to {repr k} failed"
  let counts ← (OnceRef.new ({} : Counts) : BaseIO _)
  let probed ← (OnceRef.new ([] : List PeerId) : BaseIO _)
  let tasks ← (TaskSet.new : BaseIO TaskSet)
  let start ← IO.monoMsNow
  let deadline := start + a.seconds * 1000
  let mut nextReport := start + reportEveryMs
  repeat
    let now ← IO.monoMsNow
    if deadline ≤ now then break
    -- Park: an event wakes it, and so does the timer of the next report
    -- or of the end.
    let timer ← (Park.sleep (min deadline nextReport - now) none : BaseIO (Park (Option Event)))
    let got ← Async.run (select #[Park.recv events id, timer])
    if let some e := got then
      match e with
      | .connected p out =>
        IO.println s!"peer + {short p} {if out then "out" else "in"}"
        counts.update fun c => { c with peers := c.peers + 1 }
      | .disconnected p => IO.println s!"peer - {short p}"
      | .status p st =>
        IO.println s!"status {short p}: digest {Bytes.toHex (statusDigest st)}, head slot \
          {StandIn.headSlot st}, finalized epoch {StandIn.finalizedEpoch st}"
        counts.update fun c => { c with statuses := c.statuses + 1 }
        let first ← probed.updateGet fun l => (!l.contains p, if l.contains p then l else p :: l)
        if first then tasks.spawn (probePeer s counts digest p st)
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
      | .metaData p seq md =>
        IO.println s!"metadata refresh {short p}: seq {seq}, cgc {StandIn.custody md}"
      | .unresponsive p => IO.println s!"no ping answer {short p}"
      | .tooManyRequests p m => IO.println s!"too many requests {short p}: {m}"
      | .partialColumn .. | .partialGossip .. => pure ()
    -- Every 10 s, the gossip so far, so a stall shows as a flat count.
    let now ← IO.monoMsNow
    if now ≥ nextReport then
      nextReport := now + reportEveryMs
      let c ← counts.get
      let meshed ← match ← Async.run s.gossip.stats with
        | some st => pure s!"{(st.mesh.filter (·.2 > 0)).length} of {st.topics} topics meshed, \
            router peers {st.peers}, seen {st.seen}, cached {st.cached}, pending {st.pending}, \
            dontSend {st.dontSend}, dropped {st.dropped}, v1.2 {st.v12Peers}, v1.3 {st.v13Peers}"
        | none => pure "no stats"
      IO.println s!"t+{(now - start) / 1000}s: peers {(← s.peers).length}, blocks {c.blocks}, \
        aggregates {c.aggregates}, attestations {c.attestations}, columns {c.columns}, \
        events dropped {← dropped.get}, {meshed}"
  -- The stop closes the host, which wakes every request the tasks park
  -- on, and then the join returns at once.
  Async.run s.stop
  Async.run tasks.joinAll
  let c ← counts.get
  IO.println s!"eth2-probe: peers {c.peers}, statuses {c.statuses}, gossip blocks {c.blocks}, \
    aggregates {c.aggregates}, attestations {c.attestations}, columns {c.columns}, \
    range chunks {c.rangeChunks} (context ours: {c.rangeContextOk}), column chunks {c.columnChunks}, \
    pings {c.pings}, metadata {c.metadata}, goodbyes {c.goodbyes}, \
    light-client answers {c.lightClient}"
  return if c.statuses > 0 && c.blocks > 0 && c.rangeChunks > 0 && c.rangeContextOk then 0 else 1

end Eth2Probe

def main (args : List String) : IO UInt32 := do
  match Eth2Probe.parse args {} with
  | .ok a => Eth2Probe.run a
  | .error e =>
    IO.eprintln s!"eth2-probe: {e}"
    IO.eprintln "usage: eth2-probe <testnet-dir> [--ip <a.b.c.d>] [--port <p>] [--seconds <n>] [--boot-enr <enr>]... [--slot-ms <ms>] [--slots-per-epoch <n>] [--no-scoring] [--no-quic]"
    return 2
