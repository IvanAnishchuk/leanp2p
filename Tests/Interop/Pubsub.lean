import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Host
import Libp2p.Mux
import Libp2p.Security.Noise
import Libp2p.Protocols.Identify
import Libp2p.Protocols.Gossipsub.HostSeam
import Libp2p.Protocols.Gossipsub.Node

/-!
# The pubsub interop driver

The Lean side of the checks against go-libp2p-pubsub v0.19.0 over
go-libp2p v0.51.0; `scripts/pubsub-interop.sh` builds the go side
(`scripts/pubsub-go/`) and runs every mode below over loopback TCP. Our
host runs TCP, Noise, and yamux, and answers identify with its signed
peer record.

* `pubsub-interop record SEQ ADDR...`: print the hex of our signed peer
  record (seed `L`); go's `verify` consumes it.
* `pubsub-interop floodsub ADDR`: a node with floodsub on dials a go
  floodsub-only node, publishes `from-lean`, and waits for `from-go`.
  go speaks no meshsub, so both directions negotiate `/floodsub/1.0.0`.
* `pubsub-interop px-accept ADDR`: dial a go gossipsub node with peer
  exchange on and a full mesh, raise its app score above
  `acceptPXThreshold`, and join the topic. go prunes our GRAFT with the
  other peers of its mesh and their signed records. The check passes
  once we connect to one of them; their addresses reach us only through
  the records.
* `pubsub-interop px-send PORT SECS`: listen with peer exchange on and a
  mesh bound of two, ask each new peer for identify so its signed record
  enters the host, and serve for SECS seconds. The script's go nodes
  join; the last one's GRAFT finds the mesh full and gets our prune,
  and that go node passes when it connects to a peer it only learned
  from our records.

Each mode exits 0 on success. The seeds are one character, 32 times, as
the go side builds them.
-/

set_option autoImplicit false

namespace Tests.Interop.Pubsub

open Conc (Async Chan OnceRef Clock)
open Libp2p.Identity Libp2p.Core
open Libp2p.Protocols Libp2p.Protocols.Gossipsub

/-- The topic of every mode. -/
def topic : TopicId := ⟨"interop"⟩

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : Async α :=
  throw <| IO.userError s!"lean: {msg}"

/-- The value of an `Except`, or a failure that names the error. -/
def orFail {ε α : Type} [Repr ε] (what : String) : Except ε α → Async α
  | .ok a => return a
  | .error e => fail s!"{what}: {(repr e).pretty}"

/-- Our identity: the Ed25519 key of 32 bytes of `L`. -/
def leanKey : Async PrivKey :=
  orFail "key" (PrivKey.ofData? .ed25519 ⟨Array.replicate 32 'L'.toNat.toUInt8⟩)

/-- A multiaddr from its text form. -/
def addr (s : String) : Async Multiformats.Multiaddr :=
  orFail s!"address {s}" (Multiformats.Multiaddr.parse? s)

/-- Sleep on the system clock. -/
def sleep (ms : Nat) : Async Unit := do
  let timer ← (Clock.system.after ms : BaseIO (Conc.Park Unit))
  discard <| Conc.select #[timer]

/-- A running host and its gossipsub node. -/
structure Running where
  host : Libp2p.Host.Host
  node : Node.Node

/-- Our host over TCP, Noise, and yamux, with identify answering our
signed peer record over `listen`, and the gossipsub node over it. When
`fetch` is set, each new connection runs an identify request, so the
peer's signed record enters the host. -/
def start (config : Node.Config) (listen : Option String) (fetch : Bool) : Async Running := do
  let key ← leanKey
  let noise ← orFail "noise" (← (Libp2p.Security.Noise.Config.generate key).run)
  let pub ← orFail "public key" key.toPublic
  let hostConfig : Libp2p.Host.Config := {
    identity := key
    transports := [Streams.Tcp.transport]
    security := [Libp2p.Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux] }
  let host ← orFail "host" (← (Libp2p.Host.Host.new hostConfig : BaseIO _))
  let bound ← match listen with
    | some text => do pure [← orFail "listen" (← host.startListening (← addr text))]
    | none => pure []
  -- The record names the bound address; the seq is the start time, so a
  -- restart signs a newer one (RFC 0003).
  let seq ← (Clock.system.nowMs : BaseIO Nat)
  let spr ← orFail "record" (← host.signRecord bound seq)
  let protocols := [Identify.protocolId.toString, Constants.meshsubV13Id.toString,
    Constants.meshsubV12Id.toString, Constants.meshsubId.toString] ++
    (if config.floodsub then [Constants.floodsubId.toString] else [])
  host.setHandler (Identify.respondHandler pub (bound.map (·.toBytes)) protocols "leanp2p-interop"
    (some (Bytes.toNatList spr)))
  if fetch then
    -- The notifiee must not park, so each request runs on its own task;
    -- the host's close ends the stream it waits on.
    let owner ← Conc.TaskSet.new
    host.addNotifiee fun
      | .connected peer _ _ _ => owner.spawn do
          match ← Identify.request host peer Clock.system 5000 with
          | .ok () => IO.println s!"IDENTIFIED {peer}"
          | .error e => IO.eprintln s!"lean: identify {peer}: {e}"
      | _ => pure ()
  let node ← (Node.start (HostSeam.ofHost host) config : BaseIO Node.Node)
  for a in bound do
    IO.println s!"ADDR {a}/p2p/{host.localPeer}"
  -- The script reads the address from a file, so it must not wait in
  -- the buffer.
  (← IO.getStdout).flush
  return { host, node }

/-- Dial a go node at its full multiaddr. -/
def dial (running : Running) (text : String) : Async PeerId := do
  orFail s!"dial {text}" (← running.host.dial (← addr text))

/-- Stop the node, then the host. -/
def stop (running : Running) : Async Unit := do
  running.node.stop
  running.host.close

/-- Wait up to `ms` for `cond`, checking every 100 ms. -/
def waitFor (ms : Nat) (cond : Async Bool) : Async Bool := do
  let mut left := ms
  while 0 < left do
    if ← cond then return true
    sleep 100
    left := left - 100
  cond

def recordMode (args : List String) : Async UInt32 := do
  let some seqText := args.head? | fail "record SEQ ADDR..."
  let some seq := seqText.toNat? | fail s!"seq {seqText}"
  let key ← leanKey
  let peer ← orFail "peer id" (key.toPublic.bind PeerId.ofPubKey)
  let addrs ← args.tail.mapM addr
  match ← (PeerRecord.sign key { peerId := peer, seq, addrs }).run with
  | .ok e => IO.println (Bytes.toHex e.marshal); return 0
  | .error e => fail s!"sign: {repr e}"

def floodsubMode (target : String) : Async UInt32 := do
  -- Each RPC from go goes to stderr, so a failed run shows what arrived.
  let trace : Peer → List Nat → BaseIO Unit := fun q bytes => do
    let t ← Clock.system.nowMs
    discard (IO.eprintln s!"{t} RPC from {q}: {bytes.length} bytes" |>.toBaseIO)
  let traceOut : Peer → Rpc.RPC → BaseIO Unit := fun q rpc => do
    let t ← Clock.system.nowMs
    discard (IO.eprintln
      s!"{t} RPC to {q}: {rpc.subscriptions.length} subs, {rpc.publish.length} msgs" |>.toBaseIO)
  let running ← start { floodsub := true, onRpc := trace, onSend := traceOut } none false
  let got : OnceRef Bool ← OnceRef.new false
  -- The message id is the data, so each publish carries a count; a
  -- repeat would be a duplicate.
  let count : OnceRef Nat ← OnceRef.new 0
  let publishNext : Async Unit := do
    let n ← (count.updateGet fun n => (n + 1, n + 1) : BaseIO Nat)
    discard (running.node.publish topic s!"from-lean-{n}".toUTF8 : BaseIO Bool)
  let goPrefix := Bytes.toNatList "from-go".toUTF8
  discard <| dial running target
  discard (running.node.subscribe topic fun m => do
    if (m.data.getD []).take goPrefix.length == goPrefix then got.set true : BaseIO Bool)
  let ok ← waitFor 20000 do
    publishNext
    (got.get : BaseIO Bool)
  -- Keep publishing a moment, so go sees `from-lean` too.
  for _ in [0:5] do
    publishNext
    sleep 200
  stop running
  if ok then IO.println "LEAN-GOT from-go"; return 0
  IO.println "LEAN-TIMEOUT"
  return 1

def pxAcceptMode (target : String) : Async UInt32 := do
  -- The app score counts, so the bootstrapper scores above the
  -- threshold of 0, as the spec's bootstrapper setup does.
  let base := Core.defaults
  let params : Core.Params :=
    { base with score := { base.score with global := { base.score.global with appSpecificWeight := 1 } } }
  let running ← start { params } none false
  let g ← dial running target
  discard (running.node.setAppScore g 10 : BaseIO Bool)
  discard (running.node.subscribe topic (fun _ => pure ()) : BaseIO Bool)
  let found : OnceRef (Option PeerId) ← OnceRef.new none
  let ok ← waitFor 25000 do
    let others := (← (running.host.peers : BaseIO (List PeerId))).filter (· != g)
    if let some q := others.head? then
      found.set (some q)
      return true
    return false
  stop running
  match ← (found.get : BaseIO (Option PeerId)) with
  | some q => IO.println s!"PX-CONNECTED {q}"
  | none => IO.println "PX-TIMEOUT"
  return if ok then 0 else 1

def pxSendMode (port : String) (secs : Nat) : Async UInt32 := do
  let base := Core.defaults
  let params : Core.Params :=
    { base with mesh := { d := 2, dLow := 1, dHigh := 2, dScore := 1, dLazy := 6 }, dOut := 0,
                doPX := true }
  let running ← start { params } (some s!"/ip4/127.0.0.1/tcp/{port}") true
  discard (running.node.subscribe topic (fun _ => pure ()) : BaseIO Bool)
  sleep (secs * 1000)
  stop running
  return 0

def main (args : List String) : IO UInt32 := do
  let run : Async UInt32 := match args with
    | "record" :: rest => recordMode rest
    | ["floodsub", target] => floodsubMode target
    | ["px-accept", target] => pxAcceptMode target
    | ["px-send", port, secs] => pxSendMode port (secs.toNat?.getD 30)
    | _ => fail "modes: record, floodsub ADDR, px-accept ADDR, px-send PORT SECS"
  try
    run.run
  catch e =>
    IO.eprintln (toString e)
    return 1

end Tests.Interop.Pubsub

def main (args : List String) : IO UInt32 := Tests.Interop.Pubsub.main args
