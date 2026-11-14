import Tests.Support
import Tests.HostPair
import Libp2p.Protocols.Gossipsub.Node

/-!
# Gossipsub on real hosts: joins, leaves, and the reconcile

Spike P3 over two real hosts on the sim (`Tests.HostPair`). The host's
connection events reach the router, a peer with no meshsub handler
leaves the router after its writer's negotiation fails, and a closed
session leaves it too. Each wait advances the test clock by one
heartbeat at a time, with a bound.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.HostNode

open Conc
open Libp2p.Protocols.Gossipsub
open Tests.HostPair (Pair hostPair)

/-- Park for 50 ms of real time. A park holds no thread, so the suite's
other tasks run under `LEAN_NUM_THREADS=1`, where `IO.sleep` would
block the one worker. -/
private def nap : Async Unit := do
  let t ← (Park.sleep 50 () : BaseIO (Park Unit))
  select #[t]

/-- Wait until `ok` holds for the node's peer list, for up to `rounds`
heartbeats. A stream's negotiation runs on tasks, outside the test
clock, so the wait polls in real time (50 ms steps, ten per heartbeat)
and advances the clock one heartbeat only after the tasks had their
time. A clock that races ahead fires yamux's 10 s write deadline
(`Yamux.writeDeadlineMs`) on a connection whose tasks never ran, so a
caller keeps one wait's `rounds` under 10. -/
private def waitPeers (tc : TestClock) (node : Node.Node) (ok : List Peer → Bool)
    (rounds : Nat := 8) : Async Bool := do
  for i in [0:rounds * 10] do
    if let some s ← node.scores then
      if ok (s.map (·.1)) then return true
    nap
    if i % 10 == 9 then tc.advance 1000
  return false

/-- Wait, as `waitPeers` does, until `ok` holds for the node's stats. -/
private def waitStats (tc : TestClock) (node : Node.Node) (ok : Node.Stats → Bool)
    (rounds : Nat := 8) : Async Bool := do
  for i in [0:rounds * 10] do
    if let some s ← node.stats then
      if ok s then return true
    nap
    if i % 10 == 9 then tc.advance 1000
  return false

def run (r : Runner) : IO Unit := Async.run do
  r.section "gossipsub on hosts" "(spike P3: connection events and the reconcile)"
  -- The client runs no gossipsub: the server's writer fails to
  -- negotiate meshsub, and the reconcile drops the client.
  do
    let p ← hostPair
    let server ← (Node.start (HostSeam.ofHost p.server) { clock := p.clock.clock } : BaseIO Node.Node)
    let clientPeer := p.client.localPeer
    -- The server registers its side of the session on its own task, so
    -- the join comes from the start's peer list or the first reconcile.
    r.check "hosts: a peer connected before the start joins"
      (← waitPeers p.clock server (·.contains clientPeer) 3)
    r.check "hosts: a peer with no meshsub leaves the router"
      (← waitPeers p.clock server (!·.contains clientPeer))
    server.stop
    r.check "hosts: the pair closes with no fault (unsupported)" (← p.close).isNone
  -- Both run gossipsub, the client first, so its handler is set before the
  -- server's writer opens. The peer stays, then leaves at the close.
  do
    let p ← hostPair
    let client ← (Node.start (HostSeam.ofHost p.client) { clock := p.clock.clock } : BaseIO Node.Node)
    let server ← (Node.start (HostSeam.ofHost p.server) { clock := p.clock.clock } : BaseIO Node.Node)
    let clientPeer := p.client.localPeer
    r.check "hosts: a meshsub peer joins"
      (← waitPeers p.clock server (·.contains clientPeer) 5)
    r.check "hosts: the client learns the server through its stream"
      (← waitPeers p.clock client (·.contains p.serverPeer) 8)
    -- The metrics snapshot (spike P12) sees the one peer and no topic.
    match ← server.stats with
    | some s =>
      r.check "hosts: stats count one peer, no topic, no drop"
        (s.peers == 1 && s.topics == 0 && s.pending == 0 && s.dropped == 0)
    | none => r.check "hosts: stats answer" false
    -- Both nodes serve /meshsub/1.3.0, so the pair negotiates it. The
    -- writer records the version when its open returns, on its own task.
    r.check "hosts: the pair negotiates meshsub 1.3.0"
      (← waitStats p.clock server (·.v13Peers == 1) 3)
    r.check "hosts: a meshsub peer stays across heartbeats"
      ((← waitPeers p.clock server (!·.contains clientPeer) 5) == false)
    discard (p.client.closePeer p.serverPeer : BaseIO Bool)
    r.check "hosts: a closed session leaves the router"
      (← waitPeers p.clock server (!·.contains clientPeer))
    client.stop
    server.stop
    r.check "hosts: the pair closes with no fault (meshsub)" (← p.close).isNone
  -- The ByteArray payload path (spike F3): a 2 MiB message crosses two
  -- nodes, and the receiver's validation sees the bytes intact.
  do
    let p ← hostPair
    let idOf (topic : String) (d : ByteArray) : MessageId :=
      ⟨topic.length :: d.size % 256 :: d.size / 256 % 256 :: d.size / 65536 % 256 ::
        (d.extract 0 8).toList.map (·.toNat)⟩
    let held : Chan (MessageId × Peer) ← Chan.new 4
    let cap := Libp2p.Protocols.Constants.gossipMaxMessageSize
    let base : Node.Config :=
      { clock := p.clock.clock, payloadId := some idOf, maxRpcSize := cap
        params := { Core.defaults with validateMessages := true } }
    let server ← (Node.start (HostSeam.ofHost p.server)
      { base with onValidate := fun _ id src => discard (held.trySend (id, src)) } : BaseIO Node.Node)
    let client ← (Node.start (HostSeam.ofHost p.client) base : BaseIO Node.Node)
    let topic : TopicId := ⟨"blocks"⟩
    discard (server.subscribe topic (fun _ => pure ()) : BaseIO Bool)
    discard (client.subscribe topic (fun _ => pure ()) : BaseIO Bool)
    -- Wait for the mesh: the client grafts the server at a heartbeat.
    discard <| waitStats p.clock client (fun s => s.mesh.any (·.2 == 1)) 5
    let payload : ByteArray := ⟨(Array.range (2 * 2 ^ 20)).map (·.toUInt8)⟩
    r.check "payload path: publish takes 2 MiB" (← (client.publish topic payload : BaseIO Bool))
    let mut got : Option (MessageId × Peer) := none
    for i in [0:80] do
      if let some h ← (held.tryRecv : BaseIO _) then
        got := some h
        break
      nap
      if i % 10 == 9 then p.clock.advance 1000
    match got with
    | some (id, src) =>
      r.check "payload path: the receiver holds it from the client" (src == p.client.localPeer)
      r.check "payload path: the receiver's bytes equal the sent bytes"
        ((← (server.payload id : BaseIO _)).map (·.toList) == some payload.toList)
      r.check "payload path: the handle is the id function's"
        (id == idOf topic.name payload)
    | none => r.check "payload path: the receiver holds the message" false
    client.stop
    server.stop
    r.check "hosts: the pair closes with no fault (payload)" (← p.close).isNone
  -- A message over the RPC cap (spike P7): the node counts it in
  -- `dropped`. The client's cap is 64 bytes. The server subscribes, so
  -- the client's publish goes to it through the fanout.
  do
    let p ← hostPair
    let server ← (Node.start (HostSeam.ofHost p.server) { clock := p.clock.clock } :
      BaseIO Node.Node)
    let client ← (Node.start (HostSeam.ofHost p.client)
      { clock := p.clock.clock, maxRpcSize := 64 } : BaseIO Node.Node)
    let topic : TopicId := ⟨"blocks"⟩
    discard (server.subscribe topic (fun _ => pure ()) : BaseIO Bool)
    discard <| waitPeers p.clock client (·.contains p.serverPeer) 4
    -- The server's subscription reaches the client on the server's stream.
    discard <| waitStats p.clock server (·.v13Peers == 1) 4
    let mut counted := false
    for _ in [0:4] do
      discard (client.publish topic ⟨Array.replicate 200 7⟩ : BaseIO Bool)
      if ← waitStats p.clock client (·.dropped ≥ 1) 1 then
        counted := true
        break
    r.check "hosts: the node counts an RPC over the cap in dropped" counted
    client.stop
    server.stop
    r.check "hosts: the pair closes with no fault (over cap)" (← p.close).isNone
  -- An explicit peer (spike P9): the client keeps the server, and dials it
  -- again at its next check after the session ends.
  do
    let p ← hostPair
    let cfg : Node.Config :=
      { clock := p.clock.clock, explicitPeers := [p.serverPeer], explicitCheckMs := 2000 }
    let server ← (Node.start (HostSeam.ofHost p.server) { clock := p.clock.clock } :
      BaseIO Node.Node)
    let client ← (Node.start (HostSeam.ofHost p.client) cfg : BaseIO Node.Node)
    r.check "hosts: the explicit peer joins"
      (← waitPeers p.clock client (·.contains p.serverPeer) 4)
    -- The redial can come within one check interval, so the test reads
    -- the end from the host's event. The router's peer list can miss it.
    let ended : Chan Unit ← Chan.new 4
    (p.client.addNotifiee fun
      | .disconnected q _ => if q == p.serverPeer then discard (ended.trySend ()) else pure ()
      | _ => pure () : BaseIO Unit)
    discard (p.client.closePeer p.serverPeer : BaseIO Bool)
    r.check "hosts: the explicit peer's session ends" ((← ended.recv).isSome)
    -- The next check, at most 2000 ms of test clock away, dials it again.
    let mut back := false
    for i in [0:80] do
      if ← (p.client.connected p.serverPeer : BaseIO Bool) then
        back := true
        break
      nap
      if i % 10 == 9 then p.clock.advance 1000
    r.check "hosts: the node dials its explicit peer again" back
    r.check "hosts: the explicit peer is in the router again"
      (← waitPeers p.clock client (·.contains p.serverPeer) 4)
    client.stop
    server.stop
    r.check "hosts: the pair closes with no fault (explicit)" (← p.close).isNone

/-- Spike P13 over two hosts: both nodes request partial messages on one
topic. Each stream opens with the Extensions message, the subscriptions
carry the flags, and a partial message crosses to the other node's
application. -/
def runPartial (r : Runner) : IO Unit := Async.run do
  r.section "gossipsub partial messages on hosts" "(spike P13: gossipsub-v1.3.md, partial-messages.md)"
  let p ← hostPair
  let topic : TopicId := ⟨"columns"⟩
  let params : Core.Params :=
    { Core.defaults with partialTopics := [(topic, { requests := true, supports := true })] }
  -- The server logs whether the client's first RPC carried extensions,
  -- and every partial message it hands to the application.
  let firsts : Chan Bool ← Chan.new 4
  let seenFrom ← OnceRef.new ([] : List Peer)
  let extCount ← OnceRef.new 0
  let onRpc (q : Peer) (bytes : List Nat) : BaseIO Unit := do
    let ext := match Pb.decodeMessage? (α := Rpc.RPC) bytes with
      | .ok (rpc, _) => (rpc.control.bind (·.extensions)).isSome
      | .error _ => false
    if ext then extCount.update (· + 1)
    let first ← seenFrom.updateGet fun l => (!l.contains q, if l.contains q then l else q :: l)
    if first then discard (firsts.trySend ext)
  let partials : Chan (Peer × Rpc.PartialMessage) ← Chan.new 4
  let server ← (Node.start (HostSeam.ofHost p.server)
    { clock := p.clock.clock, params, onRpc,
      onPartial := fun q pm => discard (partials.trySend (q, pm)) } : BaseIO Node.Node)
  let client ← (Node.start (HostSeam.ofHost p.client) { clock := p.clock.clock, params } :
    BaseIO Node.Node)
  discard (server.subscribe topic (fun _ => pure ()) : BaseIO Bool)
  discard (client.subscribe topic (fun _ => pure ()) : BaseIO Bool)
  -- The client grafts the server at a heartbeat.
  r.check "partial: the mesh forms"
    (← waitStats p.clock client (fun s => s.mesh.any (·.2 == 1)) 6)
  r.check "partial: the client's first RPC carries the Extensions message"
    ((← (firsts.tryRecv : BaseIO _)) == some true)
  -- The client's router learned the server's request from its SubOpts.
  let mut offered : List (Peer × Bool) := []
  for i in [0:40] do
    if let some ps ← client.partialPeers topic then
      if !ps.isEmpty then
        offered := ps
        break
    nap
    if i % 10 == 9 then p.clock.advance 1000
  r.check "partial: the client offers partial messages to the requesting server"
    (offered == [(p.serverPeer, true)])
  let pm : Rpc.PartialMessage :=
    { topicId := some (Bytes.toNatList (Bytes.ofString topic.name)), groupId := some [0, 1, 2],
      partialMessage := some [7, 7, 7], partsMetadata := some [0xff] }
  r.check "partial: the node accepts the send" (← (client.sendPartial p.serverPeer pm : BaseIO Bool))
  let mut got : Option (Peer × Rpc.PartialMessage) := none
  for i in [0:40] do
    if let some x ← (partials.tryRecv : BaseIO _) then
      got := some x
      break
    nap
    if i % 10 == 9 then p.clock.advance 1000
  r.check "partial: the server's application gets the partial message from the client"
    (got == some (p.client.localPeer, pm))
  r.check "partial: the node accepts the application's judgment"
    (← (server.judgePartial p.client.localPeer topic true : BaseIO Bool))
  -- Many RPCs crossed by now: subscriptions, grafts, the partial message.
  r.check "partial: the client sent the Extensions message once"
    ((← (extCount.get : BaseIO Nat)) == 1)
  client.stop
  server.stop
  r.check "partial: the pair closes with no fault" (← p.close).isNone

end Tests.Gossipsub.HostNode
