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

/-- Wait until `ok` holds for the node's peer list, for up to `rounds`
heartbeats. A stream's negotiation runs on tasks, not on the test
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
    (IO.sleep 50 : IO Unit)
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
  -- Both run gossipsub, the client first, so its handler is up before the
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
    r.check "hosts: a meshsub peer stays across heartbeats"
      ((← waitPeers p.clock server (!·.contains clientPeer) 5) == false)
    discard (p.client.closePeer p.serverPeer : BaseIO Bool)
    r.check "hosts: a closed session leaves the router"
      (← waitPeers p.clock server (!·.contains clientPeer))
    client.stop
    server.stop
    r.check "hosts: the pair closes with no fault (meshsub)" (← p.close).isNone

end Tests.Gossipsub.HostNode
