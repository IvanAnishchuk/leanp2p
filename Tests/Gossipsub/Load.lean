import Tests.Support
import Tests.Gossipsub.Identity
import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Eth2

/-!
# Gossipsub suite: the router under a consensus load

The router core with Lighthouse's peer target and a consensus node's
topics: 200 peers, each subscribed to every topic of one fork digest
(`Libp2p.Eth2.topicsPerFork`, 205), under the consensus parameters with
Lighthouse's score profile. The core runs the events one after another,
as the node's loop does.

The load is the rate that the seen cache covers, 341 messages per second
(`Libp2p.Eth2.Gossip`), with a heartbeat every 700 ms. Each message comes
from a mesh peer, waits for validation, and goes out to the rest of the
mesh. Every tenth message is a large one (a block or a column), so 7
other mesh peers send IDONTWANT for it (gossipsub v1.2). The data is a
32-byte handle, as on the node's payload path, where the core never sees
the payload.

The checks hold each cost to a quarter of its budget on one core: a
message to a quarter of its 2.9 ms share, and a heartbeat to a quarter
of its 700 ms. The margin leaves room for a slower machine. The run
prints the measured costs.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Load

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Core

/-- The peer count: Lighthouse's default target. -/
def peerCount : Nat := 200

/-- The messages per second that the seen cache covers. -/
def messagesPerSecond : Nat := 341

/-- The peers. One byte each names 255 peers, so the count fits. -/
private def peers : List Peer := (List.range peerCount).map (Tests.Gossipsub.Identity.peer ·.succ)

/-- The topics of one fork digest. -/
private def digest : ByteArray := ⟨#[0x80, 0x49, 0xf2, 0x50]⟩

private def kinds : List Libp2p.Eth2.Kind :=
  [.beaconBlock, .beaconAggregateAndProof, .voluntaryExit, .proposerSlashing, .attesterSlashing,
   .syncCommitteeContributionAndProof, .blsToExecutionChange, .lightClientFinalityUpdate,
   .lightClientOptimisticUpdate] ++
  (List.range Libp2p.Eth2.Constants.attestationSubnetCount).map .beaconAttestation ++
  (List.range Libp2p.Eth2.Constants.syncCommitteeSubnetCount).map .syncCommittee ++
  (List.range Libp2p.Eth2.Constants.dataColumnSidecarSubnetCount).map .dataColumnSidecar

private def topics : Array TopicId := (kinds.map fun k => ⟨Libp2p.Eth2.topicOf digest k⟩).toArray

/-- The consensus parameters, scored, with the handle as the message id. -/
private def params : Params :=
  let chain : Libp2p.Eth2.Chain :=
    { schedule := [{ epoch := 0, digest, enrForkId := digest ++ ⟨Array.replicate 12 0⟩ }]
      slotDurationMs := 12000, slotsPerEpoch := 32, genesisTime := 0 }
  { Libp2p.Eth2.Scoring.scoredParams chain digest 500000 100 with msgId := fun m => ⟨m.data.getD []⟩ }

private def emptyState : State :=
  { peers := {}, mesh := [], fanout := []
    mcache := Cache.MessageIndex.empty params.window
    seen := Cache.SeenIndex.empty params.seen
    backoff := [], iwant := [], topics := [], now := 0, lastHeartbeat := 0 }

/-- The 32-byte handle of message `k`. -/
private def handle (k : Nat) : List Nat := (List.range 32).map fun i => k / 256 ^ (i % 4) % 256 + i

private def messageOf (t : TopicId) (k : Nat) : Message :=
  { «from» := none, data := some (handle k), seqno := none, topic := t, signature := none, key := none }

private def rpcBytes (r : Rpc.RPC) : List Nat := Pb.encodeMessage r

/-- An RPC that carries one message. -/
private def publishBytes (m : Message) : List Nat :=
  rpcBytes { subscriptions := [], publish := [m], control := none }

/-- An RPC that carries one IDONTWANT. -/
private def dontWantBytes (id : MessageId) : List Nat :=
  let c : Rpc.ControlMessage :=
    { ihave := [], iwant := [], graft := [], prune := [], idontwant := [{ messageIds := [id] }] }
  rpcBytes { subscriptions := [], publish := [], control := some c }

/-- One event, and the state after it. A protocol error keeps the state. -/
private def run1 (s : State) (e : Event) : State × Nat :=
  match step params s e with
  | .ok (s', acts) => (s', acts.length)
  | .error _ => (s, 0)

/-- The state after the joins, the subscriptions both ways, and the
first heartbeat, which fills every mesh. -/
private def setup (_ : Unit) : State := Id.run do
  let mut s := emptyState
  for t in topics do s := (run1 s (.subscribe t)).1
  let subs : Rpc.RPC :=
    { subscriptions := topics.toList.map fun t => { subscribe := true, topicid := t.name }
      publish := [], control := none }
  -- Each peer has its own address, so the colocation term stays 0.
  for (p, i) in peers.zip (List.range peerCount) do
    s := (run1 s (.peerJoined p .meshsub)).1
    s := (run1 s (.peerInfo p true (some [10, 0, i / 256, i % 256]))).1
    s := (run1 s (.rpc p (rpcBytes subs))).1
  (run1 s (.tick 700 peers)).1

/-- The mesh of a topic. -/
private def meshPeers (s : State) (t : TopicId) : List Peer :=
  ((s.mesh.find? (·.1 == t)).map (·.2)).getD []

/-- Run `count` messages from `start` at the consensus rate, with the
heartbeats between them. The answer: the state, the time in messages,
the time in heartbeats, the heartbeat count, and the actions. -/
private def drive (s0 : State) (start count : Nat) : IO (State × Nat × Nat × Nat × Nat) := do
  let mut s := s0
  let mut msgNs := 0
  let mut beatNs := 0
  let mut beats := 0
  let mut acts := 0
  let perBeat := messagesPerSecond * 700 / 1000
  for k in [start:start + count] do
    let t := topics[k % topics.size]?.getD ⟨""⟩
    let mesh := meshPeers s t
    let src := mesh[k % max mesh.length 1]?.getD (Tests.Gossipsub.Identity.peer 1)
    let m := messageOf t k
    let id : MessageId := ⟨handle k⟩
    let t0 ← IO.monoNanosNow
    let (s1, a1) := run1 { s with now := s.now + 3 } (.rpc src (publishBytes m))
    let (s2, a2) := run1 s1 (.validated id src .accept)
    let mut s3 := s2
    if k % 10 == 0 then
      for q in (mesh.filter (· != src)).take 7 do
        s3 := (run1 s3 (.rpc q (dontWantBytes id))).1
    -- Force the state before the clock reads again.
    let held := s3.seen.index.size
    let t1 ← IO.monoNanosNow
    msgNs := msgNs + (t1 - t0)
    acts := acts + a1 + a2 + (if held == 0 then 1 else 0)
    s := s3
    -- 239 messages 3 ms apart span one heartbeat interval.
    if (k + 1) % perBeat == 0 then
      let t2 ← IO.monoNanosNow
      let (s4, a4) := run1 s (.tick s.now peers)
      let meshes := s4.mesh.length
      let t3 ← IO.monoNanosNow
      beatNs := beatNs + (t3 - t2)
      beats := beats + 1
      acts := acts + a4 + (if meshes == 0 then 1 else 0)
      s := s4
  return (s, msgNs, beatNs, beats, acts)

def run (r : Runner) : IO Unit := do
  r.section "gossipsub router under a consensus load" "phase0 p2p-interface.md, Lighthouse's peer target"
  let s := setup ()
  let meshed := topics.toList.map fun t => (meshPeers s t).length
  r.check s!"load: every topic meshes with D = 8 of {peerCount} peers" (meshed.all (· == 8))
  -- A warm-up fills the message cache and the IDONTWANT table, then the
  -- measured run.
  let (s, _, _, _, _) ← drive s 0 1000
  let count := 3410
  let (s, msgNs, beatNs, beats, _) ← drive s 1000 count
  let perMsgUs := msgNs / count / 1000
  let perBeatMs := beatNs / max beats 1 / 1000000
  IO.println s!"load: {count} messages, {perMsgUs} us each; {beats} heartbeats, {perBeatMs} ms each; \
    {s.dontSend.size} IDONTWANT pairs, {s.peers.size} peers"
  r.check "load: a message costs under a quarter of its 2.9 ms share"
    (perMsgUs * messagesPerSecond * 4 < 1000000)
  r.check "load: a heartbeat costs under a quarter of its 700 ms"
    (perBeatMs * 4 < 700)

end Tests.Gossipsub.Load
