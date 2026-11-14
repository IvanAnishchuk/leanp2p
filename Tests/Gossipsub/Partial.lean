import Tests.Support
import Tests.Gossipsub.Identity
import Libp2p.Protocols.Gossipsub.Core

/-!
# Gossipsub suite: v1.3 extensions and partial messages

Spike P13. The wire checks pin the new fields to `extensions.proto`:
`SubOpts` fields 3 and 4, `ControlMessage` field 6 with the
`partialMessages` extension at field 10, and the RPC's `partial` field
10. The core checks follow `partial-messages.md`: the behavior table of
`SubOpts`, the gossip rule, the application interface, and the scoring
of protocol violations from `gossipsub-v1.3.md`.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Partial

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Core

/-! ## Fixtures -/

private def ta : TopicId := ⟨"t"⟩
private def tb : TopicId := ⟨"u"⟩

private def pa : Peer := Identity.peer 1
private def pb : Peer := Identity.peer 2
private def pc : Peer := Identity.peer 3

private def prims : Sign.Prims :=
  { unmarshalKey := fun _ => none
    inlineKey := fun _ => none
    idOfKey := fun _ => []
    verify := fun _ _ _ => false }

/-- The topic parameters: first deliveries count up to 10, and an
invalid delivery is counted. -/
private def topicScore : Score.TopicParams :=
  { topicWeight := 1
    timeInMeshWeight := 0
    timeInMeshQuantum := 1
    timeInMeshCap := 0
    firstMessageDeliveriesWeight := 1
    firstMessageDeliveriesDecay := scoreScale
    firstMessageDeliveriesCap := 10
    meshMessageDeliveriesWeight := 0
    meshMessageDeliveriesDecay := scoreScale
    meshMessageDeliveriesThreshold := 0
    meshMessageDeliveriesCap := 0
    meshMessageDeliveriesActivation := 0
    meshMessageDeliveriesWindow := 0
    meshFailurePenaltyWeight := 0
    meshFailurePenaltyDecay := scoreScale
    invalidMessageDeliveriesWeight := -1
    invalidMessageDeliveriesDecay := scoreScale }

/-- Topic `t` requests partial messages, and topic `u` takes full messages.
A mesh of one, so a heartbeat leaves the other peers for gossip. -/
private def params : Params :=
  { defaults with
    mesh := { d := 1, dLow := 1, dHigh := 1, dScore := 1, dLazy := 2 }
    dOut := 0
    prims := prims
    msgId := fun m => ⟨m.data.getD []⟩
    score := { defaults.score with topics := fun t => if t = ta then some topicScore else none }
    partialTopics := [(ta, { requests := true, supports := true })] }

private def peerRec : PeerData :=
  { score := Score.PeerState.zero, proto := .meshsub, subs := [ta] }

/-- Three peers on topic `t`. The mesh holds `pb`. -/
private def start : State :=
  { peers := [(pa, peerRec), (pb, peerRec), (pc, peerRec)]
    mesh := [(ta, [pb])]
    fanout := []
    mcache := Cache.MessageIndex.empty params.window
    seen := Cache.SeenIndex.empty params.seen
    backoff := []
    iwant := []
    topics := [ta]
    now := 0
    lastHeartbeat := 0 }

private def msgOf (topic : TopicId) (payload : List Nat) : Message :=
  { «from» := none, data := some payload, seqno := none, topic := topic,
    signature := none, key := none }

private def rpcOf (r : Rpc.RPC) : List Nat := Pb.encodeMessage r

private def emptyRpc : Rpc.RPC := { subscriptions := [], publish := [], control := none }

/-- `pa` requests partial messages on `t`, and `pc` only supports them. -/
private def subsRpc (requests supports : Bool) : Rpc.RPC :=
  { emptyRpc with subscriptions :=
      [{ subscribe := true, topicid := "t", requestsPartial := requests,
         supportsSendingPartial := supports }] }

private def topicBytes (t : TopicId) : List Nat := Bytes.toNatList (Bytes.ofString t.name)

private def partialOn (t : TopicId) (data : Option (List Nat)) : Rpc.PartialMessage :=
  { topicId := some (topicBytes t), groupId := some [0, 7], partialMessage := data,
    partsMetadata := some [1, 1, 0] }

private def stateOf : Except ProtocolError (State × List Action) → State
  | .ok (s, _) => s
  | .error _ => start

private def actionsOf : Except ProtocolError (State × List Action) → List Action
  | .ok (_, a) => a
  | .error _ => []

/-- The RPCs an action list sends to `q`. -/
private def sentTo (q : Peer) (l : List Action) : List Rpc.RPC :=
  l.filterMap fun a => match a with
    | .sendRpc q' r => if q' == q then some r else none
    | _ => none

private def penalty (s : State) (q : Peer) : Nat :=
  ((peerOf s q).map (·.score.behaviourPenalty)).getD 0

private def counters (s : State) (q : Peer) : Score.TopicCounters :=
  ((peerOf s q).map (Score.countersOf ·.score ta)).getD Score.TopicCounters.zero

private def hasIhave (r : Rpc.RPC) : Bool :=
  match r.control with
  | some c => !c.ihave.isEmpty
  | none => false

/-- The bytes decode to `want` with nothing left. -/
private def decodesTo {α : Type} [Pb.ProtoMessage α] [BEq α] (bs : List Nat) (want : α) : Bool :=
  match Pb.decodeMessage? (α := α) bs with
  | .ok (v, rest) => v == want && rest.isEmpty
  | .error _ => false

/-- Run the events in order from `s`. -/
private def runAll (s : State) (es : List Event) : State × List Action :=
  match run params s es with
  | .ok r => r
  | .error _ => (s, [])

/-! ## Checks -/

def run (r : Runner) : IO Unit := do
  r.section "gossipsub v1.3 partial messages"
    "vendor/specs/pubsub/gossipsub/gossipsub-v1.3.md, partial-messages.md, extensions/extensions.proto"

  -- The wire: a v1.1 subscription keeps its bytes, and each flag adds
  -- its field only when true.
  let plain : Rpc.SubOpts := { subscribe := true, topicid := "t" }
  r.check "wire: a subscription without flags is fields 1 and 2 only"
    (Pb.encodeMessage plain == [0x08, 0x01, 0x12, 0x01, 0x74])
  let flagged : Rpc.SubOpts := { plain with requestsPartial := true, supportsSendingPartial := true }
  r.check "wire: the flags are fields 3 and 4, varint 1"
    (Pb.encodeMessage flagged == [0x08, 0x01, 0x12, 0x01, 0x74, 0x18, 0x01, 0x20, 0x01])
  r.check "wire: the flagged subscription round trips"
    (decodesTo (Pb.encodeMessage flagged) flagged)
  -- ControlExtensions { partialMessages = 10 }: tag 10 << 3 = 80, two
  -- varint bytes 0x50 0x01, then the value 1.
  let ext : Rpc.ControlExtensions := { partialMessages := true }
  r.check "wire: the partialMessages extension is field 10"
    (Pb.encodeMessage ext == [0x50, 0x01])
  -- testExtension = 6492434 is an experimental field: a decoder drops it.
  -- Its tag is 6492434 << 3 = 0x3188890, the four-byte varint
  -- 90 91 c6 01.
  r.check "wire: an unknown extension decodes to no extension"
    (decodesTo [0x90, 0x91, 0xc6, 0x01, 0x01] ({} : Rpc.ControlExtensions))
  let ctl : Rpc.ControlMessage := { ihave := [], iwant := [], graft := [], prune := [], extensions := some ext }
  r.check "wire: the extensions are control field 6"
    (Pb.encodeMessage ctl == [0x32, 0x02, 0x50, 0x01])
  let prpc : Rpc.RPC := { emptyRpc with partialRpc := some (partialOn ta (some [9, 9])) }
  r.check "wire: the partial RPC round trips"
    (decodesTo (rpcOf prpc) prpc)
  r.check "wire: the partial RPC is RPC field 10"
    ((rpcOf prpc).head? == some 0x52)
  -- Field-number order, as go and rust write it: control (3) first.
  let both : Rpc.RPC := { prpc with control := some ctl }
  let bothBytes := rpcOf both
  r.check "wire: control (field 3) comes before partial (field 10)"
    -- Tag 0x1a, length 4, the four control bytes, then tag 0x52.
    (bothBytes.head? == some 0x1a && (bothBytes.drop 6).head? == some 0x52)
  r.check "wire: an RPC with control and partial round trips"
    (decodesTo bothBytes both)

  -- The SubOpts behavior table: the core records each peer's choice.
  let s1 := stateOf (step params start (.rpc pa (rpcOf (subsRpc true false))))
  let s1 := stateOf (step params s1 (.rpc pc (rpcOf (subsRpc false true))))
  r.check "core: a request implies support"
    (peerPartial s1 pa ta == { requests := true, supports := true })
  r.check "core: the core records support alone"
    (peerPartial s1 pc ta == { requests := false, supports := true })
  let unsub : Rpc.RPC := { emptyRpc with subscriptions :=
    [{ subscribe := false, topicid := "t", requestsPartial := true }] }
  r.check "core: an unsubscribe drops the choice, and the core ignores its flags"
    (peerPartial (stateOf (step params s1 (.rpc pc (rpcOf unsub)))) pc ta == {})

  -- A full message goes to the mesh, and to no peer that takes partial
  -- messages. `pa` joins the mesh, so the forward would reach it.
  let s2 := { s1 with mesh := [(ta, [pa, pb, pc])] }
  let fwd := actionsOf (step params s2 (.rpc pb (rpcOf { emptyRpc with publish := [msgOf ta [5]] })))
  r.check "core: no full message to a peer that requested partial messages"
    ((sentTo pa fwd).all (·.publish.isEmpty))
  r.check "core: a peer that only supports them gets the full message"
    ((sentTo pc fwd).any (!·.publish.isEmpty))
  let own := actionsOf (step params s2 (.publish (msgOf ta [6])))
  r.check "core: a local publish skips the requesting peer too"
    ((sentTo pa own).isEmpty && !(sentTo pc own).isEmpty)

  -- The application interface: the data goes only to a requester, the
  -- metadata to any peer that supports partial messages.
  let pm := partialOn ta (some [9, 9])
  let toA := sentTo pa (actionsOf (step params s1 (.sendPartial pa pm)))
  r.check "core: a requester gets the data and the metadata"
    (toA.map (·.partialRpc) == [some pm])
  let toC := sentTo pc (actionsOf (step params s1 (.sendPartial pc pm)))
  r.check "core: a supporter gets the metadata without the data"
    (toC.map (·.partialRpc) == [some { pm with partialMessage := none }])
  r.check "core: a peer with no choice gets nothing"
    ((actionsOf (step params s1 (.sendPartial pb pm))).isEmpty)
  r.check "core: a topic we cannot send on sends nothing"
    ((actionsOf (step params s1 (.sendPartial pa (partialOn tb (some [1]))))).isEmpty)

  -- Inbound: a partial message reaches the application, mesh peer or
  -- not. Data on a topic where we did not request it costs P₇.
  let (sIn, aIn) := match step params s1 (.rpc pc (rpcOf prpc)) with
    | .ok r => r
    | .error _ => (s1, [])
  r.check "core: an inbound partial message goes to the application"
    (aIn == [.partialIn pc (partialOn ta (some [9, 9]))])
  r.check "core: a valid partial message costs nothing" (penalty sIn pc == 0)
  let wrong : Rpc.RPC := { emptyRpc with partialRpc := some (partialOn tb (some [1])) }
  let (sBad, aBad) := match step params s1 (.rpc pc (rpcOf wrong)) with
    | .ok r => r
    | .error _ => (s1, [])
  r.check "core: the core drops unrequested data" aBad.isEmpty
  r.check "core: unrequested data costs one P₇ penalty" (penalty sBad pc == 1)

  -- The Extensions message belongs in the first RPC, once.
  let extRpc : Rpc.RPC := { emptyRpc with control := some ctl }
  let e1 := stateOf (step params start (.rpc pb (rpcOf extRpc)))
  r.check "core: the core records the first RPC's extensions"
    (((peerOf e1 pb).bind (·.extensions)) == some ext && penalty e1 pb == 0)
  let e2 := stateOf (step params e1 (.rpc pb (rpcOf extRpc)))
  r.check "core: a second Extensions message costs a P₇ penalty" (penalty e2 pb == 1)
  let late := stateOf (step params (stateOf (step params start (.rpc pb (rpcOf emptyRpc))))
    (.rpc pb (rpcOf extRpc)))
  r.check "core: extensions after the first RPC cost a P₇ penalty" (penalty late pb == 1)

  -- Gossip: no IHAVE to a peer that requested partial messages.
  let (_, acts) := runAll s1 [.publish (msgOf ta [7]), .tick params.heartbeatInterval [pa, pb, pc]]
  r.check "core: gossip skips the requesting peer"
    ((sentTo pa acts).all (!hasIhave ·))
  r.check "core: gossip reaches the other non-mesh peer"
    ((sentTo pc acts).any hasIhave)
  -- In place of the IHAVE, the core names the requesting gossip target
  -- to the application. It names no other target.
  let offers := acts.filterMap fun a => match a with
    | .partialGossip t ps => some (t, ps)
    | _ => none
  r.check "core: the heartbeat offers partial messages to the requester"
    (offers == [(ta, [pa])])
  -- Partial messages never enter the message cache. So the core makes
  -- the offer also when the cache holds no message.
  let (_, quiet) := runAll s1 [.tick params.heartbeatInterval [pa, pb, pc]]
  r.check "core: the core makes the offer with an empty message cache"
    (quiet.any (· == .partialGossip ta [pa]) && quiet.all fun a => match a with
      | .sendRpc _ r => !hasIhave r
      | _ => true)
  -- A topic where we cannot send partial messages makes no offer.
  let fullOnly : Params := { params with partialTopics := [] }
  let offFull := match Core.run fullOnly s1 [.tick params.heartbeatInterval [pa, pb, pc]] with
    | .ok (_, a) => a
    | .error _ => []
  r.check "core: a full-message topic makes no offer"
    (offFull.all fun a => match a with
      | .partialGossip _ _ => false
      | _ => true)

  -- The scoring hooks of the Fulu partial columns.
  let j1 := stateOf (step params s1 (.partialJudged pa ta true))
  r.check "core: novel valid parts count as a first delivery"
    ((counters j1 pa).firstMessageDeliveries == 1)
  let j2 := stateOf (step params s1 (.partialJudged pa ta false))
  r.check "core: bad parts count as an invalid delivery"
    ((counters j2 pa).invalidMessageDeliveries == 1)

  -- Our own announcements carry our choice.
  r.check "core: our subscription to t requests partial messages"
    (subOpts params ta true == { subscribe := true, topicid := "t", requestsPartial := true,
                                 supportsSendingPartial := true })
  r.check "core: our unsubscribe carries no flags"
    (subOpts params ta false == { subscribe := false, topicid := "t" })
  r.check "core: a node with a partial topic announces the extension"
    (ownExtensions params == some ext && ownExtensions defaults == none)

end Tests.Gossipsub.Partial
