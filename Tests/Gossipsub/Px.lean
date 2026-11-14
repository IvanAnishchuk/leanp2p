import Tests.Support
import Tests.Gossipsub.Identity
import Libp2p.Protocols.Gossipsub.Core

/-!
# Gossipsub suite: peer exchange and floodsub peers

The core half of the two features; `scripts/pubsub-interop.sh` runs the
node half against go-libp2p-pubsub.

Peer exchange follows `gossipsub-v1.1.md`, "PRUNE Backoff and Peer
Exchange", and go-libp2p-pubsub's `makePrune` and `handlePrune`:

* a GRAFT into a full mesh is pruned with the other peers of the topic,
  when `doPX` is on, and with none when it is off;
* the prune names no peer to a target below score 0, and no peer below
  score 0;
* an unsubscribe prunes with the peer exchange too;
* a received prune's peers become one `pxConnect` when the sender's
  score is not below `acceptPXThreshold`, the topic is ours, and the
  peer is new; `prunePeers` caps them.

Floodsub peers follow go-libp2p-pubsub's `rpcs`: they get our messages
and our forwards, never a GRAFT or an IHAVE, and a `protocol` event
takes a peer out of the mesh.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Px

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Core

private def ta : TopicId := ⟨"t"⟩
private def tb : TopicId := ⟨"u"⟩

private def pa : Peer := Identity.peer 1
private def pb : Peer := Identity.peer 2
private def pc : Peer := Identity.peer 3
private def pd : Peer := Identity.peer 4
private def pe : Peer := Identity.peer 5

private def prims : Sign.Prims :=
  { unmarshalKey := fun _ => none
    inlineKey := fun _ => none
    idOfKey := fun _ => []
    verify := fun _ _ _ => false }

/-- A mesh bound of two, the peer exchange on, and the app score
counted, so a test can lift one peer above `acceptPXThreshold`. -/
private def params : Params :=
  { defaults with
    mesh := { d := 2, dLow := 1, dHigh := 2, dScore := 1, dLazy := 6 }
    dOut := 0
    prims := prims
    msgId := fun m => ⟨m.data.getD []⟩
    score := { defaults.score with global := { defaults.score.global with appSpecificWeight := 1 } }
    doPX := true }

private def rec (proto : PubsubProto := .meshsub) : PeerData :=
  { score := Score.PeerState.zero, proto, subs := [ta] }

/-- Four meshsub peers on `t`; the mesh holds `pa` and `pb`, full at
`dHigh`. -/
private def start : State :=
  { peers := [(pa, rec), (pb, rec), (pc, rec), (pd, rec)]
    mesh := [(ta, [pa, pb])]
    fanout := []
    mcache := Cache.MessageIndex.empty params.window
    seen := Cache.SeenIndex.empty params.seen
    backoff := []
    iwant := []
    topics := [ta]
    now := 0
    lastHeartbeat := 0 }

private def emptyRpc : Rpc.RPC := { subscriptions := [], publish := [], control := none }

private def ctl (c : Rpc.ControlMessage) : Rpc.RPC := { emptyRpc with control := some c }

private def graftOf (t : TopicId) : Rpc.RPC :=
  ctl { ihave := [], iwant := [], graft := [{ topicId := t.name }], prune := [] }

private def idOf (q : Peer) : List Nat := Bytes.toNatList q.toBytes

private def infoOf (q : Peer) : Rpc.PeerInfo := { peerId := some (idOf q), signedPeerRecord := none }

private def pruneOf (t : TopicId) (px : List Rpc.PeerInfo) : Rpc.RPC :=
  ctl { ihave := [], iwant := [], graft := [],
        prune := [{ topicId := t.name, peers := px, backoff := some 60 }] }

private def stepOf (p : Params) (s : State) (e : Event) : State × List Action :=
  match step p s e with
  | .ok r => r
  | .error _ => (s, [])

/-- The peer-exchange entries of every prune an action list sends to `q`. -/
private def pxTo (q : Peer) (l : List Action) : List Rpc.PeerInfo :=
  l.flatMap fun a => match a with
    | .sendRpc q' r => if q' == q then
        (r.control.map (·.prune.flatMap (·.peers))).getD [] else []
    | _ => []

private def prunesTo (q : Peer) (l : List Action) : Nat :=
  (l.filter fun a => match a with
    | .sendRpc q' r => q' == q && (r.control.map (!·.prune.isEmpty)).getD false
    | _ => false).length

private def connects (l : List Action) : List (Peer × List Rpc.PeerInfo) :=
  l.filterMap fun a => match a with
    | .pxConnect s infos => some (s, infos)
    | _ => none

private def sentTo (q : Peer) (l : List Action) : List Rpc.RPC :=
  l.filterMap fun a => match a with
    | .sendRpc q' r => if q' == q then some r else none
    | _ => none

private def msgOf (payload : List Nat) : Message :=
  { «from» := none, data := some payload, seqno := none, topic := ta,
    signature := none, key := none }

private def withScore (s : State) (q : Peer) (app : Int) : State :=
  updateScoreOf s q fun sc => { sc with appScore := app }

def run (r : Runner) : IO Unit := do
  r.section "Gossipsub peer exchange and floodsub" "gossipsub-v1.1.md, go-libp2p-pubsub gossipsub.go"

  /- ## Sending -/
  -- `pc` grafts into the full mesh: the prune names `pa`, `pb`, `pd`.
  let (_, acts) := stepOf params start (.rpc pc (Pb.encodeMessage (graftOf ta)))
  r.check "px.send.graft-full.prune" (prunesTo pc acts == 1)
  r.check "px.send.graft-full.peers"
    ((pxTo pc acts).map (·.peerId) == [pa, pb, pd].map (some ∘ idOf))
  r.check "px.send.no-record" ((pxTo pc acts).all (·.signedPeerRecord.isNone))
  -- With `doPX` off, the same prune names nobody.
  let (_, actsOff) := stepOf { params with doPX := false } start (.rpc pc (Pb.encodeMessage (graftOf ta)))
  r.check "px.send.off" (prunesTo pc actsOff == 1 && (pxTo pc actsOff).isEmpty)
  -- `prunePeers` caps the list.
  let (_, actsCap) := stepOf { params with prunePeers := 1 } start
    (.rpc pc (Pb.encodeMessage (graftOf ta)))
  r.check "px.send.cap" ((pxTo pc actsCap).length == 1)
  -- A peer below score 0 is not offered, and a target below 0 gets none.
  let negD := withScore start pd (-5)
  let (_, actsNeg) := stepOf params negD (.rpc pc (Pb.encodeMessage (graftOf ta)))
  r.check "px.send.skips-negative"
    ((pxTo pc actsNeg).map (·.peerId) == [pa, pb].map (some ∘ idOf))
  r.check "px.send.negative-target" (pxPeers params (withScore start pc (-1)) pc ta == [])
  -- An unsubscribe prunes the mesh with the peer exchange.
  let (_, actsU) := stepOf params start (.unsubscribe ta)
  r.check "px.send.unsubscribe"
    ((pxTo pa actsU).map (·.peerId) == [pb, pc, pd].map (some ∘ idOf))

  /- ## Accepting -/
  let px := [infoOf pe, infoOf pc]
  -- A score at the threshold 0 is accepted ("below this threshold is
  -- ignored"); `pc` is known, so only `pe` remains.
  let (_, a0) := stepOf params start (.rpc pa (Pb.encodeMessage (pruneOf ta px)))
  r.check "px.accept.at-threshold" (connects a0 == [(pa, [infoOf pe])])
  -- A score below it is ignored.
  let (_, aLow) := stepOf params (withScore start pa (-1)) (.rpc pa (Pb.encodeMessage (pruneOf ta px)))
  r.check "px.accept.below-threshold" (connects aLow).isEmpty
  let lifted := withScore start pa 1
  let (_, a1) := stepOf params lifted (.rpc pa (Pb.encodeMessage (pruneOf ta px)))
  r.check "px.accept.connect" (connects a1 == [(pa, [infoOf pe])])
  -- A prune of a topic we did not join brings nothing.
  let (_, a2) := stepOf params lifted (.rpc pa (Pb.encodeMessage (pruneOf tb px)))
  r.check "px.accept.unknown-topic" (connects a2).isEmpty
  -- An entry whose peer id does not decode is dropped.
  let (_, a3) := stepOf params lifted
    (.rpc pa (Pb.encodeMessage (pruneOf ta [{ peerId := some [1, 2, 3], signedPeerRecord := none }])))
  r.check "px.accept.bad-id" (connects a3).isEmpty
  -- `prunePeers` caps what we take.
  let many := (List.range 5).map fun i => infoOf (Identity.peer (10 + i))
  let (_, a4) := stepOf { params with prunePeers := 2 } lifted
    (.rpc pa (Pb.encodeMessage (pruneOf ta many)))
  r.check "px.accept.cap" ((connects a4).map (·.2.length) == [2])
  -- The prune still leaves the mesh.
  let (s5, _) := stepOf params lifted (.rpc pa (Pb.encodeMessage (pruneOf ta px)))
  r.check "px.accept.prunes-mesh" (!memB pa (meshOf s5 ta))

  /- ## Floodsub peers -/
  let flood : State := { start with peers := start.peers ++ [(pe, rec .floodsub)] }
  -- Our publish reaches the mesh and the floodsub peer.
  let (_, ap) := stepOf params flood (.publish (msgOf [7]))
  r.check "flood.publish" (!(sentTo pe ap).isEmpty && !(sentTo pa ap).isEmpty)
  -- A forward from `pa` reaches the floodsub peer, never back to `pa`.
  let pubRpc : Rpc.RPC := { emptyRpc with publish := [msgOf [8]] }
  let (_, af) := stepOf params flood (.rpc pa (Pb.encodeMessage pubRpc))
  r.check "flood.forward" (!(sentTo pe af).isEmpty && (sentTo pa af).isEmpty)
  -- A heartbeat that must fill the mesh never grafts the floodsub peer.
  let thin : State := { flood with mesh := [(ta, [])] }
  let (st, aTick) := stepOf params thin (.tick 1000 [pe, pc, pd])
  r.check "flood.never-meshed" (!memB pe (meshOf st ta) && (sentTo pe aTick).isEmpty)
  -- A `protocol` event takes a mesh peer out of the mesh.
  let (sp, _) := stepOf params start (.protocol pa .floodsub)
  r.check "flood.protocol-leaves-mesh" (!memB pa (meshOf sp ta) && isFlood sp pa)
  -- The prune names no floodsub peer.
  let (_, ax) := stepOf params flood (.rpc pc (Pb.encodeMessage (graftOf ta)))
  r.check "flood.not-exchanged" (!((pxTo pc ax).map (·.peerId)).contains (some (idOf pe)))

end Tests.Gossipsub.Px
