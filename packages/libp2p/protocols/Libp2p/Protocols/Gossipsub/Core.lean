import Libp2p.Protocols.Gossipsub.Types
import Libp2p.Protocols.Gossipsub.Rpc
import Libp2p.Protocols.Gossipsub.Score
import Libp2p.Protocols.Gossipsub.Cache
import Libp2p.Protocols.Gossipsub.Sign

/-!
# Gossipsub router core

The pure state machine of the gossipsub router, v1.1 with the v1.2
IDONTWANT and the v1.3 partial-messages extension: the state, the
external events, the outgoing actions, the one error constructor, and
the total `step`. Time and the peer order enter as event data, so the
core reads no clock and makes no random choice. `run` drives a list of
events.

The core owns the mesh, the fanout, the score accounting, and the
heartbeat. It calls the public surface of the score, the cache, and the
sign parts. It decodes an inbound RPC at its own boundary and maps a
decode failure to the one error constructor.

An inbound message that passes validation and is not already seen is
delivered to the application and forwarded to every other peer of
`mesh[topic]`. The sender already holds it, so the forward list drops
the sender. A local publish records the message id in the seen cache,
so a later echo of the same id is not forwarded again.

The heartbeat emits gossip after it settles the mesh and before it
shifts the message cache. The recipients are peers of the supplied order
at or above the gossip threshold that are in neither the mesh nor the
fanout of the topic. Their count is adaptive: at least `dLazy`, and
`gossipFactor` percent of the candidates when that is more. A recipient
that requested partial messages on the topic gets no IHAVE. In its
place, one `Action.partialGossip` names all such recipients to the
application. The application then offers them its partial messages.

Floodsub peers (`PubsubProto.floodsub`) are a separate forward set
(`floodTargets`): they join no mesh, take no gossip, and get every
message of their topics, as go-libp2p-pubsub's `rpcs` treats a peer
without the mesh feature. Peer exchange runs in both directions:
- With `doPX` set, three prunes name other peers (`pxPeers`): the prune
  of an oversubscribed mesh, the prune of a GRAFT into a full mesh, and
  the prune of an unsubscribe.
- The peers of a received prune become `Action.pxConnect` when the
  sender's score is at or above `acceptPXThreshold` (`pxAccept`).

Gaps that remain:

- `validationOk` uses `strictNoSign`, with no per-topic policy.
  `defaults.msgId` is the payload. That policy leaves `from` and
  `seqno` absent, so the spec's default id would be empty for every
  accepted message.
- A graft for a topic the router does not subscribe to is ignored. The
  v1.0 spec answers with a prune, and the v1.1 spam measures say to
  ignore it. This step follows v1.1.
- The partial-messages choices are fixed parameters
  (`Params.partialTopics`), so a node never changes its `SubOpts` flags
  on a topic it already announced.

The spec sections, under `vendor/specs/pubsub/gossipsub/`:
- `gossipsub-v1.0.md`: the router, the message cache, the mesh, the
  fanout, the heartbeat
- `gossipsub-v1.1.md`: the score gates, the backoff, the spam measures
- `gossipsub-v1.2.md`: IDONTWANT
- `gossipsub-v1.3.md` with `partial-messages.md`: the extensions

The root `docs/ARCHITECTURE.md` section 3.3 fixes the shape: one total
`step` that returns `Except ProtocolError (State × List Action)`, with
time as an input.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Core

open Libp2p.Protocols.Gossipsub

/-! ## Types -/

/-- The pubsub protocol a peer negotiated. -/
inductive PubsubProto where
  /-- The gossipsub mesh protocol. -/
  | meshsub
  /-- The floodsub protocol. -/
  | floodsub
  deriving DecidableEq, BEq, Repr

/-- A partial-messages choice for one topic (`partial-messages.md`,
"Changes to `SubOpts`"): `requests` asks for partial messages, and
`supports` can send them. A request implies support. -/
structure PartialOpts where
  /-- Partial messages are wanted on the topic. -/
  requests : Bool := false
  /-- Partial messages can be sent on the topic. -/
  supports : Bool := false
  deriving DecidableEq, BEq, Repr

/-- The choice can send partial messages: a request implies support. -/
def PartialOpts.sends (o : PartialOpts) : Bool := o.requests || o.supports

/-- The per-peer record: the score state, the pubsub protocol, and the
topics the peer announced. `Peer` keeps its one meaning, the peer id of
`Types.lean`. -/
structure PeerData where
  /-- The score state of the peer. -/
  score : Score.PeerState
  /-- The pubsub protocol of the peer. -/
  proto : PubsubProto
  /-- The announced topics. -/
  subs : List TopicId
  /-- We dialed the peer: the `D_out` quota counts it
  (`gossipsub-v1.1.md`, lines 186 to 203). -/
  outbound : Bool := false
  /-- The peer's IP address bytes, for P₆'s colocation count. -/
  ip : Option (List Nat) := none
  /-- The partial-messages choice the peer announced, per topic. -/
  partialSubs : List (TopicId × PartialOpts) := []
  /-- An RPC from the peer arrived: an Extensions message after this
  breaks the first-message rule (`gossipsub-v1.3.md`). -/
  rpcSeen : Bool := false
  /-- The peer's Extensions message, from its first RPC. -/
  extensions : Option Rpc.ControlExtensions := none

/-- The mesh degree parameters: `d`, `dLow`, `dHigh`, `dScore`, `dLazy`. -/
structure MeshParams where
  /-- The target mesh degree. -/
  d : Nat
  /-- The low mesh water mark. -/
  dLow : Nat
  /-- The high mesh water mark. -/
  dHigh : Nat
  /-- The number of score-best peers the mesh keeps. -/
  dScore : Nat
  /-- The number of peers that receive gossip. -/
  dLazy : Nat
  deriving DecidableEq, Repr

/-- The router parameters. -/
structure Params where
  /-- The score parameters. -/
  score : Score.Params
  /-- The score thresholds. -/
  thresholds : Thresholds
  /-- The mesh degree parameters. -/
  mesh : MeshParams
  /-- The heartbeat interval in milliseconds. -/
  heartbeatInterval : Millis
  /-- The fanout time to live in milliseconds. -/
  fanoutTtl : Millis
  /-- The prune backoff period in milliseconds. -/
  pruneBackoff : Millis
  /-- The gossip factor in percent. -/
  gossipFactor : Nat
  /-- The IWANT answer deadline in milliseconds. -/
  iwantDeadline : Millis
  /-- The message cache window parameters. -/
  window : Cache.WindowParams
  /-- The seen cache parameters. -/
  seen : Cache.SeenParams
  /-- The signature primitives. -/
  prims : Sign.Prims
  /-- The message id function. -/
  msgId : Sign.MsgIdFn
  /-- Hold each accepted message until the application answers it
  (`gossipsub-v1.1.md`, "Extended Validators"). When set, the core emits
  `Action.validate` in place of the delivery and the forward, keeps the
  message out of the message cache, and acts on `Event.validated`.
  rust-libp2p calls this `validate_messages`, and Lighthouse sets it. -/
  validateMessages : Bool := false
  /-- The cap on one message's `data`, as it travels. `none` sets no cap.
  A consensus node sets `max_compressed_len(MAX_PAYLOAD_SIZE)` (phase0
  "Maximum message sizes": "Clients MUST reject ... messages whose size
  exceed the following limits"). The uncompressed bound needs the
  snappy header, which the client's decoder reads. -/
  maxDataSize : Option Nat := none
  /-- Send IDONTWANT (gossipsub v1.2) for a held message whose `data` has
  at least this many bytes. `none` sends no IDONTWANT. The spec leaves
  the policy open ("choose a message size threshold"), and Lighthouse
  sets `idontwant_message_size_threshold`. Only `validateMessages`
  sends. -/
  idontwantThreshold : Option Nat := none
  /-- The most IDONTWANT pairs the router keeps. The oldest go first. The
  spec leaves the prune strategy to the implementation. -/
  dontSendCap : Nat := 4096
  /-- The spam measures (`gossipsub-v1.1.md`, lines 621 to 644):
  - `maxIhaveMessages`: the most IHAVE messages one peer may send per
    heartbeat (rust-libp2p's `max_ihave_messages_heartbeat`, 10)
  - `maxIhaveLength`: the most ids we ask one peer for per heartbeat
    (rust's control cap, 5000)
  - `gossipRetransmission`: the most times we answer one peer's IWANT
    for one id (rust's `gossip_retransimission`, 3) -/
  maxIhaveMessages : Nat := 10
  maxIhaveLength : Nat := 5000
  gossipRetransmission : Nat := 3
  /-- The caps on a peer's subscriptions, as rust-libp2p's
  `MaxCountSubscriptionFilter` sets them (`subscription_filter.rs`):
  - `maxSubscriptionsPerRpc`: the most subscription options in one RPC
  - `maxSubscribedTopics`: the most topics one peer may announce

  An RPC past either cap has its subscriptions ignored, and the rest of
  the RPC stands (`admitSubs`). `none` sets no cap, as go and rust do by
  default. The table of a peer's topics is a list, so an RPC of `n`
  options costs `n` times the peer's topic count: a node that faces
  public peers sets `maxSubscriptionsPerRpc`. -/
  maxSubscriptionsPerRpc : Option Nat := none
  maxSubscribedTopics : Option Nat := none
  /-- How long a departed peer's score stays (`gossipsub-v1.1.md`, lines
  212 to 214: "the score is retained for some period of time when a peer
  disconnects"). rust's default is 1 h, and Lighthouse sets 100 epochs. -/
  retainScore : Millis := 3600000
  /-- "A shorter backoff period can be used in case of an unsubscribe
  event" (`gossipsub-v1.1.md`, lines 108 to 110). go and rust use 10 s. -/
  unsubscribeBackoff : Millis := 10000
  /-- Flood publishing (`gossipsub-v1.1.md`, lines 145 to 163): our own
  messages go to every subscribed peer at or above `publishThreshold`.
  go and rust enable it by default. Lighthouse disables it
  (`config.rs:519`), so the default here is off. -/
  floodPublish : Bool := false
  /-- `D_out`: the outbound peers a mesh keeps (`gossipsub-v1.1.md`,
  lines 186 to 203). rust's `mesh_outbound_min` is 2. It must stay below
  `D_lo` and at most `D/2`. -/
  dOut : Nat := 2
  /-- Opportunistic grafting (`gossipsub-v1.1.md`, lines 260 to 279): at
  each of its heartbeats, a mesh whose median score is below
  `opportunisticGraftThreshold` grafts up to this many peers that score
  above the median. rust grafts 2 every 60 heartbeats. -/
  opportunisticGraftPeers : Nat := 2
  /-- Our partial-messages choice per topic (gossipsub v1.3,
  `partial-messages.md`). A topic not listed takes full messages only.
  Any entry that can send makes the node announce the extension. -/
  partialTopics : List (TopicId × PartialOpts) := []
  /-- Peer exchange on prune (`gossipsub-v1.1.md`, "Peer Exchange"): a
  prune we send names up to `prunePeers` other peers of the topic. go and
  rust disable it by default, and so does this router. Teku enables it.
  The acceptance side always runs, behind the gate of
  `acceptPXThreshold`. -/
  doPX : Bool := false
  /-- The most peers one prune names, and the most peers we take from one
  received prune. go's `PrunePeers` and rust's `prune_peers` are 16. -/
  prunePeers : Nat := 16

/-- The parameter bound the mesh theorems consume: the target degree is
at most the high water mark. -/
structure Params.Valid (p : Params) : Prop where
  /-- The target degree is at most the high water mark. -/
  d_le_dHigh : p.mesh.d ≤ p.mesh.dHigh

/-- One fanout record: the peers and the last publish time. -/
structure Fanout where
  /-- The fanout peers. -/
  peers : List Peer
  /-- The last publish time. -/
  lastPublished : Millis
  deriving Repr

/-- The router state. -/
structure State where
  /-- The known peers and their records. -/
  peers : List (Peer × PeerData)
  /-- The mesh of each topic. -/
  mesh : List (TopicId × List Peer)
  /-- The fanout of each topic. -/
  fanout : List (TopicId × Fanout)
  /-- The message cache. -/
  mcache : Cache.MessageIndex
  /-- The seen cache. -/
  seen : Cache.SeenIndex
  /-- The backoff table. -/
  backoff : Cache.BackoffTable
  /-- The IWANT promises. -/
  iwant : Cache.PromiseTable
  /-- The topics the router subscribes to. -/
  topics : List TopicId
  /-- The current time. -/
  now : Millis
  /-- The time of the last heartbeat. -/
  lastHeartbeat : Millis
  /-- The time of the last score decay. The scores decay at the first
  heartbeat one `decayInterval` after it ("The decay interval",
  `gossipsub-v1.1.md`), so the interval may span many heartbeats. -/
  lastDecay : Millis := 0
  /-- The messages that wait for the application's answer, with their
  ids and the peers that sent them (`Params.validateMessages`). -/
  pending : List (MessageId × Peer × Message) := []
  /-- The receipt time of each held message (`expirePending`). -/
  pendingAt : List (MessageId × Millis) := []
  /-- The IDONTWANT pairs (gossipsub v1.2): a forward of the id skips
  the peer. Newest first. -/
  dontSend : List (Peer × MessageId) := []
  /-- The explicit peers (`gossipsub-v1.1.md`, "Explicit Peering
  Agreements"): outside every mesh, and sent every valid message. -/
  explicit : List Peer := []
  /-- The delivery record of each recent id: the time of its first
  arrival and every peer that sent it. P₃'s near-first deliveries and
  P₄ for every sender of a rejected message read it, as go-libp2p's
  `deliveries` table does. -/
  deliveries : Std.HashMap MessageId (Millis × List Peer) := {}
  /-- Per peer this heartbeat: the IHAVE messages it sent and the ids we
  asked it for. `maintain` clears it. -/
  ihaveSeen : Std.HashMap Peer (Nat × Nat) := {}
  /-- How many times we answered each peer's IWANT for each id. -/
  served : Std.HashMap (Peer × MessageId) Nat := {}
  /-- The records of departed peers and when each expires (`retainScore`). -/
  retained : List (Peer × PeerData × Millis) := []

/-- The application's answer on one held message
(`gossipsub-v1.1.md`, "Extended Validators"). -/
inductive Validation where
  /-- Deliver and forward. -/
  | accept
  /-- Drop, and count an invalid delivery against the sender (P₄). -/
  | reject
  /-- Drop, with no penalty. -/
  | ignore
  deriving DecidableEq, BEq, Repr

/-- The external events. -/
inductive Event where
  /-- A peer joined with a protocol. -/
  | peerJoined (peer : Peer) (proto : PubsubProto)
  /-- A peer left. -/
  | peerLeft (peer : Peer)
  /-- An RPC arrived from a peer, as bytes. -/
  | rpc (sender : Peer) (bytes : List Nat)
  /-- The application publishes a message. -/
  | publish (msg : Message)
  /-- The application subscribes to a topic. -/
  | subscribe (topic : TopicId)
  /-- The application unsubscribes from a topic. -/
  | unsubscribe (topic : TopicId)
  /-- The heartbeat fires at `now` with a peer order. -/
  | tick (now : Millis) (order : List Peer)
  /-- The application answers the held message `id` from `source`. -/
  | validated (id : MessageId) (source : Peer) (outcome : Validation)
  /-- What the host knows of a connected peer: whether we dialed it, and
  its IP address bytes. -/
  | peerInfo (peer : Peer) (outbound : Bool) (ip : Option (List Nat))
  /-- The application's score of a peer: P₅ (`gossipsub-v1.1.md`, "P₅"). -/
  | appScore (peer : Peer) (score : Int)
  /-- The application sends a partial message to a peer
  (`partial-messages.md`, "Application-Library Interface"). The core
  drops the data for a peer that did not request it, and drops the whole
  message for a peer that cannot send partial messages. -/
  | sendPartial (peer : Peer) (msg : Rpc.PartialMessage)
  /-- The application judged the parts a peer sent on a topic: novel
  valid data counts as a first delivery, bad data as an invalid one
  (Fulu `partial-columns/p2p-interface.md`, the scoring hooks). -/
  | partialJudged (peer : Peer) (topic : TopicId) (valid : Bool)
  /-- The pubsub protocol a known peer negotiated. The host announces a
  connection before any stream negotiates, so a join records `meshsub`,
  and this event corrects it. A peer that speaks floodsub leaves every
  mesh and fanout. -/
  | protocol (peer : Peer) (proto : PubsubProto)
  deriving Repr

/-- The outgoing actions. -/
inductive Action where
  /-- Send an RPC to a peer. -/
  | sendRpc (to : Peer) (rpc : Rpc.RPC)
  /-- Deliver a message to the application. -/
  | deliver (msg : Message)
  /-- Hand a held message to the application for its answer, with its
  id and its propagation source (`Params.validateMessages`). -/
  | validate (msg : Message) (id : MessageId) (source : Peer)
  /-- Hand a partial message from a peer to the application, mesh peer
  or not (`partial-messages.md`, "Application-Library Interface"). -/
  | partialIn (source : Peer) (msg : Rpc.PartialMessage)
  /-- Offer partial messages on a topic to the gossip targets of the
  heartbeat that requested them. The offer takes the place of an IHAVE
  (`partial-messages.md`, "Partial Message Gossip"). Only the application
  knows its groups, so it answers through `sendPartial`, as go's
  `OnEmitGossip` does. -/
  | partialGossip (topic : TopicId) (peers : List Peer)
  /-- Connect to the peers a prune from `source` offered
  (`gossipsub-v1.1.md`, "PRUNE Backoff and Peer Exchange"). The node
  verifies each signed peer record, stores its addresses, and dials
  under its own bound on pending dials, as go-libp2p-pubsub's
  `pxConnect` and `connector` do. -/
  | pxConnect (source : Peer) (peers : List Rpc.PeerInfo)
  deriving DecidableEq, BEq, Repr

/-- The one error constructor: an RPC that does not decode. -/
inductive ProtocolError where
  /-- The RPC bytes do not decode. -/
  | decode (e : Pb.Error)
  deriving DecidableEq, BEq, Repr

/-! ## Boolean membership -/

/-- Boolean membership, decided by `DecidableEq`. The core uses it in
the guards of its definitions, because a `Prop` membership has no
decidable instance in the core library. -/
def memB {α : Type} [DecidableEq α] (a : α) (l : List α) : Bool :=
  l.any (fun b => decide (b = a))

/-- The Boolean membership holds exactly for the `Prop` membership. -/
theorem memB_eq_true {α : Type} [DecidableEq α] {a : α} {l : List α} :
    memB a l = true ↔ a ∈ l := by
  rw [memB, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hab⟩
    rw [← of_decide_eq_true hab]
    exact hb
  · intro h
    exact ⟨a, h, by simp⟩

/-! ## Association list accessors -/

/-- The first list of the topic. -/
def lookupTopic : List (TopicId × List Peer) → TopicId → List Peer
  | [], _ => []
  | (t', ps) :: l, t => if t = t' then ps else lookupTopic l t

/-- Replace the first entry of the topic, or append the topic. -/
def upsertMesh : List (TopicId × List Peer) → TopicId → List Peer →
    List (TopicId × List Peer)
  | [], t, ps => [(t, ps)]
  | (t', ps') :: l, t, ps => if t = t' then (t, ps) :: l else (t', ps') :: upsertMesh l t ps

/-- The mesh of the topic. -/
def meshOf (s : State) (topic : TopicId) : List Peer := lookupTopic s.mesh topic

/-- Write the mesh of the topic. -/
def setTopicMesh (s : State) (topic : TopicId) (ps : List Peer) : State :=
  { s with mesh := upsertMesh s.mesh topic ps }

/-- The first fanout record of the topic. -/
def lookupFanout : List (TopicId × Fanout) → TopicId → Option Fanout
  | [], _ => none
  | (t', f) :: l, t => if t = t' then some f else lookupFanout l t

/-- The fanout peers of the topic. -/
def fanoutOf (s : State) (topic : TopicId) : List Peer :=
  match lookupFanout s.fanout topic with
  | some f => f.peers
  | none => []

/-- Write the fanout record of the topic. -/
def setTopicFanout (s : State) (topic : TopicId) (f : Fanout) : State :=
  { s with fanout := (topic, f) :: s.fanout.filter (fun e => decide (e.1 ≠ topic)) }

/-- The first record of the peer. -/
def lookupPeer : List (Peer × PeerData) → Peer → Option PeerData
  | [], _ => none
  | (q', pd) :: l, q => if q = q' then some pd else lookupPeer l q

/-- Replace the first record of the peer, or append the peer. -/
def upsertPeer : List (Peer × PeerData) → Peer → PeerData → List (Peer × PeerData)
  | [], q, pd => [(q, pd)]
  | (q', pd') :: l, q, pd => if q = q' then (q, pd) :: l else (q', pd') :: upsertPeer l q pd

/-- The record of the peer. -/
def peerOf (s : State) (q : Peer) : Option PeerData := lookupPeer s.peers q

/-- Write the record of the peer. -/
def setPeer (s : State) (q : Peer) (pd : PeerData) : State :=
  { s with peers := upsertPeer s.peers q pd }

/-- Update every peer record through `f`. The list order stays. -/
def mapPeers (s : State) (f : Peer → PeerData → PeerData) : State :=
  { s with peers := s.peers.map (fun e => (e.1, f e.1 e.2)) }

/-- Update the score state of one peer and leave every other field. -/
def updateScoreOf (s : State) (q : Peer) (f : Score.PeerState → Score.PeerState) : State :=
  mapPeers s (fun r pd => if r = q then { pd with score := f pd.score } else pd)

/-- The score of a peer at the state time. A missing peer scores 0. -/
def scoreOf (p : Params) (s : State) (q : Peer) : Score :=
  match peerOf s q with
  | some pd => Score.score p.score pd.score s.now
  | none => 0

/-- The peer speaks floodsub (`/floodsub/1.0.0`). Such a peer joins no
mesh and gets no gossip. It gets every message of its topics, as
go-libp2p-pubsub's `rpcs` sends to peers without the mesh feature. -/
def isFlood (s : State) (q : Peer) : Bool :=
  ((peerOf s q).map (fun pd => pd.proto == .floodsub)).getD false

/-- The next heartbeat is due: the interval has passed since the last one. -/
def heartbeatDue (p : Params) (s : State) (now : Millis) : Prop :=
  s.lastHeartbeat + p.heartbeatInterval ≤ now

/-- The heartbeat condition is decidable. -/
instance heartbeatDueDecidable (p : Params) (s : State) (now : Millis) :
    Decidable (heartbeatDue p s now) :=
  decidable_of_iff (s.lastHeartbeat + p.heartbeatInterval ≤ now) Iff.rfl

/-- The RPC grafts the topic. -/
def rpcGrafts (r : Rpc.RPC) (t : TopicId) : Prop :=
  match r.control with
  | some c => ∃ g ∈ c.graft, g.topicId = t.name
  | none => False

/-- The RPC prunes the topic. -/
def rpcPrunes (r : Rpc.RPC) (t : TopicId) : Prop :=
  match r.control with
  | some c => ∃ p ∈ c.prune, p.topicId = t.name
  | none => False

/-- The RPC carries nonempty ihave gossip. -/
def rpcHasIhave (r : Rpc.RPC) : Prop :=
  match r.control with
  | some c => c.ihave ≠ []
  | none => False

/-- The messages the action list delivers to the application. -/
def delivers : List Action → List Message
  | [] => []
  | .deliver m :: as => m :: delivers as
  | .sendRpc _ _ :: as => delivers as
  | .validate _ _ _ :: as => delivers as
  | .partialIn _ _ :: as => delivers as
  | .partialGossip _ _ :: as => delivers as
  | .pxConnect _ _ :: as => delivers as

/-! ## Outgoing RPC constructors -/

/-- An RPC that carries one control message. -/
def controlRpc (c : Rpc.ControlMessage) : Rpc.RPC :=
  { subscriptions := [], publish := [], control := some c }

/-! ## Partial messages (gossipsub v1.3)

The extension's state is per peer and per topic: the choice each peer
announced in its `SubOpts`. The core reads it in four places. A forward
of a full message skips a peer that takes partial messages on its topic.
Gossip skips such a peer too ("Partial Message Gossip"). An outbound
partial message loses its data for a peer that did not request it. An
inbound partial message goes to the application. -/

/-- Our choice for topic `t`. -/
def partialOpts (p : Params) (t : TopicId) : PartialOpts :=
  ((p.partialTopics.find? (fun e => decide (e.1 = t))).map (·.2)).getD {}

/-- The choice peer `q` announced for `t`. -/
def peerPartial (s : State) (q : Peer) (t : TopicId) : PartialOpts :=
  ((peerOf s q).bind fun pd => (pd.partialSubs.find? (fun e => decide (e.1 = t))).map (·.2)).getD {}

/-- `q` takes partial messages on `t` in place of full ones: it
requested them, and we can send them (`partial-messages.md`, "Behavior
table"). -/
def wantsPartial (p : Params) (s : State) (q : Peer) (t : TopicId) : Bool :=
  (partialOpts p t).sends && (peerPartial s q t).requests

/-- Drop each send of a full message to a peer that takes partial
messages on its topic. Other actions pass. -/
def dropForPartial (p : Params) (s : State) (acts : List Action) : List Action :=
  acts.filter fun a => match a with
    | .sendRpc q r => !(r.publish.any fun m => wantsPartial p s q m.topic)
    | _ => true

theorem mem_dropForPartial {p : Params} {s : State} {acts : List Action} {a : Action}
    (h : a ∈ dropForPartial p s acts) : a ∈ acts :=
  (List.mem_filter.1 h).1

/-- The Extensions message the node sends first on each stream: present
when some topic can send partial messages (`gossipsub-v1.3.md`). -/
def ownExtensions (p : Params) : Option Rpc.ControlExtensions :=
  if p.partialTopics.any (·.2.sends) then some { partialMessages := true } else none

/-- One subscription record with our choice for the topic. An
unsubscribe carries no flags: the receiver ignores them there. -/
def subOpts (p : Params) (t : TopicId) (on : Bool) : Rpc.SubOpts :=
  let o : PartialOpts := if on then partialOpts p t else {}
  { subscribe := on, topicid := t.name, requestsPartial := o.requests,
    supportsSendingPartial := o.sends }

/-- The hello RPC: one subscription record per topic, with our choice
for each. -/
def helloRpc (topics : List TopicId) (p : Option Params := none) : Rpc.RPC :=
  { subscriptions := topics.map (fun t => match p with
      | some p => subOpts p t true
      | none => ({ subscribe := true, topicid := t.name } : Rpc.SubOpts)),
    publish := [], control := none }

/-- A graft of the topic. -/
def graftRpc (t : TopicId) : Rpc.RPC :=
  controlRpc { ihave := [], iwant := [], graft := [{ topicId := t.name }], prune := [] }

/-- A prune of the topic with the backoff period in seconds, and the
peers of the peer exchange (`pxPeers`). -/
def pruneRpc (t : TopicId) (backoff : Millis) (px : List Rpc.PeerInfo := []) : Rpc.RPC :=
  controlRpc
    { ihave := [], iwant := [], graft := [],
      prune := [{ topicId := t.name, peers := px, backoff := some (backoff / 1000) }] }

/-- An IHAVE of the topic with the message ids. -/
def ihaveRpc (t : TopicId) (ids : List MessageId) : Rpc.RPC :=
  controlRpc
    { ihave := [{ topicId := t.name, messageIds := ids }], iwant := [], graft := [], prune := [] }

/-- An IWANT with the message ids. -/
def iwantRpc (ids : List MessageId) : Rpc.RPC :=
  controlRpc { ihave := [], iwant := [{ messageIds := ids }], graft := [], prune := [] }

/-- An RPC that forwards one published message. -/
def publishRpc (m : Message) : Rpc.RPC :=
  { subscriptions := [], publish := [m], control := none }

/-- The explicit peers that announced the topic and sit outside its mesh:
"every new valid incoming message is forwarded to the direct peers"
(`gossipsub-v1.1.md`, "Explicit Peering Agreements"). -/
def explicitTargets (s : State) (topic : TopicId) : List Peer :=
  s.explicit.filter fun q =>
    ((peerOf s q).map (fun pd => memB topic pd.subs)).getD false && !memB q (meshOf s topic)

/-- The peers that receive a forwarded inbound message: the mesh and the
explicit peers. The sender already holds the message, so the list drops
the sender. -/
def inboundTargets (s : State) (sender : Peer) (topic : TopicId) : List Peer :=
  (meshOf s topic ++ explicitTargets s topic).filter (fun q => decide (q ≠ sender))

/-- The floodsub peers that announced the topic, at or above the publish
threshold: go-libp2p-pubsub's `rpcs` sends every message to them, from
us or forwarded ("floodsub peers", `gossipsub.go`). -/
def floodTargets (p : Params) (s : State) (topic : TopicId) : List Peer :=
  (s.peers.filter fun e => e.2.proto == .floodsub && memB topic e.2.subs &&
    decide (p.thresholds.publishThreshold ≤ scoreOf p s e.1)).map Prod.fst

/-- One publish RPC per accepted message, to each mesh peer, explicit
peer, and floodsub peer other than the sender. The targets come from
the pre-state. -/
def forwardPubs (p : Params) (s : State) (sender : Peer) (ms : List Message) : List Action :=
  ms.flatMap fun m =>
    let mesh := inboundTargets s sender m.topic
    let flood := (floodTargets p s m.topic).filter (fun q => decide (q ≠ sender) && !memB q mesh)
    (mesh ++ flood).map fun q => Action.sendRpc q (publishRpc m)

/-! ## The decode boundary -/

/-- The one decode entry point of the core: wire bytes to an RPC value.
The protobuf decoder returns the empty suffix, so the core drops it. -/
def decodeRpc (bytes : List Nat) : Except ProtocolError Rpc.RPC :=
  match Pb.decodeMessage? (α := Rpc.RPC) bytes with
  | .ok (r, _) => .ok r
  | .error e => .error (.decode e)

/-- A decode that the model decoder reports as successful decodes to the
same value. -/
theorem decodeRpc_of_decodeMessage (bytes : List Nat) (r : Rpc.RPC)
    (h : Pb.decodeMessage? (α := Rpc.RPC) bytes = .ok (r, [])) :
    decodeRpc bytes = .ok r := by
  simp [decodeRpc, h]

/-- The message's `data` fits `Params.maxDataSize`. -/
def sizeOk (p : Params) (m : Message) : Bool :=
  match p.maxDataSize with
  | none => true
  | some cap => decide ((m.data.getD []).length ≤ cap)

/-- A `strictNoSign` validation, and the size cap, as a `Bool`. A
message over the cap counts as invalid, so the sender takes the P₄
penalty, as for any message the router rejects. -/
def validationOk (p : Params) (m : Message) : Bool :=
  sizeOk p m &&
  match Sign.validate p.prims (fun x => Pb.encodeMessage x) .strictNoSign m with
  | .ok _ => true
  | .error _ => false

/-! ## Message acceptance -/

/-- One run of the acceptance loop: the accepted messages, the ids the
loop saw, and the seen cache after the run. -/
structure Accept where
  /-- The accepted messages, in arrival order. -/
  accepted : List Message
  /-- The ids the loop passed. -/
  done : List MessageId
  /-- The seen cache after the run. -/
  cache : Cache.SeenIndex

/-- Accept a list of messages. The gate reads the pre-state cache `c0`,
so a message that the pre-state cache holds as seen is never accepted.
The local `done` list rejects a repeated id inside the one event. -/
def accept (c0 : Cache.SeenIndex) (now : Millis) (idf : Sign.MsgIdFn)
    (done : List MessageId) (c : Cache.SeenIndex) : List Message → Accept
  | [] => { accepted := [], done := done, cache := c }
  | m :: ms =>
      if c0.contains (idf m) now || memB (idf m) done then
        accept c0 now idf done c ms
      else
        let r := accept c0 now idf (idf m :: done) (c.add (idf m) now) ms
        { accepted := m :: r.accepted, done := r.done, cache := r.cache }

/-! ## The heartbeat plan -/

/-- One per-topic heartbeat plan: the kept mesh, the pruned peers, and
the added peers. -/
structure TopicPlan where
  /-- The topic. -/
  topic : TopicId
  /-- The mesh after the heartbeat. -/
  kept : List Peer
  /-- The peers that leave the mesh. -/
  pruned : List Peer
  /-- The peers that enter the mesh. -/
  added : List Peer
  deriving Repr

/-- The peers that announce the topic. -/
def announced (s : State) (topic : TopicId) : List Peer :=
  (s.peers.filter (fun e => memB topic e.2.subs)).map Prod.fst

/-- The peer exchange of a prune to `target` on `topic`
(`gossipsub-v1.1.md`, "PRUNE Backoff and Peer Exchange"). With `doPX`
set, it names up to `prunePeers` other gossipsub peers of the topic,
each at or above score 0. A target below score 0 gets none: "no PX
information is emitted towards those peers". Each entry carries the
peer id only. The node adds the signed peer record that the host holds,
as go-libp2p-pubsub's `makePrune` reads it from the certified address
book. go shuffles the candidates. This core takes them in state order,
so a transcript replays. -/
def pxPeers (p : Params) (s : State) (target : Peer) (topic : TopicId) : List Rpc.PeerInfo :=
  if p.doPX && decide (0 ≤ scoreOf p s target) then
    ((announced s topic).filter (fun q =>
        decide (q ≠ target) && decide (0 ≤ scoreOf p s q) && !isFlood s q)).take p.prunePeers
      |>.map fun q => { peerId := some (Bytes.toNatList q.toBytes), signedPeerRecord := none }
  else []

/-- The peers a heartbeat grafts. First come `need` candidates. When the
mesh is still `outNeed` short of outbound peers, outbound candidates
follow, up to that quota ("the router selects outbound peers from the
candidates and grafts them", `gossipsub-v1.1.md`, lines 186 to 203). An
inbound peer never fills the outbound quota. -/
def pickAdded (cands : List Peer) (isOut : Peer → Bool) (need outNeed : Nat) : List Peer :=
  let base := cands.take need
  let extra := ((cands.filter isOut).filter (fun q => !memB q base)).take
    (outNeed - (base.filter isOut).length)
  base ++ extra

/-- A picked peer is a candidate. -/
theorem mem_pickAdded {cands : List Peer} {isOut : Peer → Bool} {need outNeed : Nat} {q : Peer}
    (h : q ∈ pickAdded cands isOut need outNeed) : q ∈ cands := by
  unfold pickAdded at h
  rw [List.mem_append] at h
  rcases h with h | h
  · exact List.mem_of_mem_take h
  · exact (List.mem_filter.1 (List.mem_filter.1 (List.mem_of_mem_take h)).1).1

/-- One topic plan:
- An overfull mesh keeps its `dScore` best and its `D_out` outbound
  peers, and fills to `d`.
- An underfull mesh, or one short of outbound peers, takes candidates
  from the order (`pickAdded`).
- A candidate is outside the mesh, outside backoff, known, not explicit,
  and at or above score 0.

The plan cuts the kept list at `dHigh`, so the mesh bound holds by
construction. -/
def planTopic (p : Params) (s : State) (now : Millis) (order : List Peer)
    (topic : TopicId) : TopicPlan :=
  let ps := meshOf s topic
  -- An overfull mesh keeps its `dScore` best-scoring peers, then fills to
  -- `d` from the rest (`gossipsub-v1.1.md`, lines 247 to 258), and prunes
  -- the others. Ties and the fill prefer the back of the mesh list, and
  -- the kept peers keep their mesh order.
  let best := (ps.reverse.mergeSort (fun a b => decide (scoreOf p s b ≤ scoreOf p s a))).take
    p.mesh.dScore
  let isOut (q : Peer) : Bool := ((peerOf s q).map (·.outbound)).getD false
  let rest := ps.filter (fun q => !memB q best)
  -- `D_out`: the fill takes outbound peers first, up to the quota
  -- (`gossipsub-v1.1.md`, lines 186 to 203).
  let outShort := p.dOut - (best.filter isOut).length
  let fillOut := (rest.filter isOut).take outShort
  let restIn := rest.filter (fun q => !memB q fillOut)
  let fill := fillOut ++ restIn.drop (restIn.length - (p.mesh.d - best.length - fillOut.length))
  let kept0 := if ps.length > p.mesh.dHigh then
      ps.filter (fun q => memB q best || memB q fill)
    else ps
  let over := ps.filter (fun q => !memB q kept0)
  let need := if kept0.length < p.mesh.dLow then p.mesh.d - kept0.length else 0
  let cands := order.filter (fun q =>
    !memB q ps && !(Cache.Backoff.active s.backoff q topic now) &&
      (peerOf s q).isSome && decide (0 ≤ scoreOf p s q) && !memB q s.explicit && !isFlood s q)
  let added := pickAdded cands isOut need (p.dOut - (kept0.filter isOut).length)
  { topic := topic, kept := (kept0 ++ added).take p.mesh.dHigh, pruned := over, added := added }

/-- The plan of every topic in the mesh. -/
def planList (p : Params) (s : State) (now : Millis) (order : List Peer) : List TopicPlan :=
  s.mesh.map (fun e => planTopic p s now order e.1)

/-- Apply the score updates of the plans: a pruned peer takes the prune
update, an added peer takes the graft update. -/
def applyPlanScores (p : Params) (s : State) (plans : List TopicPlan) : State :=
  mapPeers s (fun q pd =>
    { pd with
      score := plans.foldl (fun sc pl =>
        if memB q pl.pruned then Score.prune p.score sc s.now pl.topic
        else if memB q pl.added then Score.graft p.score sc s.now pl.topic
        else sc) pd.score })

/-- The actions of the plans: a prune to each pruned peer, with the peer
exchange of an oversubscribed mesh (`pxPeers` over `s`), then a graft to
each added peer. -/
def planActions (p : Params) (s : State) (pl : TopicPlan) : List Action :=
  pl.pruned.map (fun q => Action.sendRpc q (pruneRpc pl.topic p.pruneBackoff (pxPeers p s q pl.topic))) ++
    pl.added.map (fun q => Action.sendRpc q (graftRpc pl.topic))

/-- Write the planned meshes and drop the peers below score 0 from every
mesh. A dropped peer takes the prune score update. -/
def settleMesh (p : Params) (s : State) (plans : List TopicPlan) : State :=
  { s with
    mesh := plans.map (fun pl =>
      (pl.topic, pl.kept.filter (fun q => decide (0 ≤ scoreOf p s q)))),
    peers := s.peers.map (fun e =>
      (e.1, if scoreOf p s e.1 < 0 then
        { e.2 with
          score := s.topics.foldl (fun sc t => Score.prune p.score sc s.now t) e.2.score }
      else e.2)) }

/-- The gossip targets of a topic. A candidate is a peer of the order at
or above the gossip threshold. The candidates exclude the peers of the
topic's mesh and fanout, and the floodsub peers. Adaptive gossip
(`gossipsub-v1.1.md`, lines 165 to 184) takes at least `dLazy`
candidates. When `gossipFactor` percent of the candidates is more, it
takes that many. -/
def gossipTargets (p : Params) (s : State) (order : List Peer) (t : TopicId) : List Peer :=
  let cands := order.filter (fun q =>
    decide (p.thresholds.gossipThreshold ≤ scoreOf p s q) &&
      !(memB q (meshOf s t)) && !(memB q (fanoutOf s t)) && !isFlood s q)
  cands.take (max p.mesh.dLazy (cands.length * p.gossipFactor / 100))

/-- The gossip actions of each topic of the mesh and the fanout. The core
draws the targets of a topic (`gossipTargets`), then splits them, as
go-libp2p-pubsub's `emitGossip` does. A target that takes partial
messages on the topic gets no IHAVE. In its place, one `partialGossip`
names all such targets (`partial-messages.md`, "Partial Message
Gossip"). Each other target gets an IHAVE with the gossip ids of the
topic.

Partial messages never enter the message cache. So the core makes the
offer also when the cache holds no id. The ids come from the cache as it
stands, so a heartbeat emits gossip before it shifts the cache. -/
def gossipActions (p : Params) (s : State) (order : List Peer) : List Action :=
  let topics := s.mesh.map Prod.fst ++ s.fanout.map Prod.fst
  topics.flatMap fun t =>
    let targets := gossipTargets p s order t
    let partials := targets.filter (wantsPartial p s · t)
    let ids := Cache.MessageIndex.gossipIds s.mcache t
    let offer := if partials = [] then [] else [Action.partialGossip t partials]
    let ihaves := if ids = [] then []
      else (targets.filter (!wantsPartial p s · t)).map fun q => Action.sendRpc q (ihaveRpc t ids)
    ihaves ++ offer

/-- The state at the start of the heartbeat: the scores decayed when a
decay interval has passed, the new clock, the cleared backoff table, the
pruned seen cache, and the shifted message cache. -/
def freshState (p : Params) (s : State) (now : Millis) : State :=
  let due := decide (p.score.global.decayInterval ≤ now - s.lastDecay)
  { s with
    peers := if due then
        s.peers.map (fun e => (e.1, { e.2 with score := Score.decay p.score e.2.score }))
      else s.peers,
    lastDecay := if due then now else s.lastDecay,
    now := now,
    lastHeartbeat := now,
    backoff := Cache.Backoff.clear s.backoff now,
    seen := Cache.SeenIndex.prune s.seen now,
    mcache := Cache.MessageIndex.shift s.mcache }

/-- The per-topic plans of the heartbeat. -/
def heartbeatPlans (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List TopicPlan :=
  planList p (freshState p s now) now order

/-- The state after the plan score updates. -/
def planScored (p : Params) (s : State) (now : Millis) (order : List Peer) : State :=
  applyPlanScores p (freshState p s now) (heartbeatPlans p s now order)

/-- The state after the heartbeat. -/
def heartbeatNext (p : Params) (s : State) (now : Millis) (order : List Peer) : State :=
  settleMesh p (planScored p s now order) (heartbeatPlans p s now order)

/-- The plan actions of the heartbeat. -/
def planActionsOf (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List Action :=
  (heartbeatPlans p s now order).flatMap (planActions p (freshState p s now))

/-- The negative prune actions of the heartbeat. -/
def negativeActions (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List Action :=
  (heartbeatPlans p s now order).flatMap (fun pl =>
    (pl.kept.filter (fun q => decide (scoreOf p (planScored p s now order) q < 0))).map
      (fun q => Action.sendRpc q (pruneRpc pl.topic p.pruneBackoff)))

/-- The state the gossip reads: the mesh and the scores after the
heartbeat, and the message cache before the shift. The spec emits the
ids, then shifts the cache. -/
def gossipState (p : Params) (s : State) (now : Millis) (order : List Peer) : State :=
  { heartbeatNext p s now order with mcache := s.mcache }

/-- The actions of the heartbeat. Gossip is emitted after the mesh is
settled and before the cache shifts. -/
def heartbeatActions (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List Action :=
  planActionsOf p s now order ++ negativeActions p s now order ++
    gossipActions p (gossipState p s now order) order

/-- The heartbeat: decay, the fresh clock and tables, the per-topic plan,
the score updates, the mesh write with the negative prune, and the
actions of the plan, the negative prune, and the gossip. -/
def heartbeat (p : Params) (s : State) (now : Millis) (order : List Peer) :
    State × List Action :=
  (heartbeatNext p s now order, heartbeatActions p s now order)

/-- The heartbeat in one pass: the fresh state, the plans, and the scored
state each once. `heartbeat` names them part by part, and the proofs
reason about the parts. Lean evaluates strictly and hoists no call out
of a function, so the parts would plan every topic again for each use,
and `negativeActions` once more for each kept peer of each plan. -/
def heartbeatOnce (p : Params) (s : State) (now : Millis) (order : List Peer) :
    State × List Action :=
  let fresh := freshState p s now
  let plans := planList p fresh now order
  let scored := applyPlanScores p fresh plans
  let next := settleMesh p scored plans
  let negative := plans.flatMap (fun pl =>
    (pl.kept.filter (fun q => decide (scoreOf p scored q < 0))).map
      (fun q => Action.sendRpc q (pruneRpc pl.topic p.pruneBackoff)))
  (next, plans.flatMap (planActions p fresh) ++ negative ++
    gossipActions p { next with mcache := s.mcache } order)

/-- The compiled heartbeat is the one pass. Both sides unfold to the same
terms, and `csimp` makes the compiler run `heartbeatOnce` wherever the
code says `heartbeat`. -/
@[csimp] theorem heartbeat_eq_once : @heartbeat = @heartbeatOnce := by
  funext p s now order
  rfl

/-! ## The event handlers -/

/-- A peer joins: record it, and send the hello RPC with our topics. A
known peer keeps its record. -/
def join (p : Params) (s : State) (peer : Peer) (proto : PubsubProto) :
    State × List Action :=
  -- A peer back within `retainScore` of its departure gets its old score
  -- (`gossipsub-v1.1.md`, lines 212 to 214), so a reconnect does not
  -- reset a bad score.
  let kept := (s.retained.find? (fun e => decide (e.1 = peer ∧ s.now < e.2.2 + p.retainScore))).map
    (·.2.1)
  let s0 : State := { s with retained := s.retained.filter (fun e => decide (e.1 ≠ peer)) }
  let s1 :=
    if (peerOf s peer).isSome then s
    else setPeer s0 peer
      { score := (kept.map (·.score)).getD Score.PeerState.zero, proto := proto, subs := [] }
  (s1, [Action.sendRpc peer (helloRpc s.topics)])

/-- A peer leaves: drop it from the peers, the meshes, the fanout
records, and the promise table, and keep its record with the departure
time for `retainScore` (`join`). -/
def leave (s : State) (peer : Peer) : State × List Action :=
  ({ s with
     peers := s.peers.filter (fun e => decide (e.1 ≠ peer)),
     mesh := s.mesh.map (fun e => (e.1, e.2.filter (fun q => decide (q ≠ peer)))),
     fanout := s.fanout.map (fun e =>
       (e.1, { e.2 with peers := e.2.peers.filter (fun q => decide (q ≠ peer)) })),
     iwant := s.iwant.filter (fun e => decide (e.peer ≠ peer)),
     retained := match peerOf s peer with
       | some pd => (peer, pd, s.now) :: s.retained.filter (fun e => decide (e.1 ≠ peer))
       | none => s.retained },
   [])

/-- One subscription option against the announced list. -/
def applySubOpts (subs : List TopicId) (o : Rpc.SubOpts) : List TopicId :=
  let t : TopicId := ⟨o.topicid⟩
  if o.subscribe then (if memB t subs then subs else t :: subs)
  else subs.filter (fun u => decide (u ≠ t))

/-- One subscription option against the partial-messages choices. A
subscribe records the flags. An unsubscribe drops them, and the core
ignores the flags of the unsubscribe itself (`partial-messages.md`,
"Changes to `SubOpts`"). -/
def applyPartialOpts (ps : List (TopicId × PartialOpts)) (o : Rpc.SubOpts) :
    List (TopicId × PartialOpts) :=
  let t : TopicId := ⟨o.topicid⟩
  let rest := ps.filter (fun e => decide (e.1 ≠ t))
  if o.subscribe && (o.requestsPartial || o.supportsSendingPartial) then
    (t, { requests := o.requestsPartial,
          supports := o.requestsPartial || o.supportsSendingPartial }) :: rest
  else rest

/-- The subscription options of one RPC that the caps admit: all of
them, or none (`Params.maxSubscriptionsPerRpc`). The count check comes
first, so an RPC past it costs no pass over the peer's topics. rust
ignores the subscriptions of such an RPC in the same way
(`behaviour.rs`, "Subscription filter error"). -/
def admitSubs (p : Params) (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    List Rpc.SubOpts :=
  let perRpcOk := match p.maxSubscriptionsPerRpc with
    | some m => decide (subs.length ≤ m)
    | none => true
  if !perRpcOk then []
  else match p.maxSubscribedTopics, peerOf s sender with
    | some m, some pd => if (subs.foldl applySubOpts pd.subs).length ≤ m then subs else []
    | _, _ => subs

/-- Update the announced topics of the sender, and its choices. -/
def handleSubs (s : State) (sender : Peer) (subs : List Rpc.SubOpts) : State :=
  match peerOf s sender with
  | some pd => setPeer s sender { pd with subs := subs.foldl applySubOpts pd.subs,
                                          partialSubs := subs.foldl applyPartialOpts pd.partialSubs }
  | none => s

/-- Note `sender` in the delivery record of each message. A first
arrival starts the record. With `credit`, a later arrival from a mesh
peer within the topic's `meshMessageDeliveriesWindow` of the first is a
near-first delivery, and counts toward P₃ (`gossipsub-v1.1.md`, "P₃"),
once per peer. -/
def recordOne (p : Params) (credit : Bool) (sender : Peer) (st : State) (m : Message) : State :=
  match st.deliveries.get? (p.msgId m) with
  | none => { st with deliveries := st.deliveries.insert (p.msgId m) (st.now, [sender]) }
  | some (t, senders) =>
    if memB sender senders then st
    else
      let window := ((p.score.topics m.topic).map (·.meshMessageDeliveriesWindow)).getD 0
      if credit && memB sender (meshOf st m.topic) && decide (st.now ≤ t + window) then
        updateScoreOf { st with deliveries := st.deliveries.insert (p.msgId m) (t, sender :: senders) }
          sender (fun sc => Score.meshDelivery p.score sc m.topic)
      else { st with deliveries := st.deliveries.insert (p.msgId m) (t, sender :: senders) }

/-- `recordOne` over the messages of an RPC, in order. -/
def recordDeliveries (p : Params) (credit : Bool) (sender : Peer) (s : State)
    (ms : List Message) : State :=
  ms.foldl (recordOne p credit sender) s

/-- Handle the published messages of an RPC: validate, accept, cache,
score, deliver, and forward. -/
def handlePubs (p : Params) (s : State) (sender : Peer) (ms : List Message) :
    State × List Action :=
  let valid := ms.filter (fun m => validationOk p m)
  let invalid := ms.filter (fun m => !(validationOk p m))
  let r := accept s.seen s.now p.msgId [] s.seen valid
  let s1 : State :=
    { s with
      seen := r.cache,
      mcache := r.accepted.foldl (fun c m => c.put (p.msgId m) m) s.mcache,
      -- Any arrival of an id keeps every IWANT promise for it.
      iwant := valid.foldl (fun ps m => ps.deliver (p.msgId m)) s.iwant }
  let s2 := invalid.foldl (fun st m =>
    updateScoreOf st sender (fun sc => Score.invalidDelivery p.score sc m.topic)) s1
  let s3 := r.accepted.foldl (fun st m =>
    updateScoreOf st sender (fun sc =>
      let sc' := Score.firstDelivery p.score sc m.topic
      if memB sender (meshOf s m.topic) then Score.meshDelivery p.score sc' m.topic else sc')) s2
  (recordDeliveries p true sender s3 valid, r.accepted.map (fun m => Action.deliver m) ++
    dropForPartial p s (forwardPubs p s sender r.accepted))

/-- An IDONTWANT of the ids. -/
def idontwantRpc (ids : List MessageId) : Rpc.RPC :=
  controlRpc { ihave := [], iwant := [], graft := [], prune := [],
               idontwant := [{ messageIds := ids }] }

/-- Drop each forward of a message to a peer that sent IDONTWANT for its
id. Other actions pass. -/
def dropDontWant (p : Params) (s : State) (acts : List Action) : List Action :=
  acts.filter fun a => match a with
    | .sendRpc q r => !(r.publish.any fun m => memB (q, p.msgId m) s.dontSend)
    | _ => true

theorem mem_dropDontWant {p : Params} {s : State} {acts : List Action} {a : Action}
    (h : a ∈ dropDontWant p s acts) : a ∈ acts :=
  (List.mem_filter.1 h).1

/-- Drop the IDONTWANT pairs of one id. -/
def forgetDontWant (s : State) (id : MessageId) : State :=
  { s with dontSend := s.dontSend.filter fun e => decide (e.2 ≠ id) }

/-- Record the IDONTWANT ids of a control message from `sender`, up to
`dontSendCap` pairs. -/
def noteDontWant (p : Params) (s : State) (sender : Peer) : Option Rpc.ControlMessage → State
  | none => s
  | some c =>
    let ids := c.idontwant.flatMap (·.messageIds)
    if ids.isEmpty then s
    else { s with dontSend := (ids.map (sender, ·) ++ s.dontSend).take p.dontSendCap }

/-- `handlePubs` under `Params.validateMessages`. It accepts as
`handlePubs` does, then holds each accepted message for the
application's answer. The seen cache records the id at once, so the
core drops a duplicate during the wait. The message cache, the delivery
scores, and the forward wait for `Validation.accept` (`handleValidated`).
So gossip and IWANT never serve a message that the application did not
accept. -/
def holdPubs (p : Params) (s : State) (sender : Peer) (ms : List Message) :
    State × List Action :=
  let valid := ms.filter (fun m => validationOk p m)
  let invalid := ms.filter (fun m => !(validationOk p m))
  let r := accept s.seen s.now p.msgId [] s.seen valid
  let s1 : State :=
    { s with
      seen := r.cache,
      pending := s.pending ++ r.accepted.map (fun m => (p.msgId m, sender, m))
      pendingAt := s.pendingAt ++ r.accepted.map (fun m => (p.msgId m, s.now))
      iwant := valid.foldl (fun ps m => ps.deliver (p.msgId m)) s.iwant }
  let s2 := invalid.foldl (fun st m =>
    updateScoreOf st sender (fun sc => Score.invalidDelivery p.score sc m.topic)) s1
  -- "When the peer receives the first message instance it immediately
  -- broadcasts ... IDONTWANT with the messageId to all its mesh peers.
  -- This could be performed prior to the message validation"
  -- (`gossipsub-v1.2.md`, "Basic scenario").
  let large := r.accepted.filter fun m => match p.idontwantThreshold with
    | some t => decide (t ≤ (m.data.getD []).length)
    | none => false
  let dontWants := large.flatMap fun m =>
    (inboundTargets s sender m.topic).map fun q => Action.sendRpc q (idontwantRpc [p.msgId m])
  -- The record notes every sender; the credit and the penalty wait for
  -- the answer (`handleValidated`).
  (recordDeliveries p false sender s2 valid,
    r.accepted.map (fun m => Action.validate m (p.msgId m) sender) ++ dontWants)

/-- The application's answer on a held message. An unknown id is a
no-op: the answer came twice, or for a message never held. Accept
caches the message, scores the delivery, and forwards it to the mesh
peers other than the source. Reject counts an invalid delivery against
the source. Ignore only drops it. -/
def handleValidated (p : Params) (s : State) (id : MessageId) (_source : Peer)
    (outcome : Validation) : State × List Action :=
  match s.pending.find? (fun e => decide (e.1 = id)) with
  | none => (s, [])
  | some (_, src, m) =>
    let s1 : State := { s with pending := s.pending.filter (fun e => decide (e.1 ≠ id)),
                               pendingAt := s.pendingAt.filter (fun e => decide (e.1 ≠ id)) }
    -- The score goes to the peer the core recorded at receipt. The
    -- answer's source is the application's copy of the same value.
    -- Every peer that sent the message while it waited, from the record.
    let others := ((s.deliveries.get? id).map (·.2)).getD [] |>.filter (· != src)
    match outcome with
    | .accept =>
      let s2 : State := { s1 with mcache := s1.mcache.put id m }
      let s3 := updateScoreOf s2 src (fun sc =>
        let sc' := Score.firstDelivery p.score sc m.topic
        if memB src (meshOf s m.topic) then Score.meshDelivery p.score sc' m.topic else sc')
      -- The mesh peers that sent it during the wait delivered near-first.
      let s4 := others.foldl (fun st q =>
        if memB q (meshOf s m.topic) then
          updateScoreOf st q (fun sc => Score.meshDelivery p.score sc m.topic)
        else st) s3
      -- The forward skips the IDONTWANT peers. The seen cache stops a
      -- second forward, so the pairs of this id go.
      (forgetDontWant s4 id, dropDontWant p s (dropForPartial p s (forwardPubs p s src [m])))
    | .reject =>
      -- Every sender of an invalid message takes P₄, as go's
      -- `markInvalidMessageDelivery` does for each peer of the record.
      ((src :: others).foldl (fun st q =>
        updateScoreOf st q (fun sc => Score.invalidDelivery p.score sc m.topic)) s1, [])
    | .ignore => (s1, [])

/-- Drop the held messages older than the message cache's history,
`historyLength` heartbeats. rust-libp2p keeps an unvalidated message in
its message cache, so it expires with that window. An expired message
stays in the seen cache, so the core drops a later copy as a duplicate,
and no score changes. The loop calls this at each heartbeat, outside
`step`, so the step theorems hold unchanged. -/
def expirePending (p : Params) (s : State) (now : Millis) : State :=
  let ttl := p.window.historyLength * p.heartbeatInterval
  let old := (s.pendingAt.filter fun e => decide (e.2 + ttl ≤ now)).map (·.1)
  if old.isEmpty then s
  else { s with pending := s.pending.filter (fun e => !memB e.1 old),
                pendingAt := s.pendingAt.filter (fun e => !memB e.1 old) }

/-- Opportunistic grafting (`gossipsub-v1.1.md`, lines 260 to 279). A mesh
whose median peer score is below `opportunisticGraftThreshold` grafts up
to `opportunisticGraftPeers` peers. Each grafted peer:
- announced the topic
- is outside the mesh and its backoff
- is not explicit
- scores above the median

The answer is the state with the meshes grown, and the grafts to send. -/
def opportunisticGrafts (p : Params) (s : State) (now : Millis) : State × List Action :=
  s.mesh.foldl (fun (st, acts) (t, ps) =>
    if ps.isEmpty then (st, acts) else
    let scores := (ps.map (scoreOf p st)).mergeSort (fun a b => decide (a ≤ b))
    let median := scores.getD (scores.length / 2) 0
    if decide (p.thresholds.opportunisticGraftThreshold ≤ median) then (st, acts) else
    let cands := ((announced st t).filter fun q =>
      !memB q ps && !(Cache.Backoff.active st.backoff q t now) && !memB q st.explicit &&
        !isFlood st q && decide (median < scoreOf p st q)).take p.opportunisticGraftPeers
    let st := cands.foldl (fun st q =>
      updateScoreOf (setTopicMesh st t (q :: meshOf st t)) q (fun sc => Score.graft p.score sc now t)) st
    (st, acts ++ cands.map (fun q => Action.sendRpc q (graftRpc t)))) (s, [])

/-- Heartbeat upkeep that the spike runs outside `step` (the loop calls it
before each tick), so the heartbeat theorems hold unchanged. Each part
cites #95:

* Fanout expiry (`gossipsub-v1.0.md`, lines 449 to 473): a topic with no
  publish for `fanoutTtl` loses its fanout.
* Broken IWANT promises (`gossipsub-v1.1.md`, spam measures): each
  promise past its deadline adds one P₇ behaviour penalty to its peer,
  and leaves the table.
* P₆ (`gossipsub-v1.1.md`, "P₆"): each peer's IP colocation count is the
  number of known peers on its IP address.
* Opportunistic grafting, on the heartbeats that the loop marks
  (`opportunistic`): see `opportunisticGrafts`. -/
def maintain (p : Params) (s : State) (now : Millis) (opportunistic : Bool := false) :
    State × List Action :=
  let broken := Cache.PromiseTable.broken s.iwant now
  let s0 := broken.foldl (fun st (q, n) =>
    updateScoreOf st q (fun sc => (List.replicate n ()).foldl (fun sc _ => Score.behaviourPenalty sc) sc)) s
  -- P₆: one count per IP address over the known peers.
  let ips := s0.peers.filterMap (·.2.ip)
  let s1 : State := { s0 with peers := s0.peers.map fun (q, pd) =>
    (q, { pd with score := { pd.score with ipColocation :=
      match pd.ip with
      | some a => (ips.filter (· == a)).length
      | none => 0 } }) }
  let (s1, grafts) := if opportunistic then opportunisticGrafts p s1 now else (s1, [])
  ({ s1 with
    iwant := s1.iwant.filter (fun e => decide (now < e.deadline))
    fanout := s1.fanout.filter (fun e => decide (now < e.2.lastPublished + p.fanoutTtl))
    -- A delivery record lives as long as the seen cache remembers its id.
    deliveries := s1.deliveries.filter (fun _ (t, _) => decide (now < t + p.seen.ttl))
    -- The IHAVE counts are per heartbeat.
    ihaveSeen := {}
    -- A retransmission count lives as long as its message is cached.
    served := s1.served.filter (fun k _ => (Cache.MessageIndex.get s1.mcache k.2).isSome)
    -- A departed peer's record lives `retainScore`.
    retained := s1.retained.filter (fun e => decide (now < e.2.2 + p.retainScore)) }, grafts)

/-- Whether the promise table holds the pair. -/
def promised (ps : Cache.PromiseTable) (q : Peer) (id : MessageId) : Bool :=
  ps.any (fun e => decide (e.peer = q ∧ e.id = id))

/-- Handle one IHAVE: request the ids that are unseen, uncached, and not
promised, and record the promise. -/
def handleIhave (p : Params) (s : State) (sender : Peer) (i : Rpc.ControlIHave) :
    State × List Action :=
  -- The spam measures: past `maxIhaveMessages` IHAVEs this heartbeat,
  -- the core ignores the peer. We ask it for at most `maxIhaveLength`
  -- ids.
  let (count, asked) := s.ihaveSeen.getD sender (0, 0)
  -- An IHAVE for a topic we do not subscribe to asks for nothing, as
  -- go's `handleIHave` skips a topic with no mesh (`gossipsub.go`, line
  -- 960). The gossip threshold applies to the whole RPC (`gossipOf`).
  if !memB (⟨i.topicId⟩ : TopicId) s.topics then
    (s, [])
  else if p.maxIhaveMessages ≤ count then (s, [])
  else
  let wanted := (i.messageIds.filter (fun id =>
    !(s.seen.contains id s.now) && (Cache.MessageIndex.get s.mcache id).isNone &&
      !(promised s.iwant sender id))).take (p.maxIhaveLength - asked)
  let s1 : State :=
    { s with
      iwant := wanted.foldl
        (fun ps id => ps.promise sender id (s.now + p.iwantDeadline)) s.iwant
      ihaveSeen := s.ihaveSeen.insert sender (count + 1, asked + wanted.length) }
  (s1, if wanted = [] then [] else [Action.sendRpc sender (iwantRpc wanted)])

/-- Handle one IWANT: answer each id that the message cache holds under
the same id, at most `gossipRetransmission` times per peer and id. -/
def handleIwant (p : Params) (s : State) (sender : Peer) (w : Rpc.ControlIWant) :
    State × List Action :=
  let answers := w.messageIds.filterMap (fun id =>
    match Cache.MessageIndex.get s.mcache id with
    | some m =>
      if p.msgId m = id && decide (s.served.getD (sender, id) 0 < p.gossipRetransmission) then some m
      else none
    | none => none)
  let s1 : State := { s with served := answers.foldl (fun t m =>
    t.insert (sender, p.msgId m) (t.getD (sender, p.msgId m) 0 + 1)) s.served }
  (s1, answers.map (fun m => Action.sendRpc sender (publishRpc m)))

/-- Handle one GRAFT. An unknown topic is ignored. A member is a no-op.
A peer in backoff, or a mesh at `dHigh`, gets a prune. Otherwise the
peer enters the mesh and takes the graft score update. -/
def handleGraft (p : Params) (s : State) (sender : Peer) (g : Rpc.ControlGraft) :
    State × List Action :=
  if memB (⟨g.topicId⟩ : TopicId) s.topics then
    if memB sender (meshOf s ⟨g.topicId⟩) then (s, [])
    else if Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true then
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)])
    else if p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length then
      -- The mesh is oversubscribed, the case PX exists for.
      (s, [Action.sendRpc sender
        (pruneRpc ⟨g.topicId⟩ p.pruneBackoff (pxPeers p s sender ⟨g.topicId⟩))])
    -- "It is an error to GRAFT on an explicit peer, and such an attempt
    -- should be logged and rejected with a PRUNE."
    else if memB sender s.explicit then
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)])
    else
      match peerOf s sender with
      | some pd =>
          (setPeer (setTopicMesh s ⟨g.topicId⟩ (sender :: meshOf s ⟨g.topicId⟩)) sender
            { pd with score := Score.graft p.score pd.score s.now ⟨g.topicId⟩ }, [])
      | none => (s, [])
  else (s, [])

/-- The state after a prune records the backoff pair, for a topic we
subscribe to. A prune for any other topic changes nothing, as go's
`handlePrune` skips a topic with no mesh (`gossipsub.go`, line 1163).
Otherwise a peer could add one pair per prune, for topics of its
choosing and with a backoff of its choosing, and the table would grow
without bound. -/
def pruneState (p : Params) (s : State) (sender : Peer) (q : Rpc.ControlPrune) : State :=
  if memB (⟨q.topicId⟩ : TopicId) s.topics then
    { s with
      backoff := Cache.Backoff.add s.backoff sender ⟨q.topicId⟩
        (match q.backoff with
          | some sec => sec * 1000
          | none => p.pruneBackoff) s.now }
  else s

/-- Handle one PRUNE: record the backoff pair, and remove the sender
from the topic mesh with the prune score update. -/
def handlePrune (p : Params) (s : State) (sender : Peer) (q : Rpc.ControlPrune) :
    State × List Action :=
  if memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) then
    match peerOf (pruneState p s sender q) sender with
    | some pd =>
        (setPeer (setTopicMesh (pruneState p s sender q) ⟨q.topicId⟩
            ((meshOf (pruneState p s sender q) ⟨q.topicId⟩).filter
              (fun r => decide (r ≠ sender)))) sender
           { pd with
             score := Score.prune p.score pd.score (pruneState p s sender q).now ⟨q.topicId⟩ }, [])
    | none => (pruneState p s sender q, [])
  else (pruneState p s sender q, [])

/-- Run one handler over a list, threading the state and appending the
actions. -/
def mapHandlers {β : Type} (f : State → β → State × List Action) :
    List β → State → State × List Action
  | [], s => (s, [])
  | b :: bs, s =>
      let r := f s b
      let r' := mapHandlers f bs r.1
      (r'.1, r.2 ++ r'.2)

/-- The state after the ihave handlers. -/
def controlIhaves (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handleIhave p st sender b) c.ihave s).1

/-- The state after the iwant handlers. -/
def controlIwants (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handleIwant p st sender b) c.iwant (controlIhaves p s sender c)).1

/-- The state after the graft handlers. -/
def controlGrafts (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handleGraft p st sender b) c.graft (controlIwants p s sender c)).1

/-- The state after the prune handlers. -/
def controlPrunes (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handlePrune p st sender b) c.prune (controlGrafts p s sender c)).1

/-- The actions of the control handlers: ihave, iwant, graft, then prune. -/
def controlActions (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    List Action :=
  (mapHandlers (fun st b => handleIhave p st sender b) c.ihave s).2 ++
    (mapHandlers (fun st b => handleIwant p st sender b) c.iwant
      (controlIhaves p s sender c)).2 ++
    (mapHandlers (fun st b => handleGraft p st sender b) c.graft
      (controlIwants p s sender c)).2 ++
    (mapHandlers (fun st b => handlePrune p st sender b) c.prune
      (controlGrafts p s sender c)).2

/-- The peer exchange a prune offers, as the connect actions. A prune
counts when we joined its topic, as go and rust skip a prune of an
unknown topic.

The core ignores a sender below `acceptPXThreshold`. The spec's
parameter table says "PX information by peers below this threshold is
ignored", and go and rust read it so (`score < acceptPXThreshold`). The
prose of "Peer Scoring" says "exceeds". That reading would refuse a
peer at the threshold, so at the default 0 it would refuse every new
peer. The table, its constraint "Must be >= 0", and both
implementations decide the question.

From each prune, the action keeps up to `prunePeers` entries whose peer
id decodes and names a peer we do not know. go truncates after a
shuffle, and this core truncates in wire order. The core reads the
score from the state before the prunes, as go's `handlePrune` does. -/
def pxAccept (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) : List Action :=
  if decide (p.thresholds.acceptPXThreshold ≤ scoreOf p s sender) then
    c.prune.filterMap fun q =>
      let fresh := (q.peers.filter fun info =>
        match info.peerId with
        | some b =>
          match Libp2p.Identity.PeerId.ofBytes? (Bytes.ofNatList b) with
          | .ok pid => (peerOf s pid).isNone
          | .error _ => false
        | none => false).take p.prunePeers
      if memB (⟨q.topicId⟩ : TopicId) s.topics && !fresh.isEmpty then
        some (Action.pxConnect sender fresh)
      else none
  else []

/-- The control envelope with the sender's gossip dropped when its score
is below `GossipThreshold`: "incoming gossip is ignored"
(`gossipsub-v1.1.md`, the threshold table). go reads the score once per
RPC for its IHAVE and its IWANT (`handleIHave`, `handleIWant`,
`gossipsub.go`, lines 941 and 1015), and so does this gate. -/
def gossipOf (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    Rpc.ControlMessage :=
  if scoreOf p s sender < p.thresholds.gossipThreshold then { c with ihave := [], iwant := [] }
  else c

/-- The four control handlers in one pass: each kind runs once, on the
state the kind before it left. `controlPrunes` and `controlActions`
state the same answer, one kind at a time (`runControl_eq`), and the
proofs reason about them. Lean evaluates strictly, so those two would
each run the handlers before them again, five IHAVE passes per RPC. -/
def runControl (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State × List Action :=
  let r1 := mapHandlers (fun st b => handleIhave p st sender b) c.ihave s
  let r2 := mapHandlers (fun st b => handleIwant p st sender b) c.iwant r1.1
  let r3 := mapHandlers (fun st b => handleGraft p st sender b) c.graft r2.1
  let r4 := mapHandlers (fun st b => handlePrune p st sender b) c.prune r3.1
  (r4.1, r1.2 ++ r2.2 ++ r3.2 ++ r4.2)

/-- The one pass gives the state and the actions of the kind-by-kind
statement. Both sides unfold to the same terms. -/
theorem runControl_eq (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    runControl p s sender c = (controlPrunes p s sender c, controlActions p s sender c) := rfl

/-- Handle the control envelope: the gossip gate, then ihave, iwant,
graft, and prune, and the peer exchange of the prunes (`pxAccept`). -/
def handleControl (p : Params) (s : State) (sender : Peer) :
    Option Rpc.ControlMessage → State × List Action
  | none => (s, [])
  | some c =>
    let c := gossipOf p s sender c
    let r := runControl p s sender c
    (r.1, r.2 ++ pxAccept p s sender c)

/-- Note the sender's Extensions message. It belongs in the first RPC,
once. A later one costs a P₇ penalty (`gossipsub-v1.3.md`, "Peer Scoring
on Protocol Violations"). -/
def noteExtensions (s : State) (sender : Peer) (rpc : Rpc.RPC) : State :=
  match peerOf s sender with
  | none => s
  | some pd =>
    let ext := rpc.control.bind (·.extensions)
    let extensions := if pd.rpcSeen then pd.extensions else ext
    let s1 := setPeer s sender { pd with rpcSeen := true, extensions }
    if pd.rpcSeen && ext.isSome then updateScoreOf s1 sender Score.behaviourPenalty else s1

/-- The topic a partial message names. -/
def partialTopic (pm : Rpc.PartialMessage) : TopicId :=
  ⟨(pm.topicId.bind fun b => Bytes.toString? (Bytes.ofNatList b)).getD ""⟩

/-- An inbound partial message goes to the application, mesh peer or
not. A topic where we cannot send partial messages drops it. Data on a
topic where we did not request partial messages costs a P₇ penalty
(`partial-messages.md`, "Changes to `SubOpts`"). Our choices are fixed
parameters, so the spec's allowance for a peer that has not yet seen our
latest `SubOpts` never applies. -/
def handlePartialIn (p : Params) (s : State) (sender : Peer) :
    Option Rpc.PartialMessage → State × List Action
  | none => (s, [])
  | some pm =>
    let o := partialOpts p (partialTopic pm)
    if pm.partialMessage.isSome && !o.requests then
      (updateScoreOf s sender Score.behaviourPenalty, [])
    else if o.sends then (s, [Action.partialIn sender pm])
    else (s, [])

/-- The application sends a partial message to `q`. A peer that
requested partial messages on the topic gets it whole. A peer that only
supports them gets the metadata without the data. Any other peer gets
nothing. On a topic where we cannot send partial messages, no peer gets
one. -/
def sendPartial (p : Params) (s : State) (q : Peer) (pm : Rpc.PartialMessage) : List Action :=
  let t := partialTopic pm
  let theirs := peerPartial s q t
  let rpc (m : Rpc.PartialMessage) : Rpc.RPC :=
    { subscriptions := [], publish := [], control := none, partialRpc := some m }
  if !(partialOpts p t).sends then []
  else if theirs.requests then [Action.sendRpc q (rpc pm)]
  else if theirs.supports && pm.partsMetadata.isSome then
    [Action.sendRpc q (rpc { pm with partialMessage := none })]
  else []

/-- Handle a decoded RPC: subscriptions, published messages, control,
the Extensions message, and a partial message. -/
def handleRpc (p : Params) (s : State) (sender : Peer) (rpc : Rpc.RPC) :
    State × List Action :=
  let s1 := handleSubs s sender (admitSubs p s sender rpc.subscriptions)
  let (s2, a2) := if p.validateMessages then holdPubs p s1 sender rpc.publish
    else handlePubs p s1 sender rpc.publish
  let (s3, a3) := handleControl p s2 sender rpc.control
  let s4 := noteExtensions (noteDontWant p s3 sender rpc.control) sender rpc
  let (s5, a5) := handlePartialIn p s4 sender rpc.partialRpc
  (s5, a2 ++ a3 ++ a5)

/-- The RPC branch gates: a graylisted peer is ignored, an unknown peer
is ignored, and a decode failure is the one error. -/
def rpcStep (p : Params) (s : State) (sender : Peer) (bytes : List Nat) :
    Except ProtocolError (State × List Action) :=
  if scoreOf p s sender < p.thresholds.graylistThreshold then .ok (s, [])
  else
    match peerOf s sender with
    | none => .ok (s, [])
    | some _ =>
        match decodeRpc bytes with
        | .error e => .error e
        | .ok rpc => .ok (handleRpc p s sender rpc)

/-- The fanout candidates: gossipsub peers that announce the topic, at or
above score 0. -/
def fanoutCandidates (p : Params) (s : State) (topic : TopicId) : List Peer :=
  (announced s topic).filter (fun q => decide (0 ≤ scoreOf p s q) && !isFlood s q)

/-- Extend the fanout of the topic to `d`, and set its last publish
time. -/
def extendFanout (p : Params) (s : State) (topic : TopicId) : State :=
  match lookupFanout s.fanout topic with
  | some f =>
      let need := if f.peers.length < p.mesh.d then p.mesh.d - f.peers.length else 0
      let cands := (fanoutCandidates p s topic).filter (fun q => !memB q f.peers)
      setTopicFanout s topic { peers := f.peers ++ cands.take need, lastPublished := s.now }
  | none =>
      setTopicFanout s topic
        { peers := (fanoutCandidates p s topic).take p.mesh.d, lastPublished := s.now }

/-- The forward targets of a publish: the mesh when we subscribe to the
topic, the fanout otherwise, and the floodsub peers of the topic
(`floodTargets`). -/
def publishTargets (p : Params) (s : State) (topic : TopicId) : List Peer :=
  if p.floodPublish then
    -- Every peer that announced the topic, at or above the publish threshold.
    (s.peers.filter (fun e => memB topic e.2.subs &&
      decide (p.thresholds.publishThreshold ≤ scoreOf p s e.1))).map Prod.fst
  else
    let gossip := if memB topic s.topics then meshOf s topic else fanoutOf s topic
    gossip ++ (floodTargets p s topic).filter (fun q => !memB q gossip)

/-- The application publishes a message: validate, cache, record the id
as seen, extend the fanout when we do not subscribe, and forward to the
targets. The application already holds its own message, so this path
emits no deliver action. The seen record stops a later echo of the same
id from being forwarded again. -/
def publishLocal (p : Params) (s : State) (m : Message) : State × List Action :=
  if validationOk p m then
    let s1 : State :=
      { s with
        mcache := s.mcache.put (p.msgId m) m
        seen := s.seen.add (p.msgId m) s.now }
    let s2 := if memB m.topic s1.topics then s1 else extendFanout p s1 m.topic
    (s2, dropForPartial p s2
      ((publishTargets p s2 m.topic).map (fun q => Action.sendRpc q (publishRpc m))))
  else (s, [])

/-- The application subscribes: add the topic, move the fanout peers
into the mesh, fill to `d`, and graft the added peers. -/
def subscribe (p : Params) (s : State) (topic : TopicId) : State × List Action :=
  let s1 : State :=
    if memB topic s.topics then s else { s with topics := topic :: s.topics }
  let ps := meshOf s1 topic
  let ps1 := ps ++ (fanoutOf s1 topic).filter (fun q => !memB q ps)
  let need := if ps1.length < p.mesh.d then p.mesh.d - ps1.length else 0
  let cands := (announced s1 topic).filter (fun q =>
    !memB q ps1 && decide (0 ≤ scoreOf p s1 q) &&
      !(Cache.Backoff.active s1.backoff q topic s1.now) && !isFlood s1 q)
  let added := cands.take need
  let s2 := setTopicMesh s1 topic ((ps1 ++ added).take p.mesh.dHigh)
  let s3 : State :=
    { s2 with fanout := s2.fanout.filter (fun e => decide (e.1 ≠ topic)) }
  (s3, added.map (fun q => Action.sendRpc q (graftRpc topic)))

/-- The application unsubscribes: drop the topic, empty its mesh and
fanout, prune the old mesh peers, and record the backoff pairs. -/
def unsubscribe (p : Params) (s : State) (topic : TopicId) : State × List Action :=
  let ps := meshOf s topic
  let s1 : State := { s with topics := s.topics.filter (fun t => decide (t ≠ topic)) }
  let s2 := setTopicMesh s1 topic []
  let s3 : State :=
    { s2 with fanout := s2.fanout.filter (fun e => decide (e.1 ≠ topic)) }
  let s4 := ps.foldl
    (fun st q =>
      { st with backoff := Cache.Backoff.add st.backoff q topic p.unsubscribeBackoff s.now })
    s3
  (s4, ps.map (fun q => Action.sendRpc q (pruneRpc topic p.unsubscribeBackoff (pxPeers p s q topic))))

/-- Record the protocol a known peer negotiated. A floodsub peer leaves
every mesh and fanout, as it can take part in neither. An unknown peer
changes nothing. -/
def setProtocol (s : State) (peer : Peer) (proto : PubsubProto) : State :=
  match peerOf s peer with
  | none => s
  | some pd =>
    let s1 := setPeer s peer { pd with proto }
    if proto == .floodsub then
      { s1 with
        mesh := s1.mesh.map (fun e => (e.1, e.2.filter (fun q => decide (q ≠ peer)))),
        fanout := s1.fanout.map (fun e =>
          (e.1, { e.2 with peers := e.2.peers.filter (fun q => decide (q ≠ peer)) })) }
    else s1

/-! ## The transition and the driver -/

/-- One transition of the router. Every event is handled, and only an
RPC that does not decode returns an error. -/
def step (p : Params) (s : State) : Event → Except ProtocolError (State × List Action)
  | .peerJoined peer proto => .ok (join p s peer proto)
  | .peerLeft peer => .ok (leave s peer)
  | .rpc sender bytes => rpcStep p s sender bytes
  | .publish msg => .ok (publishLocal p s msg)
  | .subscribe topic => .ok (subscribe p s topic)
  | .unsubscribe topic => .ok (unsubscribe p s topic)
  | .tick now order =>
      if heartbeatDue p s now then .ok (heartbeat p s now order) else .ok (s, [])
  | .validated id source outcome => .ok (handleValidated p s id source outcome)
  | .peerInfo peer outbound ip =>
    .ok (match peerOf s peer with
      | some pd => (setPeer s peer { pd with outbound, ip }, [])
      | none => (s, []))
  | .appScore peer score =>
    .ok (updateScoreOf s peer (fun sc => { sc with appScore := score }), [])
  | .sendPartial peer msg => .ok (s, sendPartial p s peer msg)
  | .partialJudged peer topic valid =>
    .ok (updateScoreOf s peer (fun sc =>
      if valid then Score.firstDelivery p.score sc topic else Score.invalidDelivery p.score sc topic), [])
  | .protocol peer proto => .ok (setProtocol s peer proto, [])

/-- The transcript driver: the events in order. The first error stops
the run. -/
def run (p : Params) (s : State) : List Event → Except ProtocolError (State × List Action)
  | [] => .ok (s, [])
  | e :: es =>
      match step p s e with
      | .error err => .error err
      | .ok (s1, a1) =>
          match run p s1 es with
          | .error err => .error err
          | .ok (s2, a2) => .ok (s2, a1 ++ a2)

/-! ## The spec defaults -/

/-- The spec defaults: d 6, dLow 4, dHigh 12, dScore 4, dLazy 6,
heartbeat 1000 ms, fanout ttl 60000 ms, prune backoff 60000 ms, gossip
factor 25 percent, iwant deadline 3000 ms, window 5 over 3, seen
capacity 65536 and ttl 120000 ms, and zero score weights with no
configured topic. The numbers follow `gossipsub-v1.0.md` and the v1.1
recommendations. The seen capacity is a chosen memory bound that the
spec leaves open. `validationOk` uses `strictNoSign`, which requires
`from` and `seqno` to be absent, so the spec's default id `from ++ seqno`
would be empty for every accepted message. The default here is the
payload bytes. `Sign.defaultMsgId` stays available for a caller that
pairs it with `strictSign`. -/
def defaults : Params where
  score :=
    { topics := fun _ => none,
      global :=
        { appSpecificWeight := 0
          ipColocationFactorWeight := 0
          ipColocationFactorThreshold := 1
          behaviourPenaltyWeight := 0
          behaviourPenaltyThreshold := 0
          behaviourPenaltyDecay := scoreScale
          decayInterval := 1000
          decayToZero := 0
          topicScoreCap := 0 } }
  thresholds :=
    { gossipThreshold := 0
      publishThreshold := 0
      graylistThreshold := 0
      acceptPXThreshold := 0
      opportunisticGraftThreshold := 0 }
  mesh := { d := 6, dLow := 4, dHigh := 12, dScore := 4, dLazy := 6 }
  heartbeatInterval := 1000
  fanoutTtl := 60000
  pruneBackoff := 60000
  gossipFactor := 25
  iwantDeadline := 3000
  window := { historyLength := 5, historyGossip := 3, valid := by decide }
  seen := { capacity := 65536, ttl := 120000, valid := by decide }
  prims := Sign.Prims.identity
  msgId := fun m => ⟨m.data.getD []⟩

/-- The spec's parameter constraints a parameter set breaks, each named
(`gossipsub-v1.1.md`, the parameter tables, lines 548 to 588, and the
thresholds, lines 228 to 245). `Params.Valid` carries only `d ≤ dHigh`,
the bound the mesh theorems consume. A node checks the rest here at
start. `defaults` breaks the threshold rules on purpose: every threshold
and weight is 0, which disables scoring. -/
def Params.problems (p : Params) : List String :=
  let g := p.score.global
  let t := p.thresholds
  let checks : List (Bool × String) := [
    (decide (p.mesh.dLow ≤ p.mesh.d ∧ p.mesh.d ≤ p.mesh.dHigh), "D_lo ≤ D ≤ D_hi"),
    (decide (p.dOut < p.mesh.dLow), "D_out must be less than D_lo"),
    (decide (p.dOut ≤ p.mesh.d / 2), "D_out must be at most D/2"),
    (decide (p.mesh.dScore ≤ p.mesh.d), "D_score must be at most D"),
    (decide (p.gossipFactor ≤ 100), "GossipFactor must be in [0, 1]"),
    (decide (t.gossipThreshold < 0), "GossipThreshold must be < 0"),
    (decide (t.publishThreshold ≤ t.gossipThreshold), "PublishThreshold must be <= GossipThreshold"),
    (decide (t.graylistThreshold < t.publishThreshold), "GraylistThreshold must be < PublishThreshold"),
    (decide (0 ≤ t.acceptPXThreshold), "AcceptPXThreshold must be >= 0"),
    (decide (0 ≤ t.opportunisticGraftThreshold), "OpportunisticGraftThreshold must be >= 0"),
    (decide (0 ≤ g.appSpecificWeight), "AppSpecificWeight must be positive"),
    (decide (g.ipColocationFactorWeight ≤ 0), "IPColocationFactorWeight must be negative"),
    (decide (1 ≤ g.ipColocationFactorThreshold), "IPColocationFactorThreshold must be at least 1"),
    (decide (g.behaviourPenaltyWeight ≤ 0), "BehaviourPenaltyWeight must be negative"),
    (decide (0 < g.behaviourPenaltyDecay ∧ g.behaviourPenaltyDecay < scoreScale),
      "BehaviourPenaltyDecay must be between 0 and 1")]
  (checks.filter (!·.1)).map (·.2)

/-! ## Accessor lemmas -/

private theorem lookupTopic_upsertMesh_same (l : List (TopicId × List Peer)) (t : TopicId)
    (ps : List Peer) : lookupTopic (upsertMesh l t ps) t = ps := by
  induction l with
  | nil => simp [upsertMesh, lookupTopic]
  | cons e l ih =>
    obtain ⟨t', ps'⟩ := e
    by_cases h : t = t'
    · simp [upsertMesh, lookupTopic, h]
    · simp [upsertMesh, lookupTopic, h, ih]

private theorem lookupTopic_upsertMesh_ne (t' t : TopicId) (h : t' ≠ t)
    (l : List (TopicId × List Peer)) (ps : List Peer) :
    lookupTopic (upsertMesh l t ps) t' = lookupTopic l t' := by
  induction l with
  | nil => simp [upsertMesh, lookupTopic, h]
  | cons e l ih =>
    obtain ⟨u, us⟩ := e
    by_cases h2 : t = u
    · subst h2
      simp [upsertMesh, lookupTopic, h]
    · simp [upsertMesh, lookupTopic, h2, ih]

/-- The mesh of the written topic. -/
theorem meshOf_setTopicMesh_same (s : State) (t : TopicId) (ps : List Peer) :
    meshOf (setTopicMesh s t ps) t = ps := by
  simp [meshOf, setTopicMesh, lookupTopic_upsertMesh_same]

/-- A write of one topic leaves the mesh of another topic. -/
theorem meshOf_setTopicMesh_ne (s : State) (t t' : TopicId) (h : t' ≠ t)
    (ps : List Peer) : meshOf (setTopicMesh s t ps) t' = meshOf s t' := by
  simp [meshOf, setTopicMesh, lookupTopic_upsertMesh_ne t' t h]

private theorem lookupPeer_upsertPeer_same (l : List (Peer × PeerData)) (q : Peer)
    (pd : PeerData) : lookupPeer (upsertPeer l q pd) q = some pd := by
  induction l with
  | nil => simp [upsertPeer, lookupPeer]
  | cons e l ih =>
    obtain ⟨q', pd'⟩ := e
    by_cases h : q = q'
    · simp [upsertPeer, lookupPeer, h]
    · simp [upsertPeer, lookupPeer, h, ih]

private theorem lookupPeer_upsertPeer_ne (q' q : Peer) (h : q' ≠ q)
    (l : List (Peer × PeerData)) (pd : PeerData) :
    lookupPeer (upsertPeer l q pd) q' = lookupPeer l q' := by
  induction l with
  | nil => simp [upsertPeer, lookupPeer, h]
  | cons e l ih =>
    obtain ⟨u, ud⟩ := e
    by_cases h2 : q = u
    · subst h2
      simp [upsertPeer, lookupPeer, h]
    · simp [upsertPeer, lookupPeer, h2, ih]

/-- The record of the written peer. -/
theorem peerOf_setPeer_same (s : State) (q : Peer) (pd : PeerData) :
    peerOf (setPeer s q pd) q = some pd := by
  simp [peerOf, setPeer, lookupPeer_upsertPeer_same]

/-- A write of one peer leaves the record of another peer. -/
theorem peerOf_setPeer_ne (s : State) (q q' : Peer) (h : q' ≠ q) (pd : PeerData) :
    peerOf (setPeer s q pd) q' = peerOf s q' := by
  simp [peerOf, setPeer, lookupPeer_upsertPeer_ne q' q h]

private theorem lookupPeer_map (l : List (Peer × PeerData))
    (f : Peer → PeerData → PeerData) (q : Peer) :
    lookupPeer (l.map (fun e => (e.1, f e.1 e.2))) q = (lookupPeer l q).map (f q) := by
  induction l with
  | nil => simp [lookupPeer]
  | cons e l ih =>
    obtain ⟨q', pd'⟩ := e
    simp only [List.map_cons, lookupPeer]
    by_cases h : q = q'
    · subst h
      simp
    · simp [h, ih]

/-- The record of a peer after a map over the whole list. -/
theorem peerOf_mapPeers (s : State) (f : Peer → PeerData → PeerData) (q : Peer) :
    peerOf (mapPeers s f) q = (peerOf s q).map (f q) := by
  simp [peerOf, mapPeers, lookupPeer_map]

/-- The score of a peer after a map over the whole peer list. -/
theorem scoreOf_mapPeers (p : Params) (s : State) (f : Peer → PeerData → PeerData)
    (q : Peer) :
    scoreOf p (mapPeers s f) q =
      match peerOf s q with
      | some pd => Score.score p.score (f q pd).score s.now
      | none => 0 := by
  simp only [scoreOf, peerOf_mapPeers]
  cases h : peerOf s q <;> rfl

/-- The score reads only the peer list and the time. -/
theorem scoreOf_congr (p : Params) {s s' : State} (hpeers : s'.peers = s.peers)
    (hnow : s'.now = s.now) (q : Peer) : scoreOf p s' q = scoreOf p s q := by
  simp [scoreOf, peerOf, hpeers, hnow]

/-! ## Plan lemmas -/

/-- The plan of a topic keeps at most `dHigh` peers. -/
theorem planTopic_kept_le (p : Params) (s : State) (now : Millis) (order : List Peer)
    (t : TopicId) : (planTopic p s now order t).kept.length ≤ p.mesh.dHigh := by
  simp only [planTopic]
  rw [List.length_take]
  omega

/-- The lookup of a mesh rebuilt from a list of plans. -/
theorem lookupTopic_map_plans (plans : List TopicPlan) (f : TopicPlan → List Peer)
    (t : TopicId) :
    lookupTopic (plans.map (fun pl => (pl.topic, f pl))) t =
      match plans.find? (fun pl => decide (t = pl.topic)) with
      | some pl => f pl
      | none => [] := by
  induction plans with
  | nil => simp [lookupTopic]
  | cons pl rest ih =>
    simp only [List.map_cons]
    by_cases h : t = pl.topic
    · simp [lookupTopic, List.find?, h]
    · simp [lookupTopic, List.find?, h, ih]


/-- The mesh of a topic after the heartbeat mesh write. -/
theorem meshOf_settleMesh (p : Params) (s : State) (plans : List TopicPlan) (topic : TopicId) :
    meshOf (settleMesh p s plans) topic =
      match plans.find? (fun pl => decide (topic = pl.topic)) with
      | some pl => pl.kept.filter (fun q => decide (0 ≤ scoreOf p s q))
      | none => [] := by
  simp [meshOf, settleMesh, lookupTopic_map_plans]

/-! ## The mesh bound theorem -/

/-- After a heartbeat, every topic mesh holds at most `dHigh` peers.
The kept list is cut at `dHigh` by construction, and the negative prune
only removes peers. -/
theorem heartbeatMeshBound (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ topic, (meshOf s' topic).length ≤ p.mesh.dHigh := by
  intro topic
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  rw [heartbeatNext, meshOf_settleMesh]
  split
  · next pl hfind =>
    have hmem : pl ∈ heartbeatPlans p s now order := List.mem_of_find?_eq_some hfind
    have hmem' : pl ∈ (freshState p s now).mesh.map
        (fun e => planTopic p (freshState p s now) now order e.1) := by
      simpa [heartbeatPlans, planList] using hmem
    simp only [List.mem_map] at hmem'
    obtain ⟨e, _, rfl⟩ := hmem'
    exact Nat.le_trans (List.length_filter_le _ _)
      (planTopic_kept_le p (freshState p s now) now order e.1)
  · exact Nat.zero_le _


/-! ## The graylist gate theorem -/

/-- No RPC is processed from a peer below the graylist threshold. The
graylist premise is the only hypothesis, so the gate is what the
theorem proves: the step returns the pre-state and no actions, and it
does not consult the bytes. -/
theorem rpcGraylistIgnored (p : Params) (s : State) (sender : Peer)
    (bytes : List Nat)
    (hgray : scoreOf p s sender < p.thresholds.graylistThreshold) :
    step p s (.rpc sender bytes) = .ok (s, []) := by
  simp [step, rpcStep, hgray]


/-! ## The graft handler lemmas -/

private theorem handleGraft_unknown (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (h : memB (⟨g.topicId⟩ : TopicId) s.topics = false) :
    handleGraft p s sender g = (s, []) := by
  simp [handleGraft, h]

private theorem handleGraft_member (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = true) :
    handleGraft p s sender g = (s, []) := by
  simp [handleGraft, hsub, hm]

private theorem handleGraft_backoff (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true) :
    handleGraft p s sender g =
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)]) := by
  simp [handleGraft, hsub, hm, hb]

private theorem handleGraft_overfull (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length) :
    handleGraft p s sender g =
      (s, [Action.sendRpc sender
        (pruneRpc ⟨g.topicId⟩ p.pruneBackoff (pxPeers p s sender ⟨g.topicId⟩))]) := by
  simp [handleGraft, hsub, hm, hb, hd]

private theorem handleGraft_explicit (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : ¬ p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length)
    (he : memB sender s.explicit = true) :
    handleGraft p s sender g =
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)]) := by
  simp [handleGraft, hsub, hm, hb, hd, he]

private theorem handleGraft_add (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (pd : PeerData)
    (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : ¬ p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length)
    (he : memB sender s.explicit = false)
    (hpd : peerOf s sender = some pd) :
    handleGraft p s sender g =
      (setPeer (setTopicMesh s ⟨g.topicId⟩ (sender :: meshOf s ⟨g.topicId⟩)) sender
        { pd with score := Score.graft p.score pd.score s.now ⟨g.topicId⟩ }, []) := by
  simp [handleGraft, hsub, hm, hb, hd, he, hpd]

private theorem handleGraft_add_none (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : ¬ p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length)
    (he : memB sender s.explicit = false)
    (hpd : peerOf s sender = none) :
    handleGraft p s sender g = (s, []) := by
  simp [handleGraft, hsub, hm, hb, hd, he, hpd]

private theorem meshOf_addPeer (s : State) (sender : Peer) (pd : PeerData) (t topic : TopicId)
    (h : topic ≠ t) :
    meshOf (setPeer (setTopicMesh s t (sender :: meshOf s t)) sender pd) topic
      = meshOf s topic := by
  simp [meshOf, setPeer, setTopicMesh, lookupTopic_upsertMesh_ne topic t h]

private theorem meshOf_addPeer_same (s : State) (sender : Peer) (pd : PeerData)
    (t : TopicId) :
    meshOf (setPeer (setTopicMesh s t (sender :: meshOf s t)) sender pd) t
      = sender :: meshOf s t := by
  simp [meshOf, setPeer, setTopicMesh, lookupTopic_upsertMesh_same]

private theorem handleGraft_mesh_other (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (topic : TopicId) (h : topic ≠ ⟨g.topicId⟩) :
    meshOf (handleGraft p s sender g).1 topic = meshOf s topic := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · rw [handleGraft_member p s sender g hsub hm]
    · have hm' : memB sender (meshOf s ⟨g.topicId⟩) = false := by
        cases h' : memB sender (meshOf s ⟨g.topicId⟩) <;> simp_all
      by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · rw [handleGraft_backoff p s sender g hsub hm' hb]
      · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
          cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
        by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · rw [handleGraft_overfull p s sender g hsub hm' hb' hd]
        · by_cases he : memB sender s.explicit = true
          · rw [handleGraft_explicit p s sender g hsub hm' hb' hd he]
          · have he' : memB sender s.explicit = false := by
              cases h' : memB sender s.explicit <;> simp_all
            cases hpd : peerOf s sender with
            | none => rw [handleGraft_add_none p s sender g hsub hm' hb' hd he' hpd]
            | some pd =>
                rw [handleGraft_add p s sender g pd hsub hm' hb' hd he' hpd]
                exact meshOf_addPeer s sender _ ⟨g.topicId⟩ topic h
  · have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = false := by
      cases h' : memB (⟨g.topicId⟩ : TopicId) s.topics <;> simp_all
    rw [handleGraft_unknown p s sender g hsub']

private theorem handleGraft_mesh_same (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hnot : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length) :
    meshOf (handleGraft p s sender g).1 ⟨g.topicId⟩ = meshOf s ⟨g.topicId⟩ := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · rw [handleGraft_member p s sender g hsub hm]
    · by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · rw [handleGraft_backoff p s sender g hsub hnot hb]
      · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
          cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
        by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · rw [handleGraft_overfull p s sender g hsub hnot hb' hd]
        · exfalso
          omega
  · have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = false := by
      cases h' : memB (⟨g.topicId⟩ : TopicId) s.topics <;> simp_all
    rw [handleGraft_unknown p s sender g hsub']

private theorem handleGraft_prune (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub0 : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hnot : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length) :
    ∃ pr, Action.sendRpc sender pr ∈ (handleGraft p s sender g).2 ∧
      rpcPrunes pr ⟨g.topicId⟩ := by
  by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
  · exfalso
    rw [hnot] at hm
    simp at hm
  · by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
    · rw [handleGraft_backoff p s sender g hsub0 hnot hb]
      exact ⟨pruneRpc ⟨g.topicId⟩ p.pruneBackoff, by simp,
        by simp [pruneRpc, controlRpc, rpcPrunes]⟩
    · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
        cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
      rw [handleGraft_overfull p s sender g hsub0 hnot hb' hover]
      exact ⟨pruneRpc ⟨g.topicId⟩ p.pruneBackoff (pxPeers p s sender ⟨g.topicId⟩), by simp,
        by simp [pruneRpc, controlRpc, rpcPrunes]⟩

/-! ## The prune and control handler lemmas -/

private theorem filter_ne_self (l : List Peer) (sender : Peer) (h : memB sender l = false) :
    l.filter (fun r => decide (r ≠ sender)) = l := by
  rw [List.filter_eq_self]
  intro x hx
  have hx' : x ≠ sender := by
    intro hc
    subst hc
    have hmem : memB x l = true := memB_eq_true.mpr hx
    rw [h] at hmem
    simp at hmem
  simp [hx']

private theorem meshOf_pruneState (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (topic : TopicId) :
    meshOf (pruneState p s sender q) topic = meshOf s topic := by
  unfold pruneState
  split <;> simp [meshOf]

private theorem meshOf_setPeer (s : State) (q : Peer) (pd : PeerData) (topic : TopicId) :
    meshOf (setPeer s q pd) topic = meshOf s topic := by
  simp [meshOf, setPeer]

private theorem handlePrune_mesh_same (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (hnot : memB sender (meshOf s ⟨q.topicId⟩) = false) :
    meshOf (handlePrune p s sender q).1 ⟨q.topicId⟩ = meshOf s ⟨q.topicId⟩ := by
  have hst : meshOf (pruneState p s sender q) ⟨q.topicId⟩ = meshOf s ⟨q.topicId⟩ :=
    meshOf_pruneState p s sender q ⟨q.topicId⟩
  by_cases hm : memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) = true
  · cases hpd : peerOf (pruneState p s sender q) sender with
    | none =>
        simp only [handlePrune, hm, ite_true, hpd]
        exact hst
    | some pd =>
        have hf : (meshOf (pruneState p s sender q) ⟨q.topicId⟩).filter
            (fun r => decide (r ≠ sender))
              = meshOf (pruneState p s sender q) ⟨q.topicId⟩ := by
          apply filter_ne_self
          rw [hst]
          exact hnot
        simp only [handlePrune, hm, ite_true, hpd]
        rw [meshOf_setPeer, meshOf_setTopicMesh_same, hf, hst]
  · simp only [handlePrune, hm]
    exact hst

private theorem handlePrune_mesh_ne (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (topic : TopicId) (h : topic ≠ ⟨q.topicId⟩) :
    meshOf (handlePrune p s sender q).1 topic = meshOf s topic := by
  have hst : meshOf (pruneState p s sender q) topic = meshOf s topic :=
    meshOf_pruneState p s sender q topic
  by_cases hm : memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) = true
  · cases hpd : peerOf (pruneState p s sender q) sender with
    | none =>
        simp only [handlePrune, hm, ite_true, hpd]
        exact hst
    | some pd =>
        simp only [handlePrune, hm, ite_true, hpd]
        rw [meshOf_setPeer,
          meshOf_setTopicMesh_ne (pruneState p s sender q) ⟨q.topicId⟩ topic h, hst]
  · simp only [handlePrune, hm]
    exact hst

private theorem handlePrunes_mesh (p : Params) (s : State) (sender : Peer)
    (qs : List Rpc.ControlPrune) (topic : TopicId)
    (hnot : memB sender (meshOf s topic) = false) :
    meshOf (mapHandlers (fun st b => handlePrune p st sender b) qs s).1 topic
      = meshOf s topic := by
  induction qs generalizing s with
  | nil => simp [mapHandlers]
  | cons q qs ih =>
    simp only [mapHandlers]
    by_cases h : topic = ⟨q.topicId⟩
    · subst h
      rw [ih (s := (handlePrune p s sender q).1)
        (by rwa [handlePrune_mesh_same p s sender q hnot]),
        handlePrune_mesh_same p s sender q hnot]
    · rw [ih (s := (handlePrune p s sender q).1)
        (by rwa [handlePrune_mesh_ne p s sender q topic h]),
        handlePrune_mesh_ne p s sender q topic h]

private theorem handleIhave_mesh (p : Params) (s : State) (sender : Peer)
    (i : Rpc.ControlIHave) (topic : TopicId) :
    meshOf (handleIhave p s sender i).1 topic = meshOf s topic := by
  unfold handleIhave
  split
  split
  · simp [meshOf]
  · split <;> simp [meshOf]

private theorem handleIwant_mesh (p : Params) (s : State) (sender : Peer)
    (w : Rpc.ControlIWant) (topic : TopicId) :
    meshOf (handleIwant p s sender w).1 topic = meshOf s topic := by
  simp [handleIwant, meshOf]

private theorem handleIhaves_mesh (p : Params) (s : State) (sender : Peer)
    (is : List Rpc.ControlIHave) (topic : TopicId) :
    meshOf (mapHandlers (fun st b => handleIhave p st sender b) is s).1 topic
      = meshOf s topic := by
  induction is generalizing s with
  | nil => simp [mapHandlers]
  | cons i is ih =>
    simp only [mapHandlers]
    rw [ih (s := (handleIhave p s sender i).1), handleIhave_mesh]

private theorem handleIwants_mesh (p : Params) (s : State) (sender : Peer)
    (ws : List Rpc.ControlIWant) (topic : TopicId) :
    meshOf (mapHandlers (fun st b => handleIwant p st sender b) ws s).1 topic
      = meshOf s topic := by
  induction ws generalizing s with
  | nil => simp [mapHandlers]
  | cons w ws ih =>
    simp only [mapHandlers]
    rw [ih (s := (handleIwant p s sender w).1), handleIwant_mesh]

private theorem topics_mapHandlers {β : Type} (f : State → β → State × List Action)
    (hf : ∀ (s : State) (b : β), (f s b).1.topics = s.topics) :
    ∀ (bs : List β) (s : State), (mapHandlers f bs s).1.topics = s.topics
  | [], s => rfl
  | b :: bs, s => by
      simp only [mapHandlers]
      rw [topics_mapHandlers f hf bs (f s b).1, hf s b]

private theorem handleIhave_topics (p : Params) (s : State) (sender : Peer)
    (i : Rpc.ControlIHave) : (handleIhave p s sender i).1.topics = s.topics := by
  unfold handleIhave
  split
  split
  · simp
  · split <;> simp

private theorem handleIwant_topics (p : Params) (s : State) (sender : Peer)
    (w : Rpc.ControlIWant) : (handleIwant p s sender w).1.topics = s.topics := by
  simp [handleIwant]

private theorem handleGraft_topics (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) : (handleGraft p s sender g).1.topics = s.topics := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · simp [handleGraft, hsub, hm]
    · by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · simp [handleGraft, hsub, hm, hb]
      · by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · simp [handleGraft, hsub, hm, hb, hd]
        · by_cases he : memB sender s.explicit = true
          · simp [handleGraft, hsub, hm, hb, hd, he]
          · cases hpd : peerOf s sender <;>
              simp [handleGraft, hsub, hm, hb, hd, he, hpd, setPeer, setTopicMesh]
  · simp [handleGraft, hsub]

private theorem pruneState_topics (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) : (pruneState p s sender q).topics = s.topics := by
  unfold pruneState
  split <;> rfl

private theorem handlePrune_topics (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) : (handlePrune p s sender q).1.topics = s.topics := by
  by_cases hm : memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) = true
  · cases hpd : peerOf (pruneState p s sender q) sender with
    | none =>
        simp only [handlePrune, hm, ite_true, hpd]
        exact pruneState_topics p s sender q
    | some pd =>
        simp only [handlePrune, hm, ite_true, hpd]
        simp only [setPeer, setTopicMesh]
        exact pruneState_topics p s sender q
  · simp only [handlePrune, hm]
    exact pruneState_topics p s sender q

private theorem controlIwants_topics (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) : (controlIwants p s sender c).topics = s.topics := by
  simp only [controlIwants, controlIhaves]
  rw [topics_mapHandlers (fun st b => handleIwant p st sender b)
      (fun st b => handleIwant_topics p st sender b),
    topics_mapHandlers (fun st b => handleIhave p st sender b)
      (fun st b => handleIhave_topics p st sender b)]

private theorem controlGrafts_topics (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) : (controlGrafts p s sender c).topics = s.topics := by
  simp only [controlGrafts]
  rw [topics_mapHandlers (fun st b => handleGraft p st sender b)
      (fun st b => handleGraft_topics p st sender b),
    controlIwants_topics]

private theorem handleGrafts_mesh (p : Params) (s : State) (sender : Peer)
    (gs : List Rpc.ControlGraft) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length) :
    meshOf (mapHandlers (fun st b => handleGraft p st sender b) gs s).1 topic
      = meshOf s topic := by
  induction gs generalizing s with
  | nil => simp [mapHandlers]
  | cons g gs ih =>
    simp only [mapHandlers]
    have htop : (handleGraft p s sender g).1.topics = s.topics :=
      handleGraft_topics p s sender g
    have hsub' : memB topic (handleGraft p s sender g).1.topics = true := by
      rw [htop]; exact hsub
    by_cases h : topic = ⟨g.topicId⟩
    · subst h
      have hm : meshOf (handleGraft p s sender g).1 ⟨g.topicId⟩ = meshOf s ⟨g.topicId⟩ :=
        handleGraft_mesh_same p s sender g hnot hover
      rw [ih (s := (handleGraft p s sender g).1) hsub' (by rw [hm]; exact hnot)
        (by rw [hm]; exact hover), hm]
    · have hm : meshOf (handleGraft p s sender g).1 topic = meshOf s topic :=
        handleGraft_mesh_other p s sender g topic h
      rw [ih (s := (handleGraft p s sender g).1) hsub' (by rw [hm]; exact hnot)
        (by rw [hm]; exact hover), hm]

private theorem handleGrafts_prune (p : Params) (s : State) (sender : Peer)
    (gs : List Rpc.ControlGraft) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length)
    (hg : ∃ g ∈ gs, g.topicId = topic.name) :
    ∃ pr, Action.sendRpc sender pr ∈
        (mapHandlers (fun st b => handleGraft p st sender b) gs s).2 ∧
      rpcPrunes pr topic := by
  induction gs generalizing s with
  | nil => simp at hg
  | cons g gs ih =>
    simp only [mapHandlers]
    by_cases hsame : g.topicId = topic.name
    · have ht : (⟨g.topicId⟩ : TopicId) = topic := by rw [hsame]
      have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = true := by
        rw [ht]; exact hsub
      have hnot' : memB sender (meshOf s ⟨g.topicId⟩) = false := by
        rw [ht]; exact hnot
      have hover' : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length := by
        rw [ht]; exact hover
      obtain ⟨pr, hpr, hrpc⟩ := handleGraft_prune p s sender g hsub' hnot' hover'
      refine ⟨pr, List.mem_append_left _ hpr, ?_⟩
      rwa [ht] at hrpc
    · have hg' : ∃ g' ∈ gs, g'.topicId = topic.name := by
        obtain ⟨g', hg'mem, hg'eq⟩ := hg
        rcases List.mem_cons.mp hg'mem with h | h
        · rw [h] at hg'eq
          exact absurd hg'eq hsame
        · exact ⟨g', h, hg'eq⟩
      have htop : (handleGraft p s sender g).1.topics = s.topics :=
        handleGraft_topics p s sender g
      have hmesh : meshOf (handleGraft p s sender g).1 topic = meshOf s topic := by
        by_cases h : topic = ⟨g.topicId⟩
        · subst h
          exact handleGraft_mesh_same p s sender g hnot hover
        · exact handleGraft_mesh_other p s sender g topic h
      obtain ⟨pr, hpr, hrpc⟩ := ih (s := (handleGraft p s sender g).1)
        (by rw [htop]; exact hsub) (by rw [hmesh]; exact hnot)
        (by rw [hmesh]; exact hover) hg'
      exact ⟨pr, List.mem_append_right _ hpr, hrpc⟩

private theorem handleControl_mesh (p : Params) (s : State) (sender : Peer)
    (c : Option Rpc.ControlMessage) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length) :
    meshOf (handleControl p s sender c).1 topic = meshOf s topic := by
  cases c with
  | none => rfl
  | some c0 =>
    simp only [handleControl, runControl_eq]
    generalize gossipOf p s sender c0 = c
    have h1 : meshOf (controlIhaves p s sender c) topic = meshOf s topic := by
      simp only [controlIhaves]
      exact handleIhaves_mesh p s sender c.ihave topic
    have h2 : meshOf (controlIwants p s sender c) topic = meshOf s topic := by
      simp only [controlIwants]
      rw [handleIwants_mesh, h1]
    have h3 : meshOf (controlGrafts p s sender c) topic = meshOf s topic := by
      simp only [controlGrafts]
      rw [handleGrafts_mesh p (controlIwants p s sender c) sender c.graft topic
        (by rw [controlIwants_topics]; exact hsub)
        (by rw [h2]; exact hnot) (by rw [h2]; exact hover), h2]
    have h4 : meshOf (controlPrunes p s sender c) topic = meshOf s topic := by
      simp only [controlPrunes]
      rw [handlePrunes_mesh p (controlGrafts p s sender c) sender c.prune topic
        (by rw [h3]; exact hnot), h3]
    exact h4

private theorem handleControl_prune (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length)
    (hg : ∃ g ∈ c.graft, g.topicId = topic.name) :
    ∃ pr, Action.sendRpc sender pr ∈ controlActions p s sender c ∧ rpcPrunes pr topic := by
  have h2 : meshOf (controlIwants p s sender c) topic = meshOf s topic := by
    simp only [controlIwants, controlIhaves]
    rw [handleIwants_mesh, handleIhaves_mesh]
  have htop : (controlIwants p s sender c).topics = s.topics :=
    controlIwants_topics p s sender c
  obtain ⟨pr, hpr, hrpc⟩ :=
    handleGrafts_prune p (controlIwants p s sender c) sender c.graft topic
      (by rw [htop]; exact hsub) (by rw [h2]; exact hnot) (by rw [h2]; exact hover) hg
  refine ⟨pr, ?_, hrpc⟩
  simp only [controlActions]
  exact List.mem_append_left _ (List.mem_append_right _ hpr)

/-! ## The RPC pipeline lemmas -/

private theorem updateScoreOf_mesh (s : State) (q : Peer)
    (f : Score.PeerState → Score.PeerState) (topic : TopicId) :
    meshOf (updateScoreOf s q f) topic = meshOf s topic := by
  simp [updateScoreOf, mapPeers, meshOf]

private theorem updateScoreOf_topics (s : State) (q : Peer)
    (f : Score.PeerState → Score.PeerState) :
    (updateScoreOf s q f).topics = s.topics := by
  simp [updateScoreOf, mapPeers]

private theorem foldl_updateScoreOf_mesh (ms : List Message) (s : State) (sender : Peer)
    (f : Message → Score.PeerState → Score.PeerState) (topic : TopicId) :
    meshOf (ms.foldl (fun st m => updateScoreOf st sender (f m)) s) topic
      = meshOf s topic := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldl_cons, ih, updateScoreOf_mesh]

private theorem foldl_updateScoreOf_topics (ms : List Message) (s : State) (sender : Peer)
    (f : Message → Score.PeerState → Score.PeerState) :
    (ms.foldl (fun st m => updateScoreOf st sender (f m)) s).topics = s.topics := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldl_cons, ih, updateScoreOf_topics]

private theorem handleSubs_mesh (s : State) (sender : Peer) (subs : List Rpc.SubOpts)
    (topic : TopicId) : meshOf (handleSubs s sender subs) topic = meshOf s topic := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer, meshOf]

private theorem handleSubs_topics (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    (handleSubs s sender subs).topics = s.topics := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer]

private theorem recordOne_mesh (p : Params) (credit : Bool) (sender : Peer) (s : State)
    (m : Message) (topic : TopicId) :
    meshOf (recordOne p credit sender s m) topic = meshOf s topic := by
  unfold recordOne
  split
  · simp [meshOf]
  · split
    · rfl
    · dsimp only
      split
      · rw [updateScoreOf_mesh]; simp [meshOf]
      · simp [meshOf]

private theorem recordOne_topics (p : Params) (credit : Bool) (sender : Peer) (s : State)
    (m : Message) : (recordOne p credit sender s m).topics = s.topics := by
  unfold recordOne
  split
  · rfl
  · split
    · rfl
    · dsimp only
      split
      · rw [updateScoreOf_topics]
      · rfl

/-- The delivery record changes scores and the record, never a mesh. -/
private theorem recordDeliveries_mesh (p : Params) (credit : Bool) (sender : Peer)
    (ms : List Message) (s : State) (topic : TopicId) :
    meshOf (recordDeliveries p credit sender s ms) topic = meshOf s topic := by
  unfold recordDeliveries
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => rw [List.foldl_cons, ih, recordOne_mesh]

/-- The delivery record never changes the subscribed topics. -/
private theorem recordDeliveries_topics (p : Params) (credit : Bool) (sender : Peer)
    (ms : List Message) (s : State) :
    (recordDeliveries p credit sender s ms).topics = s.topics := by
  unfold recordDeliveries
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => rw [List.foldl_cons, ih, recordOne_topics]

private theorem handlePubs_mesh (p : Params) (s : State) (sender : Peer)
    (ms : List Message) (topic : TopicId) :
    meshOf (handlePubs p s sender ms).1 topic = meshOf s topic := by
  simp only [handlePubs]
  rw [recordDeliveries_mesh, foldl_updateScoreOf_mesh, foldl_updateScoreOf_mesh]
  simp [meshOf]

private theorem handlePubs_topics (p : Params) (s : State) (sender : Peer)
    (ms : List Message) : (handlePubs p s sender ms).1.topics = s.topics := by
  simp only [handlePubs]
  rw [recordDeliveries_topics, foldl_updateScoreOf_topics, foldl_updateScoreOf_topics]

/-- The record of a peer after the heartbeat mesh write. -/
theorem peerOf_settleMesh (p : Params) (s : State) (plans : List TopicPlan) (q : Peer) :
    peerOf (settleMesh p s plans) q =
      (peerOf s q).map (fun pd =>
        if scoreOf p s q < 0 then
          { pd with score := s.topics.foldl (fun sc t => Score.prune p.score sc s.now t) pd.score }
        else pd) := by
  simp only [peerOf, settleMesh]
  induction s.peers with
  | nil => simp [lookupPeer]
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, lookupPeer]
    by_cases h : q = a
    · subst h
      simp
    · simp [h, ih]

/-- The score of a peer after the heartbeat mesh write. -/
theorem scoreOf_settleMesh (p : Params) (s : State) (plans : List TopicPlan) (q : Peer) :
    scoreOf p (settleMesh p s plans) q =
      match peerOf s q with
      | some pd =>
          Score.score p.score
            (if scoreOf p s q < 0 then
              s.topics.foldl (fun sc t => Score.prune p.score sc s.now t) pd.score
            else pd.score) s.now
      | none => 0 := by
  unfold scoreOf
  rw [peerOf_settleMesh]
  cases h : peerOf s q with
  | none => simp
  | some pd =>
    by_cases hlt : Score.score p.score pd.score s.now < 0 <;>
      simp [scoreOf, settleMesh, h, hlt]

/-- The mesh of a topic after a heartbeat. -/
theorem meshOf_heartbeatNext (p : Params) (s : State) (now : Millis)
    (order : List Peer) (topic : TopicId) :
    meshOf (heartbeatNext p s now order) topic =
      match (heartbeatPlans p s now order).find? (fun pl => decide (topic = pl.topic)) with
      | some pl =>
          pl.kept.filter (fun q => decide (0 ≤ scoreOf p (planScored p s now order) q))
      | none => [] := by
  simp [heartbeatNext, settleMesh, meshOf, lookupTopic_map_plans]

/-! ## The score gate theorems -/

private theorem rpcHasIhave_pruneRpc (t : TopicId) (b : Millis) (px : List Rpc.PeerInfo) :
    ¬ rpcHasIhave (pruneRpc t b px) := by
  simp [rpcHasIhave, pruneRpc, controlRpc]

private theorem rpcHasIhave_graftRpc (t : TopicId) : ¬ rpcHasIhave (graftRpc t) := by
  simp [rpcHasIhave, graftRpc, controlRpc]

/-- A gossip target sits at or above the gossip threshold. -/
theorem gossipTargets_score (p : Params) (s : State) (order : List Peer) (t : TopicId)
    (q : Peer) (h : q ∈ gossipTargets p s order t) :
    p.thresholds.gossipThreshold ≤ scoreOf p s q := by
  have h' := List.mem_of_mem_take h
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.2.1.1.1

/-- A gossip target sits in neither the mesh nor the fanout of the topic. -/
theorem gossipTargets_off_mesh (p : Params) (s : State) (order : List Peer) (t : TopicId)
    (q : Peer) (h : q ∈ gossipTargets p s order t) :
    memB q (meshOf s t) = false ∧ memB q (fanoutOf s t) = false := by
  have h' := List.mem_of_mem_take h
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h'
  exact ⟨h'.2.1.1.2, h'.2.1.2⟩

/-- A gossip action targets a peer of the order at or above the gossip
threshold. -/
theorem mem_gossipActions (p : Params) (s : State) (order : List Peer)
    (to : Peer) (rpc : Rpc.RPC)
    (h : Action.sendRpc to rpc ∈ gossipActions p s order) :
    p.thresholds.gossipThreshold ≤ scoreOf p s to := by
  simp only [gossipActions, List.mem_flatMap, List.mem_append] at h
  obtain ⟨t, _, ht | ht⟩ := h
  · split at ht
    · simp at ht
    · simp only [List.mem_map, List.mem_filter] at ht
      obtain ⟨q, ⟨hq, _⟩, hqr⟩ := ht
      cases hqr
      exact gossipTargets_score p s order t _ hq
  · split at ht <;> simp at ht

/-- The partial-gossip offer of a heartbeat names only gossip targets that
requested partial messages on the topic (`partial-messages.md`, "Partial
Message Gossip"). With `gossipTargets_score` and `gossipTargets_off_mesh`,
the offer reaches none of these peers:

- a peer of the mesh or the fanout of the topic
- a peer below the gossip threshold
- a peer that takes full messages -/
theorem mem_partialGossip (p : Params) (s : State) (order : List Peer)
    (t : TopicId) (peers : List Peer) (q : Peer)
    (h : Action.partialGossip t peers ∈ gossipActions p s order) (hq : q ∈ peers) :
    q ∈ gossipTargets p s order t ∧ wantsPartial p s q t = true := by
  simp only [gossipActions, List.mem_flatMap, List.mem_append] at h
  obtain ⟨t', _, ht | ht⟩ := h
  · split at ht
    · simp at ht
    · simp only [List.mem_map] at ht
      obtain ⟨_, -, hqr⟩ := ht
      cases hqr
  · split at ht
    · simp at ht
    · simp only [List.mem_singleton, Action.partialGossip.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      simpa [List.mem_filter] using hq

private theorem ihaveRpc_topic {t t' : TopicId} {ids ids' : List MessageId}
    (h : ihaveRpc t' ids' = ihaveRpc t ids) : t' = t := by
  cases t
  cases t'
  simp [ihaveRpc, controlRpc] at h
  simp [h]

/-- No IHAVE of a heartbeat reaches a peer that takes partial messages on
the topic (`partial-messages.md`, "Partial Message Gossip"). -/
theorem gossipActions_no_ihave_partial (p : Params) (s : State) (order : List Peer)
    (to : Peer) (t : TopicId) (ids : List MessageId)
    (h : Action.sendRpc to (ihaveRpc t ids) ∈ gossipActions p s order) :
    wantsPartial p s to t = false := by
  simp only [gossipActions, List.mem_flatMap, List.mem_append] at h
  obtain ⟨t', _, ht | ht⟩ := h
  · split at ht
    · simp at ht
    · simp only [List.mem_map, List.mem_filter] at ht
      obtain ⟨q, ⟨_, hw⟩, hqr⟩ := ht
      simp only [Action.sendRpc.injEq] at hqr
      obtain ⟨rfl, hr⟩ := hqr
      have ht' : t' = t := ihaveRpc_topic hr
      subst ht'
      simpa using hw
  · split at ht <;> simp at ht

/-- The gossip state keeps the settled scores and replaces the cache, so
the score of a peer is the score after the heartbeat. -/
theorem scoreOf_gossipState (p : Params) (s : State) (now : Millis) (order : List Peer)
    (q : Peer) :
    scoreOf p (gossipState p s now order) q = scoreOf p (heartbeatNext p s now order) q := by
  simp [scoreOf, gossipState, peerOf, heartbeatNext]

theorem tickPruneNegative (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ topic peer, peer ∈ meshOf s' topic → 0 ≤ scoreOf p s' peer := by
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  intro topic peer hmem
  rw [meshOf_heartbeatNext] at hmem
  split at hmem
  · next pl hfind =>
    simp only [List.mem_filter] at hmem
    have hge : 0 ≤ scoreOf p (planScored p s now order) peer := of_decide_eq_true hmem.2
    have hscore : scoreOf p (heartbeatNext p s now order) peer
        = scoreOf p (planScored p s now order) peer := by
      simp only [heartbeatNext]
      rw [scoreOf_settleMesh]
      cases hpd : peerOf (planScored p s now order) peer with
      | none => simp [scoreOf, hpd]
      | some pd =>
        have hge' : 0 ≤ Score.score p.score pd.score (planScored p s now order).now := by
          simpa [scoreOf, hpd] using hge
        have hlt : ¬ Score.score p.score pd.score (planScored p s now order).now < 0 :=
          Int.not_lt_of_ge hge'
        simp [scoreOf, hpd, hlt]
    rw [hscore]
    exact hge
  · simp at hmem

/-- Every gossip action targets a peer at or above the gossip threshold
in the state after the heartbeat. The prune and graft actions fail the
ihave test. -/
theorem tickGossipGated (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ to rpc, Action.sendRpc to rpc ∈ acts → rpcHasIhave rpc →
      p.thresholds.gossipThreshold ≤ scoreOf p s' to := by
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  intro to rpc hmem hih
  simp only [heartbeatActions, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rcases hmem with hmem | hmem
    · simp only [planActionsOf, List.mem_flatMap] at hmem
      obtain ⟨pl, _, hpl⟩ := hmem
      simp only [planActions, List.mem_append, List.mem_map] at hpl
      rcases hpl with ⟨q, _, hq⟩ | ⟨q, _, hq⟩
      · cases hq
        exact absurd hih (rpcHasIhave_pruneRpc _ _ _)
      · cases hq
        exact absurd hih (rpcHasIhave_graftRpc _)
    · simp only [negativeActions, List.mem_flatMap, List.mem_map] at hmem
      obtain ⟨pl, _, q, _, hq⟩ := hmem
      cases hq
      exact absurd hih (rpcHasIhave_pruneRpc _ _ _)
  · rw [← scoreOf_gossipState]
    exact mem_gossipActions p (gossipState p s now order) order to rpc hmem

/-! ## The deduplication theorem -/

/-- Every accepted message was absent from the pre-state seen cache. -/
theorem accept_gate (c0 : Cache.SeenIndex) (now : Millis) (idf : Sign.MsgIdFn)
    (done : List MessageId) (c : Cache.SeenIndex) (ms : List Message) :
    ∀ m ∈ (accept c0 now idf done c ms).accepted, c0.contains (idf m) now = false := by
  induction ms generalizing done c with
  | nil => simp [accept]
  | cons m ms ih =>
    simp only [accept]
    split
    · exact ih done c
    · next hskip =>
      intro m' hm'
      rw [List.mem_cons] at hm'
      rcases hm' with hhead | hm'
      · rw [hhead]
        cases hc : c0.contains (idf m) now with
        | false => rfl
        | true => exact absurd (by rw [hc]; rfl) hskip
      · exact ih (idf m :: done) (c.add (idf m) now) m' hm'

private theorem forwardPubs_not_deliver (p : Params) (s : State) (sender : Peer)
    (ms : List Message) (m : Message) : Action.deliver m ∉ forwardPubs p s sender ms := by
  intro h
  simp only [forwardPubs, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, q, _, hq⟩ := h
  cases hq

/-- An inbound forward never goes back to the sender: neither the mesh
and explicit targets nor the floodsub targets name it. -/
theorem forwardPubs_excludes_sender (p : Params) (s : State) (sender : Peer)
    (ms : List Message) (rpc : Rpc.RPC) :
    Action.sendRpc sender rpc ∉ forwardPubs p s sender ms := by
  intro h
  simp only [forwardPubs, List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨_, _, q, hqmem, heq⟩
  injection heq with hpeer _
  subst hpeer
  rcases List.mem_append.1 hqmem with hq | hq
  · simp only [inboundTargets, List.mem_filter] at hq
    exact of_decide_eq_true hq.2 rfl
  · simp only [List.mem_filter, Bool.and_eq_true] at hq
    exact of_decide_eq_true hq.2.1 rfl

private theorem handleIhave_not_deliver (p : Params) (s : State) (sender : Peer)
    (i : Rpc.ControlIHave) (m : Message) :
    Action.deliver m ∉ (handleIhave p s sender i).2 := by
  simp only [handleIhave]
  split
  · simp
  · split <;> simp

private theorem handleIwant_not_deliver (p : Params) (s : State) (sender : Peer)
    (w : Rpc.ControlIWant) (m : Message) :
    Action.deliver m ∉ (handleIwant p s sender w).2 := by
  simp only [handleIwant]
  simp [List.mem_map]

private theorem handlePrune_not_deliver (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (m : Message) :
    Action.deliver m ∉ (handlePrune p s sender q).2 := by
  simp only [handlePrune]
  split
  · split <;> simp
  · simp

private theorem handleGraft_not_deliver (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (m : Message) :
    Action.deliver m ∉ (handleGraft p s sender g).2 := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · rw [handleGraft_member p s sender g hsub hm]
      simp
    · have hm' : memB sender (meshOf s ⟨g.topicId⟩) = false := by
        cases h' : memB sender (meshOf s ⟨g.topicId⟩) <;> simp_all
      by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · rw [handleGraft_backoff p s sender g hsub hm' hb]
        simp
      · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
          cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
        by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · rw [handleGraft_overfull p s sender g hsub hm' hb' hd]
          simp
        · by_cases he : memB sender s.explicit = true
          · rw [handleGraft_explicit p s sender g hsub hm' hb' hd he]
            simp
          · have he' : memB sender s.explicit = false := by
              cases h' : memB sender s.explicit <;> simp_all
            cases hpd : peerOf s sender with
            | none =>
                rw [handleGraft_add_none p s sender g hsub hm' hb' hd he' hpd]
                simp
            | some pd =>
                rw [handleGraft_add p s sender g pd hsub hm' hb' hd he' hpd]
                simp
  · have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = false := by
      cases h' : memB (⟨g.topicId⟩ : TopicId) s.topics <;> simp_all
    rw [handleGraft_unknown p s sender g hsub']
    simp

private theorem mapHandlers_not_deliver {β : Type} (f : State → β → State × List Action)
    (hf : ∀ (s : State) (b : β) (m : Message), Action.deliver m ∉ (f s b).2) :
    ∀ (bs : List β) (s : State) (m : Message), Action.deliver m ∉ (mapHandlers f bs s).2 := by
  intro bs
  induction bs with
  | nil =>
      intro s m
      simp [mapHandlers]
  | cons b bs ih =>
      intro s m
      simp only [mapHandlers, List.mem_append, not_or]
      exact ⟨hf s b m, ih (f s b).1 m⟩

private theorem controlActions_not_deliver (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) (m : Message) :
    Action.deliver m ∉ controlActions p s sender c := by
  intro h
  simp only [controlActions, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · rcases h with h | h
      · exact mapHandlers_not_deliver _ (fun s b => handleIhave_not_deliver p s sender b) _ _ _ h
      · exact mapHandlers_not_deliver _ (fun s b => handleIwant_not_deliver p s sender b) _ _ _ h
    · exact mapHandlers_not_deliver _ (fun s b => handleGraft_not_deliver p s sender b) _ _ _ h
  · exact mapHandlers_not_deliver _ (fun s b => handlePrune_not_deliver p s sender b) _ _ _ h

private theorem pxAccept_not_deliver (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) (m : Message) : Action.deliver m ∉ pxAccept p s sender c := by
  intro h
  simp only [pxAccept] at h
  split at h
  · simp only [List.mem_filterMap] at h
    obtain ⟨_, _, hq⟩ := h
    split at hq <;> simp at hq
  · simp at h

/-- A message reaches the application only when the pre-state seen cache
does not hold its id. -/
private theorem handleSubs_seen (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    (handleSubs s sender subs).seen = s.seen := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer]

private theorem handleSubs_now (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    (handleSubs s sender subs).now = s.now := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer]

private theorem join_not_deliver (p : Params) (s : State) (peer : Peer)
    (proto : PubsubProto) (m : Message) : Action.deliver m ∉ (join p s peer proto).2 := by
  simp [join]

private theorem leave_not_deliver (s : State) (peer : Peer) (m : Message) :
    Action.deliver m ∉ (leave s peer).2 := by
  simp [leave]

private theorem publishLocal_not_deliver (p : Params) (s : State) (msg : Message)
    (m : Message) : Action.deliver m ∉ (publishLocal p s msg).2 := by
  unfold publishLocal
  by_cases h : validationOk p msg
  · intro hm
    simp only [h, ↓reduceIte] at hm
    have hm' := mem_dropForPartial hm
    simp [List.mem_map] at hm'
  · simp [h]

private theorem subscribe_not_deliver (p : Params) (s : State) (topic : TopicId)
    (m : Message) : Action.deliver m ∉ (subscribe p s topic).2 := by
  simp only [subscribe]
  intro h
  rw [List.mem_map] at h
  obtain ⟨q, -, hq⟩ := h
  cases hq

private theorem unsubscribe_not_deliver (p : Params) (s : State) (topic : TopicId)
    (m : Message) : Action.deliver m ∉ (unsubscribe p s topic).2 := by
  simp only [unsubscribe]
  intro h
  rw [List.mem_map] at h
  obtain ⟨q, -, hq⟩ := h
  cases hq

private theorem planActions_not_deliver (p : Params) (s : State) (pl : TopicPlan) (m : Message) :
    Action.deliver m ∉ planActions p s pl := by
  simp [planActions, List.mem_map]

private theorem planActionsOf_not_deliver (p : Params) (s : State) (now : Millis)
    (order : List Peer) (m : Message) :
    Action.deliver m ∉ planActionsOf p s now order := by
  intro h
  simp only [planActionsOf, List.mem_flatMap] at h
  obtain ⟨pl, -, hp⟩ := h
  exact planActions_not_deliver p _ pl m hp

private theorem negativeActions_not_deliver (p : Params) (s : State) (now : Millis)
    (order : List Peer) (m : Message) :
    Action.deliver m ∉ negativeActions p s now order := by
  intro h
  simp only [negativeActions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨pl, -, q, -, hq⟩ := h
  cases hq

private theorem gossipActions_not_deliver (p : Params) (s : State) (order : List Peer)
    (m : Message) : Action.deliver m ∉ gossipActions p s order := by
  intro h
  simp only [gossipActions, List.mem_flatMap, List.mem_append] at h
  obtain ⟨t, -, ht | ht⟩ := h
  · split at ht
    · simp at ht
    · simp only [List.mem_map] at ht
      obtain ⟨q, -, hq⟩ := ht
      cases hq
  · split at ht <;> simp at ht

private theorem heartbeatActions_not_deliver (p : Params) (s : State) (now : Millis)
    (order : List Peer) (m : Message) :
    Action.deliver m ∉ heartbeatActions p s now order := by
  intro h
  simp only [heartbeatActions, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · exact planActionsOf_not_deliver p s now order m h
    · exact negativeActions_not_deliver p s now order m h
  · exact gossipActions_not_deliver p (gossipState p s now order) order m h

private theorem holdPubs_not_deliver (p : Params) (s : State) (sender : Peer)
    (ms : List Message) (m : Message) : Action.deliver m ∉ (holdPubs p s sender ms).2 := by
  intro h
  simp only [holdPubs, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with ⟨_, -, hq⟩ | ⟨_, -, _, -, hq⟩ <;> cases hq

private theorem handleValidated_not_deliver (p : Params) (s : State) (id : MessageId)
    (source : Peer) (outcome : Validation) (m : Message) :
    Action.deliver m ∉ (handleValidated p s id source outcome).2 := by
  intro h
  unfold handleValidated at h
  split at h
  · simp at h
  · cases outcome with
    | accept => exact forwardPubs_not_deliver p s _ _ m (mem_dropForPartial (mem_dropDontWant h))
    | reject => simp at h
    | ignore => simp at h

private theorem handlePartialIn_not_deliver (p : Params) (s : State) (sender : Peer)
    (o : Option Rpc.PartialMessage) (m : Message) :
    Action.deliver m ∉ (handlePartialIn p s sender o).2 := by
  cases o with
  | none => simp [handlePartialIn]
  | some pm =>
    simp only [handlePartialIn]
    (repeat' split) <;> simp

private theorem sendPartial_not_deliver (p : Params) (s : State) (q : Peer)
    (pm : Rpc.PartialMessage) (m : Message) : Action.deliver m ∉ sendPartial p s q pm := by
  unfold sendPartial
  by_cases h1 : (partialOpts p (partialTopic pm)).sends <;>
    by_cases h2 : (peerPartial s q (partialTopic pm)).requests <;>
    by_cases h3 : (peerPartial s q (partialTopic pm)).supports && pm.partsMetadata.isSome <;>
    simp_all

/-- A message reaches the application only when the pre-state seen cache
does not hold its id. Under `Params.validateMessages` no step delivers
at all: the application gets `Action.validate` instead. -/
theorem stepDeliverUnseen (p : Params) (s s' : State) (acts : List Action)
    (e : Event) (m : Message)
    (hstep : step p s e = .ok (s', acts)) (hdel : Action.deliver m ∈ acts) :
    Cache.SeenIndex.contains s.seen (p.msgId m) s.now = false := by
  cases e with
  | peerJoined peer proto =>
      have h1 : join p s peer proto = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (join p s peer proto).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (join_not_deliver p s peer proto m)
  | peerLeft peer =>
      have h1 : leave s peer = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (leave s peer).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (leave_not_deliver s peer m)
  | publish msg =>
      have h1 : publishLocal p s msg = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (publishLocal p s msg).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (publishLocal_not_deliver p s msg m)
  | subscribe topic =>
      have h1 : subscribe p s topic = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (subscribe p s topic).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (subscribe_not_deliver p s topic m)
  | unsubscribe topic =>
      have h1 : unsubscribe p s topic = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (unsubscribe p s topic).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (unsubscribe_not_deliver p s topic m)
  | tick now order =>
      by_cases hdue : heartbeatDue p s now
      · have h1 : heartbeat p s now order = (s', acts) := by
          simpa only [step, ite_eq_left hdue, Except.ok.injEq] using hstep
        have hacts : acts = (heartbeat p s now order).2 := by rw [h1]
        simp only [heartbeat] at hacts
        rw [hacts] at hdel
        exact absurd hdel (heartbeatActions_not_deliver p s now order m)
      · have h1 : (s, ([] : List Action)) = (s', acts) := by
          simpa only [step, ite_eq_right hdue, Except.ok.injEq] using hstep
        have hacts : acts = [] := by
          have hs := congrArg Prod.snd h1
          simpa using hs
        rw [hacts] at hdel
        simp at hdel
  | validated id source outcome =>
      have h1 : handleValidated p s id source outcome = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (handleValidated p s id source outcome).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (handleValidated_not_deliver p s id source outcome m)
  | peerInfo peer outbound ip =>
      -- The step only records the peer's facts. It emits no action.
      simp only [step] at hstep
      split at hstep <;>
        (simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
         obtain ⟨-, rfl⟩ := hstep
         simp at hdel)
  | appScore peer score =>
      simp only [step, Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      simp at hdel
  | sendPartial peer msg =>
      simp only [step, Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact absurd hdel (sendPartial_not_deliver p s peer msg m)
  | partialJudged peer topic valid =>
      simp only [step, Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      simp at hdel
  | protocol peer proto =>
      simp only [step, Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      simp at hdel
  | rpc sender bytes =>
      simp only [step, rpcStep] at hstep
      split at hstep
      · have h1 : (s, ([] : List Action)) = (s', acts) := by
          simpa only [Except.ok.injEq] using hstep
        have hacts : acts = [] := by
          have hs := congrArg Prod.snd h1
          simpa using hs
        rw [hacts] at hdel
        simp at hdel
      · split at hstep
        · have h1 : (s, ([] : List Action)) = (s', acts) := by
            simpa only [Except.ok.injEq] using hstep
          have hacts : acts = [] := by
            have hs := congrArg Prod.snd h1
            simpa using hs
          rw [hacts] at hdel
          simp at hdel
        · split at hstep
          · cases hstep
          · next rpc hdec =>
            have h1 : handleRpc p s sender rpc = (s', acts) := by
              simpa only [Except.ok.injEq] using hstep
            have hacts : acts = (handleRpc p s sender rpc).2 := by rw [h1]
            rw [hacts] at hdel
            simp only [handleRpc, List.mem_append] at hdel
            rcases hdel with (hdel | hdel) | hdel
            · split at hdel
              · exact absurd hdel (holdPubs_not_deliver p _ sender rpc.publish m)
              simp only [handlePubs, List.mem_append] at hdel
              rcases hdel with hdl | hdl
              · simp only [List.mem_map] at hdl
                obtain ⟨m', hm', heq⟩ := hdl
                have hseen : (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).seen = s.seen :=
                  handleSubs_seen s sender (admitSubs p s sender rpc.subscriptions)
                have hnow : (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).now = s.now :=
                  handleSubs_now s sender (admitSubs p s sender rpc.subscriptions)
                cases heq
                have hgate := accept_gate (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).seen
                  (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).now p.msgId []
                  (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).seen
                  (List.filter (fun m => validationOk p m) rpc.publish) m hm'
                rwa [hseen, hnow] at hgate
              · exact absurd (mem_dropForPartial hdl)
                  (forwardPubs_not_deliver p (handleSubs s sender (admitSubs p s sender rpc.subscriptions)) sender
                    ((accept (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).seen
                        (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).now p.msgId []
                        (handleSubs s sender (admitSubs p s sender rpc.subscriptions)).seen
                        (List.filter (fun m => validationOk p m) rpc.publish)).accepted) m)
            · cases hctl : rpc.control with
              | none =>
                  rw [hctl] at hdel
                  simp [handleControl] at hdel
              | some c =>
                  rw [hctl] at hdel
                  simp only [handleControl, runControl_eq, List.mem_append] at hdel
                  rcases hdel with hdel | hdel
                  · exact absurd hdel (controlActions_not_deliver p _ sender _ m)
                  · exact absurd hdel (pxAccept_not_deliver p _ sender _ m)
            · exact absurd hdel (handlePartialIn_not_deliver p _ sender rpc.partialRpc m)

/-! ## The backoff theorem -/

private theorem rpcGrafts_graftRpc (t t' : TopicId) (h : rpcGrafts (graftRpc t) t') : t' = t := by
  simp only [rpcGrafts, graftRpc, controlRpc, List.mem_cons, List.mem_nil_iff, or_false] at h
  obtain ⟨g, hg, hgt⟩ := h
  subst hg
  obtain ⟨tn⟩ := t
  obtain ⟨t'n⟩ := t'
  simpa using hgt.symm

private theorem rpcGrafts_pruneRpc (t t' : TopicId) (b : Millis) (px : List Rpc.PeerInfo) :
    ¬ rpcGrafts (pruneRpc t b px) t' := by
  simp [rpcGrafts, pruneRpc, controlRpc]

private theorem rpcGrafts_ihaveRpc (t t' : TopicId) (ids : List MessageId) :
    ¬ rpcGrafts (ihaveRpc t ids) t' := by
  simp [rpcGrafts, ihaveRpc, controlRpc]

private theorem freshState_backoff (p : Params) (s : State) (now : Millis) :
    (freshState p s now).backoff = Cache.Backoff.clear s.backoff now := by
  simp [freshState]

private theorem planTopic_added_backoff (p : Params) (s : State) (now : Millis)
    (order : List Peer) (topic : TopicId) {q : Peer}
    (h : q ∈ (planTopic p s now order topic).added) :
    Cache.Backoff.active s.backoff q topic now = false := by
  simp only [planTopic] at h
  -- `added` is a pick of the candidates (`mem_pickAdded`).
  have hc : q ∈ order.filter (fun q =>
      !memB q (meshOf s topic) && !(Cache.Backoff.active s.backoff q topic now) &&
        (peerOf s q).isSome && decide (0 ≤ scoreOf p s q) && !memB q s.explicit &&
          !isFlood s q) :=
    mem_pickAdded h
  cases hb : Cache.Backoff.active s.backoff q topic now with
  | false => rfl
  | true =>
      exfalso
      simp only [List.mem_filter] at hc
      rw [hb] at hc
      simp at hc

/-- The heartbeat never grafts a peer whose backoff is active. -/
theorem tickNoBackoffGraft (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ to rpc topic, Action.sendRpc to rpc ∈ acts → rpcGrafts rpc topic →
      Cache.Backoff.active s.backoff to topic now = false := by
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  intro to rpc topic hmem hgraft
  simp only [heartbeatActions, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rcases hmem with hmem | hmem
    · simp only [planActionsOf, List.mem_flatMap] at hmem
      obtain ⟨pl, hpl, hmem⟩ := hmem
      simp only [planActions, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨q, hq, hqeq⟩ | ⟨q, hq, hqeq⟩
      · cases hqeq
        exact absurd hgraft (rpcGrafts_pruneRpc _ _ _ _)
      · cases hqeq
        have htopic : topic = pl.topic := rpcGrafts_graftRpc pl.topic topic hgraft
        subst htopic
        have hpl' : pl ∈ (freshState p s now).mesh.map
            (fun e => planTopic p (freshState p s now) now order e.1) := by
          simpa [heartbeatPlans, planList] using hpl
        simp only [List.mem_map] at hpl'
        obtain ⟨e, -, rfl⟩ := hpl'
        have hb := planTopic_added_backoff p (freshState p s now) now order e.1 hq
        change Cache.Backoff.active s.backoff to e.1 now = false
        cases hcase : Cache.Backoff.active s.backoff to e.1 now with
        | false => rfl
        | true =>
            exfalso
            have hclear := Cache.clear_keeps_active s.backoff to e.1 now hcase
            rw [← freshState_backoff p s now] at hclear
            rw [hb] at hclear
            simp at hclear
    · simp only [negativeActions, List.mem_flatMap, List.mem_map] at hmem
      obtain ⟨pl, -, q, -, hqeq⟩ := hmem
      cases hqeq
      exact absurd hgraft (rpcGrafts_pruneRpc _ _ _ _)
  · simp only [gossipActions, List.mem_flatMap, List.mem_append] at hmem
    obtain ⟨t, -, ht | ht⟩ := hmem
    · split at ht
      · simp at ht
      · simp only [List.mem_map] at ht
        obtain ⟨q, -, hqeq⟩ := ht
        cases hqeq
        exact absurd hgraft (rpcGrafts_ihaveRpc _ _ _)
    · split at ht <;> simp at ht

/-! ## The peer exchange and floodsub theorems -/

/-- With `doPX` off, no prune names a peer. -/
theorem pxPeersOff (p : Params) (s : State) (target : Peer) (topic : TopicId)
    (h : p.doPX = false) : pxPeers p s target topic = [] := by
  simp [pxPeers, h]

/-- A prune names at most `prunePeers` peers. -/
theorem pxPeersLength (p : Params) (s : State) (target : Peer) (topic : TopicId) :
    (pxPeers p s target topic).length ≤ p.prunePeers := by
  unfold pxPeers
  split
  · simp only [List.length_map]
    exact List.length_take_le _ _
  · simp

/-- A target below score 0 gets no peer exchange (`gossipsub-v1.1.md`:
"no PX information is emitted towards those peers"). -/
theorem pxPeersNegative (p : Params) (s : State) (target : Peer) (topic : TopicId)
    (h : scoreOf p s target < 0) : pxPeers p s target topic = [] := by
  have hn : ¬ (0 ≤ scoreOf p s target) := Int.not_le.2 h
  simp [pxPeers, hn]

/-- A sender below `acceptPXThreshold` gets no connect action. -/
theorem pxAcceptGate (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage)
    (h : scoreOf p s sender < p.thresholds.acceptPXThreshold) :
    pxAccept p s sender c = [] := by
  have hn : ¬ (p.thresholds.acceptPXThreshold ≤ scoreOf p s sender) := Int.not_le.2 h
  simp [pxAccept, hn]

/-- A heartbeat grafts no floodsub peer: the candidates of a plan exclude
them. -/
theorem planTopicAddedNotFlood (p : Params) (s : State) (now : Millis) (order : List Peer)
    (topic : TopicId) {q : Peer} (h : q ∈ (planTopic p s now order topic).added) :
    isFlood s q = false := by
  simp only [planTopic] at h
  have hc := mem_pickAdded h
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hc
  exact hc.2.2

end Libp2p.Protocols.Gossipsub.Core
