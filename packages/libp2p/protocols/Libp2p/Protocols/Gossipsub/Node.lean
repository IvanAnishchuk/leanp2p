import Conc
import Streams
import Bytes
import Libp2p.Protocols.Constants
import Libp2p.Core
import Libp2p.Protocols.StreamError
import Libp2p.Protocols.Gossipsub.HostSeam
import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Protocols.Gossipsub.Payload

/-!
# Gossipsub node: the loop over the router core

The core of this unit is the pure `Core.step`. This module holds the one
task that drives it, and the publish and subscribe surface at the seam
level (ARCHITECTURE, "Modules"; root ARCHITECTURE §3.3).

## The loop

One task owns the router state. A bounded channel carries application and
host events and the wakes of Conc.Alarm. The alarm has its own task. The
loop uses repeat and parks only on the channel receive. Ready events use
constant stack space. The loop asks the alarm for the next due time after
each input. A TestClock drives the alarm in tests.

The inbound reader uses repeat with a mutable header, body cursor and chunk
position. Each bounded body allocation follows its decoded length. Each
input byte enters the body once, so small reads use constant stack space
and linear copying.

## Ownership

The task set of the node owns the loop, alarm, writer and connector tasks.
Stop joins them. The host owns the handler tasks of the inbound streams.
Nothing cancels a task: `stop` closes the two input queues, and the close
wakes the parked loop. It also closes the peer-exchange queue, which wakes the
parked connectors. A connector inside a dial ends with the dial. The
router state and pending gossip are local to the loop. Shared registries,
subscriptions and the closing flag change through OnceRef.update or
updateGet (root ARCHITECTURE §4.1). Only the first stop caller joins.

## Recorded decisions

- **The stop field runs in Async.** Joining parks, and TaskSet.joinAll runs
  in Async for that reason. So the field keeps that type and leaves the
  blocking run to the application edge.
- **Actions never park.** Each send offers a frame to a peer queue with 32
  slots. One writer task owns that peer's stream. A full queue drops the
  frame, as go does for a full peer queue. Node.dropped reports these drops.
  Actions return the next pending list, and the loop assigns that answer.
- **Delayed gossip has a bound.** At most 256 sends wait in the pending list.
  Overflow drops the newest excess sends and adds to Node.dropped. Due sends
  leave before the tick shifts the message cache. The delay index increases
  across the run. Config.order hashes the heartbeat count with peer bytes.
- **Subscribe registers its callback before the post.** The loop can serve a
  delivery between the post and the registration, and that delivery would
  miss the callback. A refused post takes back its own registration by id.
  Concurrent callers remove their own entries through atomic updates.
- **The handler announces its opener.** It posts peerJoined before reading
  frames, so the first RPC reaches a known peer. Repeat joins are no-ops.
- **No signer.** The core validates with `strictNoSign` (`Core.validationOk`),
  which requires `from` and `seqno` to be absent. So `publish` signs nothing
  and never writes the peer id of the node.
- **A local publish delivers nothing locally.** `Core.publishLocal` emits no
  deliver action, because the application already holds its own message.
  The callback of the publisher stays silent.
- **The loop announces a subscription change.** `Core.join` sends the topics
  only when a peer joins. The core emits nothing for a subscribe after the
  join, so that peer would never learn the topic. The go implementation
  announces a change in its host registry, outside the router. The loop
  does the same with subOptRpc, before the core step.
- **The default gossip delay is zero.** The pinned go router enqueues IHAVEs
  in emitGossip (gossipsub.go, lines 2007 to 2076). Its flush sends them at
  once (lines 2078 to 2092). The random sleep in announceRetry belongs to a
  subscription retry (pubsub.go, lines 1234 to 1235). The loop owns the
  emission schedule, so a caller can spread heartbeat gossip across the
  interval. The default spreads nothing and matches go. Tests configure an
  explicit spread because issue #23 names the trickle regressions. The delay
  applies only to heartbeat IHAVEs. Publish, forward, graft and hello sends
  leave at once.
- **Each peer has one writer task.** The pinned go pubsub version a01777894f4c
  resets duplicate inbound streams (comm.go, lines 55 to 65). Its sender uses
  one stream and a bounded queue per peer (lines 181 to 233). Our writer
  writes frames in queue order. A failed write retires its outbound entry
  and closes its queue. Transport notifications own peerLeft. Stop resets
  installed streams to wake parked writes and joins
  the writer tasks. The host must end a newStream call when its session ends.
- **The inbound handler serves every frame of a stream.** The pubsub spec
  uses separate long-lived inbound and outbound streams (pubsub/README.md,
  lines 78 to 83). Go reads messages in a loop (comm.go, lines 75 to 120).
  Rust keeps one inbound substream (protocols/gossipsub/src/handler.rs,
  lines 78 to 82). Both peers write many RPCs on one stream. The handler
  preserves frame order and checks each length before appending body bytes.
  A bad prefix, an over-cap frame or EOF inside a frame is a protocol error.
  A zero-length frame is legal (Rpc.lean, line 867). Go skips it; this handler
  decodes it as an empty RPC that the core accepts.
- **The receipt observer runs before the core step.** The interop harness
  logs every received message, including duplicates (gossipsub-interop,
  test-specs/implementation.md, lines 71 to 78). Its go participant logs
  messages on RECV_RPC (go-libp2p/tracer.go, lines 75 to 88). Core.handlePubs
  deduplicates before delivery (Core.lean, lines 603 and 614). Config.onRpc
  exposes the sender and unframed body before that step. The observer can
  decode the body to log every message. The default hook decodes nothing.
  Frame errors fail the handler before they reach the observer.
- **A send failure retires its outbound entry.** The next send starts a fresh
  writer and stream. The core keeps the peer and accepts further RPCs on its
  live inbound stream. Retirement checks the writer id, so an old writer
  cannot remove a newer entry for the same peer.
- **The shell holds the signed peer records.** The core names the
  peer-exchange peers by id (`Core.pxPeers`). The send path adds each
  record that the host holds (`fillRecords`), so the core stays free of
  signatures and IO. For an inbound PX, `pxConnect` checks each record
  through the host. Then it queues the peer for one of
  `Config.connectors` dial tasks, in a queue of
  `Config.maxPendingConnections`. go-libp2p-pubsub splits the work in
  the same way (`pxConnect`, `connector`).
- **The node marks a floodsub peer after its join.** The host announces
  a connection before any stream negotiates, so the join records
  `meshsub`. The stream that negotiates `/floodsub/1.0.0`, ours or the
  peer's, then posts `Core.Event.protocol`. The router removes the peer
  from every mesh.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Node


/-- A spread a caller may choose for heartbeat gossip. Each delay stays below
one second. The multiplier is prime, so the delays do not repeat with a short
period. Config.trickle defaults to zero. A caller who needs gossip inside
each heartbeat interval sets heartbeatInterval above the largest delay. -/
def spread (i : Nat) : Millis := (i * 7919 + 1) % 1000

/-- Replayable peer order for a heartbeat. The hash combines its counter
with each peer's identity bytes. The loop supplies only known peers. -/
def defaultOrder (tick : Nat) (peers : List Peer) : List Peer :=
  let key (peer : Peer) : UInt64 := mixHash (hash tick) (hash (Bytes.toNatList peer.toBytes))
  peers.mergeSort (fun a b => key a ≤ key b)

/-- The configuration of one node: the router parameters, the clock the
loop reads, and the spread of the heartbeat gossip. -/
structure Config where
  /-- The router parameters. -/
  params : Core.Params := Core.defaults
  /-- The clock of the loop's timer. -/
  clock : Conc.Clock := Conc.Clock.system
  /-- The delay of the run-wide `i`-th delayed gossip send, in milliseconds.
  The caller fixes it, so a test gets exact times. -/
  trickle : Nat → Millis := fun _ => 0
  /-- Replayable peer order for the numbered heartbeat. -/
  order : Nat → List Peer → List Peer := defaultOrder
  /-- Called for every inbound RPC with its sender and its bytes, before the
  core sees them. A harness reads it to log each received message, including
  a duplicate. It runs on the loop task, so it must not park. -/
  onRpc : Peer → List Nat → BaseIO Unit := fun _ _ => pure ()
  /-- Called for every outbound RPC before it enters the peer queue. -/
  onSend : Peer → Rpc.RPC → BaseIO Unit := fun _ _ => pure ()
  /-- Called for each held message under `params.validateMessages`, with
  its id and its propagation source. It runs on the loop task, so it
  must not park: the application queues the work and answers later
  through `Node.report`. -/
  onValidate : Message → MessageId → Peer → BaseIO Unit := fun _ _ _ => pure ()
  /-- The cap on one encoded RPC, in and out. The default is go's 1 MiB
  (`Constants.rpcCap`), which the interop gate runs at. A consensus node
  sets `Constants.gossipMaxMessageSize` (phase0 "Maximum message
  sizes"). -/
  maxRpcSize : Nat := Constants.rpcCap
  /-- The explicit peers (`gossipsub-v1.1.md`, "Explicit Peering
  Agreements"). The node dials them at start and at every
  `explicitCheckMs`, and the router forwards every valid message to
  them and never meshes them. Their addresses come from the host's
  peerstore. -/
  explicitPeers : List Peer := []
  /-- "The recommended period for connectivity checks is 5 minutes." -/
  explicitCheckMs : Millis := 300000
  /-- The `ByteArray` payload path (`Gossipsub.Payload`): the message id
  of a payload on a topic. When set, the node keeps every payload as a
  `ByteArray` and the core sees only its id, so a block-sized message
  never becomes a `List Nat`. The node then sets `params.msgId` to read
  the handle, and checks `params.maxDataSize` itself. It drops an RPC
  with an oversize payload whole, with no P₄ penalty. `onValidate` gets
  the message with its handle in `data`, and `Node.payload` reads the
  bytes. A `none` id is a local fault, for example of a hash shim. The
  node then drops the inbound RPC whole, and `publish` answers `false`. -/
  payloadId : Option (String → ByteArray → Option MessageId) := none
  /-- The heartbeats between opportunistic grafting rounds. rust's
  `opportunistic_graft_ticks` is 60. -/
  opportunisticGraftTicks : Nat := 60
  /-- Called for each partial message a peer sends on a topic where
  `params.partialTopics` can send them, mesh peer or not
  (`partial-messages.md`, "Application-Library Interface"). It runs on
  the loop task, so it must not park. The application answers through
  `Node.sendPartial`, and scores the parts through `Node.judgePartial`. -/
  onPartial : Peer → Rpc.PartialMessage → BaseIO Unit := fun _ _ => pure ()
  /-- Called at each heartbeat with the gossip targets of a topic that
  requested partial messages, in place of their IHAVE
  (`partial-messages.md`, "Partial Message Gossip"). The application
  offers the groups it holds through `Node.sendPartial`, as go's
  `OnEmitGossip` does. It runs on the loop task, so it must not park.
  `Node.sendPartial` only queues, so the callback can call it. -/
  onPartialGossip : TopicId → List Peer → BaseIO Unit := fun _ _ => pure ()
  /-- Serve and speak `/floodsub/1.0.0` (pubsub `README.md`): the
  handler takes floodsub streams, and our writer proposes floodsub last.
  go-libp2p-pubsub and Lodestar speak it. rust-libp2p, and so
  Lighthouse, disable it by default, and so does this node. -/
  floodsub : Bool := false
  /-- The dials a peer exchange may queue: go's `MaxPendingConnections`,
  128. A full queue drops the peer, as go's `pxConnect` does. -/
  maxPendingConnections : Nat := 128
  /-- The tasks that dial peer-exchange peers: go's `Connectors`, 8. -/
  connectors : Nat := 8

/-- A snapshot of the router for metrics: the sizes a client exports.
Lighthouse's `lighthouse_network` metrics are off in the shadow node
(`node.rs:107`), so a poll is the whole interface. -/
structure Stats where
  /-- The known peers. -/
  peers : Nat
  /-- The mesh size of each topic. -/
  mesh : List (TopicId × Nat)
  /-- The subscribed topics. -/
  topics : Nat
  /-- The ids in the seen cache. -/
  seen : Nat
  /-- The messages in the message cache. -/
  cached : Nat
  /-- The messages that wait for the application's answer. -/
  pending : Nat
  /-- The IDONTWANT pairs held. -/
  dontSend : Nat
  /-- Frames dropped by a full or closed peer queue, or by the pending
  gossip bound (`Node.dropped`). -/
  dropped : Nat
  /-- The peers known to speak `/meshsub/1.2.0`. -/
  v12Peers : Nat
  /-- The peers known to speak `/meshsub/1.3.0`. -/
  v13Peers : Nat

/-- A running node. Every field is a seam over the loop task, which is the
only owner of the router state. -/
structure Node where
  /-- Publish the payload on the topic. `false` when the queue of the loop
  is full, the node stopped, or the payload is over `maxDataSize`. -/
  publish : TopicId → ByteArray → BaseIO Bool
  /-- Register a delivery callback. The callback runs on the loop task, so
  it must not park. `false` under the same conditions as `publish`, and the
  callback then stays unregistered. -/
  subscribe : TopicId → (Message → BaseIO Unit) → BaseIO Bool
  /-- `subscribe` with a post that parks while the control queue is full,
  so a burst of subscriptions loses none. A consensus node subscribes to
  about 200 topics at once, and the queue holds `inputSlots`. The loop's
  next take wakes the post, and the close of the queue at `stop` wakes it
  too. `false` once the node stops, and the callback then stays
  unregistered. -/
  subscribeWait : TopicId → (Message → BaseIO Unit) → Conc.Async Bool
  /-- Drop every callback of the topic, and leave the topic. A consensus
  node leaves about 200 topics at once after a fork, so the post parks
  while the control queue is full, as `subscribeWait` does. `false` once
  the node stops. -/
  unsubscribe : TopicId → Conc.Async Bool
  /-- Tell the loop that a peer joined. The connection notifiee of the host
  is the caller at integration. -/
  peerJoined : Peer → Core.PubsubProto → BaseIO Bool
  /-- Tell the loop that a peer left. -/
  peerLeft : Peer → BaseIO Bool
  /-- Answer a held message (`Config.onValidate`): accept forwards it,
  reject drops it and scores the source, ignore drops it. `false` under
  the same conditions as `publish`. -/
  report : MessageId → Peer → Core.Validation → BaseIO Bool
  /-- The score of every known peer, in `scoreScale` units, as the loop
  sees it now. Lighthouse's peer manager reads these every decay
  interval (`peerdb.rs`, `update_gossipsub_scores`). `none` when the
  node stopped or its queue is full. -/
  scores : Conc.Async (Option (List (Peer × Score)))
  /-- Replace the score parameters of one topic, as Lighthouse does by
  validator count and slot (`service/mod.rs`,
  `update_gossipsub_parameters`). Lighthouse replaces 66 topics at once,
  more than the control queue holds, so the post parks while the queue
  is full, as `subscribeWait` does. `false` once the node stops. -/
  setTopicParams : TopicId → Option Score.TopicParams → Conc.Async Bool
  /-- Set a peer's application score, P₅. `false` under the same
  conditions as `publish`. -/
  setAppScore : Peer → Int → BaseIO Bool
  /-- A snapshot of the router (`Stats`). `none` when the node stopped
  or its queue is full. -/
  stats : Conc.Async (Option Stats)
  /-- The payload of a message id on the `ByteArray` path
  (`Config.payloadId`). The answer is `none` off that path, and once the
  payload expired with the message cache. -/
  payload : MessageId → BaseIO (Option ByteArray)
  /-- Send a partial message to a peer. The router sends the whole
  message to a peer that requested partial messages on the topic, the
  metadata alone to a peer that only supports them, and nothing to any
  other peer. `false` under the same conditions as `publish`. -/
  sendPartial : Peer → Rpc.PartialMessage → BaseIO Bool
  /-- Score the parts a peer sent on a topic: `true` for novel valid
  data (a first delivery), `false` for bad data (an invalid delivery).
  `false` under the same conditions as `publish`. -/
  judgePartial : Peer → TopicId → Bool → BaseIO Bool
  /-- The peers to offer partial messages on a topic, each with its
  request flag. They are the peers that can take partial messages: of
  the mesh for a subscribed topic, or of the fanout for another topic.
  `none` when the node stopped or its queue is full. -/
  partialPeers : TopicId → Conc.Async (Option (List (Peer × Bool)))
  /-- Close the two input queues and join the loop task. The loop serves
  the queued inputs first, and drops the gossip that waits for its time. This
  field runs in `Async` because a join parks, and a parked `BaseIO` action would
  hold a thread. A second call does nothing. -/
  stop : Conc.Async Unit
  /-- Frames dropped by a full or closed peer queue, or by the 256-send
  pending-gossip bound. -/
  dropped : BaseIO Nat

/-! ## One outbound RPC -/

/-- True when the control message of the RPC holds an IHAVE. The loop
delays these sends. `Core.rpcHasIhave` is a `Prop`, and the loop needs a `Bool`. -/
def hasIhave (r : Rpc.RPC) : Bool :=
  match r.control with
  | some c => !c.ihave.isEmpty
  | none => false

/-- One subscription record: `true` subscribes, and `false` unsubscribes.
`Core.helloRpc` holds only positive records, so the loop builds this record
beside the code that sends it. A subscribe carries our partial-messages
choice for the topic (`Core.subOpts`). -/
def subOptRpc (p : Core.Params) (t : TopicId) (on : Bool) : Rpc.RPC :=
  { subscriptions := [Core.subOpts p t on], publish := [], control := none }

/-- An input of the loop: a core event, an alarm wake, a read of the
router, or a replacement of topic parameters. Inbound RPCs reach the loop
on one queue. Every other input reaches it on a second queue
(`nextInput`). -/
inductive Input where
  | event (e : Core.Event)
  | wake (now : Millis)
  /-- Read the router: the loop calls `k` with its parameters and state.
  `k` must not park. -/
  | inspect (k : Core.Params → Core.State → BaseIO Unit)
  /-- Replace the score parameters of one topic. With `none`, the router
  stops the scoring of the topic. -/
  | setTopicParams (topic : TopicId) (tp : Option Score.TopicParams)

/-- One peer's bounded writer queue and its currently open stream. -/
structure Outbound where
  /-- The writer generation used for exact retirement. -/
  id : Nat
  /-- At most 32 encoded frames wait for this peer. -/
  queue : Conc.Chan ByteArray
  /-- Stop resets this stream to wake a parked write. -/
  stream : Conc.OnceRef (Option Streams.Stream)

/-- Close a queue and reset its stream to wake its writer. -/
private def endOutbound (ob : Outbound) : Conc.Async Unit := do
  (ob.queue.close : BaseIO Unit)
  if let some stream ← (ob.stream.get : BaseIO (Option Streams.Stream)) then
    stream.reset

/-- One writer owns the peer stream. It writes queued frames in order and
closes the stream at the end. A failed open or write retires only this writer
entry and closes its queue. The core peer stays connected. Stop resets an
installed stream; a late open checks closing too. -/
private def writer (host : HostSeam) (closing : Conc.OnceRef Bool)
    (outbound : Conc.OnceRef (List (Peer × Outbound))) (unsupported : Conc.OnceRef (List Peer))
    (onVersion : Peer → Libp2p.Core.ProtocolId → BaseIO Unit) (floodsub : Bool)
    (peer : Peer) (ob : Outbound) : Conc.Async Unit := do
  let fail : Conc.Async Unit := do
    (ob.queue.close : BaseIO Unit)
    (outbound.update (fun table => table.filter (fun e => e.2.id != ob.id)) : BaseIO Unit)
    if let some stream ← (ob.stream.get : BaseIO (Option Streams.Stream)) then stream.reset
  try
    -- The newest first: a peer answers `na` to an id it lacks, and the
    -- negotiation tries v1.2, then v1.1, then floodsub when the node
    -- speaks it (go's `GossipSubDefaultProtocols` order).
    let ids := [Constants.meshsubV13Id, Constants.meshsubV12Id, Constants.meshsubId] ++
      (if floodsub then [Constants.floodsubId] else [])
    match ← host.newStream peer ids with
    | .ok (id, stream) =>
      (onVersion peer id : BaseIO Unit)
      (ob.stream.set (some stream) : BaseIO Unit)
      if ← (closing.get : BaseIO Bool) then stream.reset
      repeat
        match ← ob.queue.recv with
        | none => break
        | some frame =>
          if let .error _ ← stream.write frame then
            fail
            break
      stream.close
    | .error (.protocol _) =>
      -- The peer speaks no meshsub: the next reconcile drops it from the
      -- router, as go-libp2p-pubsub drops a peer whose stream fails to
      -- negotiate.
      (unsupported.update fun l => if l.contains peer then l else peer :: l : BaseIO Unit)
      fail
    | .error _ => fail
  catch _ => fail

/-! ## The inbound handler -/

/-- Read consecutive frames with a bounded header and one body allocation.
The header is at most Varint.maxBytes bytes. Its decoded length is capped
before emptyWithCapacity allocates the body. This is the pinned Lean name
for the capacity constructor. Each copySlice writes only the next slice at
cursor, without retaining an earlier body value. EOF between frames is clean.
The repeat loop uses constant stack space for any number of chunks or frames. -/
private def readFrames (events : Conc.Chan Input) (cap : Nat)
    (split : ByteArray → BaseIO (Option ByteArray)) (peer : Peer)
    (stream : Streams.Stream) : Conc.Async (Except Libp2p.Core.Error Unit) := do
  let mut header := ByteArray.emptyWithCapacity Varint.maxBytes
  let mut body := ByteArray.empty
  let mut expected : Option Nat := none
  let mut cursor := 0
  let mut chunk := ByteArray.empty
  let mut pos := 0
  repeat
    if let some size := expected then
      if cursor = size then
        -- On the payload path, the core gets the RPC with handles. The
        -- reader drops an RPC that the split refuses.
        if let some small ← (split body : BaseIO (Option ByteArray)) then
          -- Park: the loop frees a slot, or stop closes the event queue.
          if let .error _ ← events.send (.event (.rpc peer (Bytes.toNatList small))) then
            return .ok ()
        body := ByteArray.empty
        expected := none
        cursor := 0
    if pos = chunk.size then
      -- Park: the peer writes, half-closes, or resets.
      match ← stream.read with
      | .error e => return .error (mapStreamError e)
      | .ok none =>
        return if header.isEmpty && expected.isNone then .ok ()
          else .error (.protocol "the stream ended inside an RPC frame")
      | .ok (some bytes) =>
        chunk := bytes
        pos := 0
    else
      match expected with
      | some size =>
        let count := Nat.min (size - cursor) (chunk.size - pos)
        body := chunk.copySlice pos body cursor count
        cursor := cursor + count
        pos := pos + count
      | none =>
        if Varint.maxBytes ≤ header.size then
          return .error (.protocol "the RPC header is malformed")
        header := header.push (chunk.get! pos)
        pos := pos + 1
        match Streams.Framing.decodeLength? .uvarint (Bytes.toNatList header) with
        | .error .truncated => pure ()
        | .error .malformed => return .error (.protocol "the RPC header is malformed")
        | .ok (size, _) =>
          if cap < size then
            return .error (.protocol "the RPC exceeds the cap")
          -- The allocation runs only after the length passes the cap.
          body := ByteArray.emptyWithCapacity size
          expected := some size
          cursor := 0
          header := ByteArray.emptyWithCapacity Varint.maxBytes
  return .ok ()

/-- Serve every RPC of a peer's stream in arrival order. Frame errors reset
both directions. A clean EOF closes our write direction. The host owns and
joins this handler task. -/
def handler (events : Conc.Chan Input) (cap : Nat := Constants.rpcCap)
    (id : Libp2p.Core.ProtocolId := Constants.meshsubId)
    (onVersion : Peer → Libp2p.Core.ProtocolId → BaseIO Unit := fun _ _ => pure ())
    (split : ByteArray → BaseIO (Option ByteArray) := fun b => pure (some b)) :
    Libp2p.Core.StreamHandler where
  id := id
  handle ctx stream := ExceptT.mk do
    let peer := ctx.remotePeer
    -- The id this handler serves is the version the peer chose.
    (onVersion peer id : BaseIO Unit)
    -- The opener joins before its first RPC. Repeat joins are loop no-ops.
    if let .error _ ← events.send (.event (.peerJoined peer .meshsub)) then
      stream.close
      return .ok ()
    -- A floodsub stream marks its peer after the join, so the router
    -- knows the peer when the mark arrives.
    if id == Constants.floodsubId then
      if let .error _ ← events.send (.event (.protocol peer .floodsub)) then
        stream.close
        return .ok ()
    let answer ← readFrames events cap split peer stream
    match answer with
    | .ok () => stream.close
    | .error _ => stream.reset
    return answer

/-! ## The subscription table -/

/-- One delivery callback. -/
private structure Subscription where
  /-- The unique registration id used by a refused post. -/
  id : Nat
  /-- The topic. -/
  topic : TopicId
  /-- The callback. -/
  callback : Message → BaseIO Unit

/-- The shared table of the callbacks, in registration order. -/
private structure Subscriptions where
  /-- The next unused registration id. -/
  next : Nat
  /-- The callbacks. -/
  entries : List Subscription

/-- Call every callback of the topic of `m`, in registration order. -/
private def deliver (subs : Conc.OnceRef Subscriptions) (m : Message) : BaseIO Unit := do
  for sub in (← subs.get).entries do
    if sub.topic = m.topic then
      sub.callback m

/-! ## The loop -/

/-- What the loop reads and never changes. -/
private structure Env where
  /-- The host seam. -/
  host : HostSeam
  /-- The configuration. -/
  config : Config
  /-- The subscription table. -/
  subs : Conc.OnceRef Subscriptions
  /-- The queue of inbound RPCs and the joins of their streams. A full
  queue parks the reader, so the back-pressure reaches the peer. -/
  events : Conc.Chan Input
  /-- The queue of every other input: the alarm's wakes, the
  application's posts and reads, and the host's notices. The loop serves
  it first (`nextInput`). -/
  control : Conc.Chan Input
  /-- The owned alarm task posts wakes on events. -/
  alarm : Conc.Alarm
  /-- The owner of the loop, alarm and writers. -/
  tasks : Conc.TaskSet
  /-- The peer writer registry. The loop inserts and writers retire by id. -/
  outbound : Conc.OnceRef (List (Peer × Outbound))
  /-- The next writer generation, allocated atomically. -/
  nextOutbound : Conc.OnceRef Nat
  /-- The first stop caller sets this flag. -/
  closing : Conc.OnceRef Bool
  /-- Frames refused by a full or closed outbound queue. -/
  drops : Conc.OnceRef Nat
  /-- The peers whose meshsub negotiation failed. The next `connected` of
  a peer removes it. -/
  unsupported : Conc.OnceRef (List Peer)
  /-- The meshsub version each peer negotiated, from our writer's open
  or from the handler that served its stream. -/
  versions : Conc.OnceRef (List (Peer × Libp2p.Core.ProtocolId))
  /-- The payloads of the `ByteArray` path, by id, with the time each
  was stored. -/
  payloads : Conc.OnceRef (Std.HashMap MessageId (ByteArray × Millis))
  /-- The peers that got our Extensions message since they joined. The
  message goes once per peer, in the first frame we send it
  (`gossipsub-v1.3.md`). A writer that opens its stream again sends
  none, as rust-libp2p sends it once per peer (`behaviour.rs`,
  `handle_established_*_connection`). `removePeer` clears the entry. -/
  extSent : Conc.OnceRef (List Peer)
  /-- The peer-exchange peers that wait for a connector. `stop` closes
  it, and the connectors end. -/
  pxQueue : Conc.Chan Peer

/-- Encode and offer one RPC to a peer's queue. This operation never parks.
A full queue drops a frame of gossip or messages. A frame of our state
waits on a task of its own (`mustArrive` below). Each peer has one
writer and one stream. -/
private def enqueueFrame (env : Env) (peer : Peer) (rpc0 : Rpc.RPC) : BaseIO Bool := do
  if ← env.closing.get then return true
  -- IDONTWANT goes to a v1.2 or v1.3 peer only (`gossipsub-v1.2.md`).
  -- For any other peer, and while the version is unknown, the control
  -- message goes without it.
  let version := (← env.versions.get).lookup peer
  let v12 := version == some Constants.meshsubV12Id || version == some Constants.meshsubV13Id
  let rpc := match rpc0.control with
    | some c => if v12 || c.idontwant.isEmpty then rpc0
      else { rpc0 with control := some { c with idontwant := [] } }
    | none => rpc0
  if rpc.subscriptions.isEmpty && rpc.publish.isEmpty &&
      (match rpc.control with
       | some c => c.ihave.isEmpty && c.iwant.isEmpty && c.graft.isEmpty && c.prune.isEmpty &&
           c.idontwant.isEmpty
       | none => true) &&
      !(match rpc0.control with | some c => c.idontwant.isEmpty | none => true) then
    -- Only an IDONTWANT, and the peer cannot take it.
    return true
  let table ← env.outbound.get
  let ob ← match table.find? (fun e => e.1 == peer) with
    | some (_, ob) => pure ob
    | none => do
      let id ← env.nextOutbound.updateGet (fun n => (n, n + 1))
      let ob : Outbound := { id, queue := ← Conc.Chan.new 32, stream := ← Conc.OnceRef.new none }
      env.outbound.update (fun table => (peer, ob) :: table)
      let record (q : Peer) (id : Libp2p.Core.ProtocolId) : BaseIO Unit := do
        env.versions.update fun l => (q, id) :: l.filter (·.1 != q)
        -- The router took the peer for a gossipsub peer at its join.
        if id == Constants.floodsubId then
          discard <| env.control.trySend (.event (.protocol q .floodsub))
      env.tasks.spawn (writer env.host env.closing env.outbound env.unsupported record
        env.config.floodsub peer ob)
      pure ob
  -- The first frame to a peer carries the Extensions message. A v1.1 or
  -- v1.2 peer skips field 6 as an unknown field.
  let first ← env.extSent.updateGet fun l => (!l.contains peer, if l.contains peer then l else peer :: l)
  let rpc := match first, Core.ownExtensions env.config.params with
    | true, some ext =>
      let c := rpc.control.getD { ihave := [], iwant := [], graft := [], prune := [] }
      { rpc with control := some { c with extensions := some ext } }
    | _, _ => rpc
  (env.config.onSend peer rpc : BaseIO Unit)
  -- On the payload path the published messages carry handles, and the
  -- frame takes the stored payloads back (`Payload.joinOutbound`).
  let frame? : Option ByteArray ←
    if env.config.payloadId.isSome && !rpc.publish.isEmpty then do
      let store ← env.payloads.get
      let body := Payload.joinOutbound rpc (fun h => (store.get? h).map (·.1))
      pure (if body.size ≤ env.config.maxRpcSize then
        some (Bytes.ofNatList (Streams.Framing.encodeLength .uvarint body.size) ++ body)
        else none)
    else pure ((Rpc.encodeFrame? rpc env.config.maxRpcSize).map Bytes.ofNatList)
  let some frame := frame? | do
    -- The node drops the frame. The next one takes the Extensions
    -- message.
    if first then env.extSent.update (·.filter (· != peer))
    return false
  if ← env.closing.get then
    ob.queue.close
    return true
  -- A frame that tells the peer our state may not be lost: subscriptions,
  -- GRAFT and PRUNE, and the Extensions message, which goes once. go
  -- retries such an announcement when the queue is full (`announceRetry`,
  -- `pubsub.go`). Here a task of the node parks on the queue instead, so
  -- the loop never parks. Gossip and messages still drop: the peer can
  -- ask again.
  let mustArrive := !rpc.subscriptions.isEmpty ||
    (match rpc.control with
     | some c => !c.graft.isEmpty || !c.prune.isEmpty || c.extensions.isSome
     | none => false)
  if !(← ob.queue.trySend frame) then
    if mustArrive then
      -- Park: the writer's take frees a slot, and the peer's removal or
      -- `stop` closes the queue.
      env.tasks.spawn (discard <| ob.queue.send frame)
    else env.drops.update (· + 1)
  return true

/-- Encode and offer one RPC to a peer's queue (`enqueueFrame`). The
core sends at most one message per RPC (`forwardPubs`, `handleIwant`,
`publishLocal`), so an RPC over the cap holds one message too large on
its own. The node drops it and counts it in `Node.dropped`. -/
private def enqueue (env : Env) (peer : Peer) (rpc : Rpc.RPC) : BaseIO Unit := do
  if !(← enqueueFrame env peer rpc) then env.drops.update (· + 1)

/-- Retire a peer writer after its disconnect event. -/
private def removePeer (env : Env) (peer : Peer) : BaseIO Unit := do
  -- A rejoin starts a new record at the peer's core, so it takes a new
  -- Extensions message.
  env.extSent.update (·.filter (· != peer))
  let removed ← env.outbound.updateGet fun table =>
    (table.filter (fun e => e.1 == peer), table.filter (fun e => e.1 != peer))
  for (_, ob) in removed do
    ob.queue.close
    env.tasks.spawn (endOutbound ob)

/-- One gossip send that waits for its due time. -/
private structure Pending where
  /-- The due time. -/
  due : Millis
  /-- The receiver. -/
  peer : Peer
  /-- The RPC. -/
  rpc : Rpc.RPC

/-- The local state of the loop. -/
private structure LoopState where
  /-- The router state. -/
  router : Core.State
  /-- The gossip sends that wait for their due time. -/
  pending : List Pending
  /-- The time of the next heartbeat. -/
  nextTick : Millis
  /-- The heartbeat count used for the peer order. -/
  ticks : Nat
  /-- The next run-wide delayed gossip index. -/
  gossipIndex : Nat
  /-- The router parameters: `Config.params` at the start, with the
  topic score parameters that `setTopicParams` replaced since. -/
  params : Core.Params
  /-- The replaced topic parameters, one entry per topic. `params` reads
  this map over the config's own function, so a replacement never
  wraps the one before it. -/
  topicOverrides : Std.HashMap TopicId (Option Score.TopicParams) := {}
  /-- The time of the next explicit-peer connectivity check. -/
  nextExplicitCheck : Millis := 0

/-- The peer of a peer-exchange entry, when its id decodes. -/
private def infoPeer? (info : Rpc.PeerInfo) : Option Peer :=
  info.peerId.bind fun b => (Libp2p.Identity.PeerId.ofBytes? (Bytes.ofNatList b)).toOption

/-- Add the signed peer record the host holds to each peer-exchange entry
of a prune (`Core.pxPeers` leaves it out), as go's `makePrune` reads it
from the certified address book. An entry with no record goes as the
peer id alone, which the spec allows. -/
private def fillRecords (env : Env) (rpc : Rpc.RPC) : BaseIO Rpc.RPC := do
  let some c := rpc.control | return rpc
  if c.prune.all (·.peers.isEmpty) then return rpc
  let prune ← c.prune.mapM fun q => do
    let peers ← q.peers.mapM fun info => do
      match infoPeer? info with
      | none => pure info
      | some pid => do
        let spr ← env.host.recordOf pid
        pure { info with signedPeerRecord := spr.map Bytes.toNatList }
    pure { q with peers }
  return { rpc with control := some { c with prune } }

/-- Handle the peers a prune offered (`Core.Action.pxConnect`). The node
skips a peer whose signed record fails the check, as go's `pxConnect`
does. The addresses of a valid record enter the peerstore. Each peer
then waits for a connector in the bounded queue, and a full queue drops
it. -/
private def pxConnect (env : Env) (infos : List Rpc.PeerInfo) : BaseIO Unit := do
  for info in infos do
    let some pid := infoPeer? info | continue
    if let some spr := info.signedPeerRecord then
      if !(← env.host.consumeRecord pid (Bytes.ofNatList spr)) then continue
    discard <| env.pxQueue.trySend pid

/-- One connector: dial each queued peer the host does not serve yet,
until `stop` closes the queue. go-libp2p-pubsub's `connector`. -/
private def connector (env : Env) : Conc.Async Unit := do
  repeat
    -- Park: a peer arrives, or `stop` closes the queue.
    match ← env.pxQueue.recv with
    | none => break
    | some pid =>
      let live ← match env.host.peers with
        | some get => (get : BaseIO (List Peer))
        | none => pure []
      if !live.contains pid then
        discard <| env.host.dial pid

/-- Run the actions of one core step, in order, and answer the delayed
sends. `gossipAt` is the time of the tick when a tick made the actions. The
run-wide i-th IHAVE waits for trickle i milliseconds. Every other action
runs now. -/
private def perform (env : Env) (gossipAt : Option Millis) (index : Nat)
    (actions : List Core.Action) : BaseIO (List Pending × Nat) := do
  let mut delayed : Array Pending := #[]
  let mut gossipIndex := index
  for action in actions do
    match action with
    | .deliver m => (deliver env.subs m : BaseIO Unit)
    | .validate m id source => env.config.onValidate m id source
    | .partialIn source pm => env.config.onPartial source pm
    | .partialGossip topic peers => env.config.onPartialGossip topic peers
    | .pxConnect _ infos => pxConnect env infos
    | .sendRpc to rpc0 =>
      let rpc ← fillRecords env rpc0
      match gossipAt with
      | some now =>
        if hasIhave rpc then
          let delay := env.config.trickle gossipIndex
          gossipIndex := gossipIndex + 1
          if delay = 0 then
            enqueue env to rpc
          else
            delayed := delayed.push { due := now + delay, peer := to, rpc := rpc }
        else
          enqueue env to rpc
      | none => enqueue env to rpc
  return (delayed.toList, gossipIndex)

/-- Tell peers about a subscription change, or tell a new peer about all
current subscriptions. Each offer uses the bounded per-peer queue. -/
private def announce (env : Env) (st : LoopState) (event : Core.Event) :
    BaseIO LoopState := do
  match event with
  | .subscribe t =>
    let rpc := subOptRpc st.params t true
    for (peer, _) in st.router.peers do
      enqueue env peer rpc
  | .unsubscribe t =>
    let rpc := subOptRpc st.params t false
    for (peer, _) in st.router.peers do
      enqueue env peer rpc
  | .peerJoined peer _ =>
    if !st.router.topics.isEmpty then
      enqueue env peer (Core.helloRpc st.router.topics (some st.params))
  | _ => pure ()
  return st

/-- Drop the core hello when the node already sent per-topic join records. -/
private def withoutPeerHello (peer : Peer) (topics : List TopicId) :
    List Core.Action → List Core.Action
  | [] => []
  | action :: rest =>
    match action with
    | .sendRpc target rpc =>
      if !topics.isEmpty && target == peer && rpc == Core.helloRpc topics then
        withoutPeerHello peer topics rest
      else action :: withoutPeerHello peer topics rest
    | _ => action :: withoutPeerHello peer topics rest

/-- One core step, then its actions. Only an RPC that does not decode makes
the core answer `.error`. That answer keeps the state, and the loop runs on. -/
private def stepAndAct (env : Env) (st : LoopState) (event : Core.Event) : BaseIO LoopState := do
  if let .peerJoined peer _ := event then
    if (Core.peerOf st.router peer).isSome then return st
  let st ← announce env st event
  if let .rpc peer bytes := event then
    (env.config.onRpc peer bytes : BaseIO Unit)
  let st ← match event with
    | .peerLeft peer => do
      removePeer env peer
      pure { st with pending := st.pending.filter (fun p => p.peer != peer) }
    | _ => pure st
  match Core.step st.params st.router event with
  | .error (.decode _) => return st
  | .ok (router, actions) =>
    let actions := match event with
      | .peerJoined peer _ => withoutPeerHello peer st.router.topics actions
      | _ => actions
    let gossipAt := match event with
      | .tick now _ => some now
      | _ => none
    let (delayed, gossipIndex) ← perform env gossipAt st.gossipIndex actions
    let all := st.pending ++ delayed
    let overflow := all.length - 256
    if 0 < overflow then env.drops.update (· + overflow)
    return { st with router, gossipIndex, pending := all.take 256 }

/-- The next wake is the first due send or the next heartbeat. -/
private def dueOf (st : LoopState) : Millis :=
  st.pending.foldl (fun due p => Nat.min due p.due) st.nextTick

/-- Make the router's peers equal to the host's live peers, less the
peers that speak no meshsub. A full queue or the race at start can lose
a `peerJoined` or a `peerLeft`, and this step corrects it. -/
private def reconcile (env : Env) (st : LoopState) : BaseIO LoopState := do
  let some livePeers := env.host.peers | return st
  let live ← livePeers
  let unsup ← env.unsupported.get
  let known := st.router.peers.map (·.1)
  let mut st := st
  for q in known do
    if !live.contains q || unsup.contains q then
      st ← stepAndAct env st (.peerLeft q)
  for q in live do
    if !known.contains q && !unsup.contains q then
      st ← stepAndAct env st (.peerJoined q .meshsub)
  return st

/-- Dial each explicit peer the host does not serve, each on a task of
the node, so the loop never parks on a dial. -/
private def dialExplicit (env : Env) : BaseIO Unit := do
  if env.config.explicitPeers.isEmpty then return ()
  let live ← match env.host.peers with
    | some get => get
    | none => pure []
  for q in env.config.explicitPeers do
    if !live.contains q then
      env.tasks.spawn (discard (env.host.dial q))

/-- Send due gossip before the heartbeat shifts the message cache. -/
private def onWake (env : Env) (st : LoopState) (now : Millis) : BaseIO LoopState := do
  let (due, later) := st.pending.partition (fun p => decide (p.due ≤ now))
  for p in due.mergeSort (fun a b => decide (a.due ≤ b.due)) do
    enqueue env p.peer p.rpc
  let st := { st with pending := later }
  if st.nextTick ≤ now then
    let st ← reconcile env st
    -- A stored payload lives one heartbeat past the message cache's
    -- window, so an IWANT answer and a held message still find it.
    if env.config.payloadId.isSome then
      let ttl := (st.params.window.historyLength + 1) * st.params.heartbeatInterval
      env.payloads.update fun m => m.filter fun _ (_, t) => now < t + ttl
    let st ← if st.nextExplicitCheck ≤ now then do
        dialExplicit env
        pure { st with nextExplicitCheck := now + env.config.explicitCheckMs }
      else pure st
    let st := { st with router := Core.expirePending st.params st.router now }
    let opportunistic := st.ticks > 0 && st.ticks % env.config.opportunisticGraftTicks == 0
    let (router, grafts) := Core.maintain st.params st.router now opportunistic
    let st := { st with router }
    discard <| perform env none st.gossipIndex grafts
    let order := env.config.order st.ticks (st.router.peers.map (·.1))
    let st ← stepAndAct env st (.tick now order)
    return { st with nextTick := now + st.params.heartbeatInterval, ticks := st.ticks + 1 }
  return st

/-- The next input of the loop. A queued control input comes first.
Otherwise the input that arrives first on either queue comes next.

A burst of inbound RPCs can fill `events` and park its readers. The
control inputs still come first: the heartbeat, the application's posts,
and the host's joins and leaves.

The answer is `none` when both queues are closed and empty. The loop
still reads the queued inputs of a closed queue.

The two queues keep no order between them. A host's leave can pass a
join that a stream handler queued earlier. The router then keeps a
departed peer until the next heartbeat. That heartbeat's `reconcile`
drops the peer before the mesh plans. An RPC that passes its peer's
leave finds an unknown peer, and the core ignores it. -/
def nextInput {α : Type} (control events : Conc.Chan α) : Conc.Async (Option α) := do
  if let some i ← (control.tryRecv : BaseIO (Option α)) then return some i
  -- Park: an input on either queue wakes it, and so does a close.
  let (fromControl, got) ← Conc.select
    #[Conc.Park.recv control (true, ·), Conc.Park.recv events (false, ·)]
  match got with
  | some i => return some i
  -- One queue is closed and empty. Read the other queue until it ends.
  | none => if fromControl then events.recv else control.recv

/-- Run the core through one receive park. Each action returns its state.
`nextInput` returns `none` only after the loop reads every queued input
of the closed queues. The tail closes the alarm and every cached
outbound stream. -/
private def loop (env : Env) (st0 : LoopState) : Conc.Async Unit := do
  let mut st := st0
  (env.alarm.set (dueOf st) : BaseIO Unit)
  repeat
    match ← nextInput env.control env.events with
    | none => break
    | some (.wake now) => st ← (onWake env st now : BaseIO LoopState)
    | some (.event e) =>
      st ← (stepAndAct env st e : BaseIO LoopState)
    | some (.inspect k) => (k st.params st.router : BaseIO Unit)
    | some (.setTopicParams topic tp) =>
      -- One map, read over the config's function: the closure depth
      -- stays one however many replacements come.
      let overrides := st.topicOverrides.insert topic tp
      let base := env.config.params.score.topics
      st := { st with
        topicOverrides := overrides
        params := { st.params with score := { st.params.score with
          topics := fun t => (overrides.get? t).getD (base t) } } }
    (env.alarm.set (dueOf st) : BaseIO Unit)
  (env.alarm.close : BaseIO Unit)
  for (_, ob) in ← (env.outbound.get : BaseIO (List (Peer × Outbound))) do
    (ob.queue.close : BaseIO Unit)

/-- The router state of a node with no peers at time `now`. -/
private def initialState (p : Core.Params) (now : Millis) : Core.State :=
  { peers := []
    mesh := []
    fanout := []
    mcache := Cache.MessageIndex.empty p.window
    seen := Cache.SeenIndex.empty p.seen
    backoff := []
    iwant := []
    topics := []
    now := now
    lastHeartbeat := now
    lastDecay := now }

/-- The published message of a payload. The four signed fields stay absent,
as `strictNoSign` requires. -/
private def messageOf (topic : TopicId) (payload : ByteArray) : Message :=
  { «from» := none
    data := some (Bytes.toNatList payload)
    seqno := none
    topic := topic
    signature := none
    key := none }

/-- The slots of each input queue of the loop. -/
def inputSlots : Nat := 64

/-- Build the state, register the handler, and start the loop. Each of
the two queues holds `inputSlots` inputs. A full RPC queue parks an inbound
handler, which carries the back-pressure to the peer. A full control
queue refuses a `BaseIO` post of the application. Inbound RPCs never
enter the control queue, and the loop serves it first. -/
def start (host : HostSeam) (config : Config := {}) : BaseIO Node := do
  -- On the payload path a message's `data` is its handle, the id bytes,
  -- so the core's id function reads it back.
  let config := if config.payloadId.isSome then
      { config with params := { config.params with msgId := fun m => ⟨m.data.getD []⟩ } }
    else config
  let now ← config.clock.nowMs
  let subs : Conc.OnceRef Subscriptions ← Conc.OnceRef.new { next := 0, entries := [] }
  -- `inputSlots` unfolds to a literal, so `decide` proves the capacity
  -- positive.
  let events : Conc.Chan Input ← Conc.Chan.new inputSlots (by decide)
  let control : Conc.Chan Input ← Conc.Chan.new inputSlots (by decide)
  let versions ← Conc.OnceRef.new ([] : List (Peer × Libp2p.Core.ProtocolId))
  let record (q : Peer) (id : Libp2p.Core.ProtocolId) : BaseIO Unit :=
    versions.update fun l => (q, id) :: l.filter (·.1 != q)
  let payloads ← Conc.OnceRef.new ({} : Std.HashMap MessageId (ByteArray × Millis))
  let over (d : ByteArray) : Bool :=
    match config.params.maxDataSize with
    | some cap => decide (cap < d.size)
    | none => false
  -- The inbound split of the payload path (`Payload.splitInbound`). A
  -- malformed RPC goes to the core as it came, and the core's decoder
  -- reports it. The split drops an RPC with an oversize payload, or with
  -- a payload that has no id.
  let split : ByteArray → BaseIO (Option ByteArray) := fun body => do
    match config.payloadId with
    | none => return some body
    | some idOf =>
      match Payload.splitInbound body idOf with
      | .error .malformed => return some body
      | .error .noId => return none
      | .ok (small, ps) =>
        if ps.any (fun (_, d) => over d) then return none
        let t ← config.clock.nowMs
        payloads.update fun m =>
          ps.foldl (fun m (id, d) => if m.contains id then m else m.insert id (d, t)) m
        return some small
  -- The node serves every version. The handler's id tells the peer's
  -- choice.
  host.setHandler (handler events config.maxRpcSize Constants.meshsubV13Id record split)
  host.setHandler (handler events config.maxRpcSize Constants.meshsubV12Id record split)
  host.setHandler (handler events config.maxRpcSize Constants.meshsubId record split)
  if config.floodsub then
    host.setHandler (handler events config.maxRpcSize Constants.floodsubId record split)
  let tasks ← Conc.TaskSet.new
  let alarm ← Conc.Alarm.new
  let outbound ← Conc.OnceRef.new ([] : List (Peer × Outbound))
  let nextOutbound ← Conc.OnceRef.new 0
  let closing ← Conc.OnceRef.new false
  let drops ← Conc.OnceRef.new 0
  let unsupported ← Conc.OnceRef.new ([] : List Peer)
  let extSent ← Conc.OnceRef.new ([] : List Peer)
  -- A configured 0 gets one slot: the channel needs a positive capacity.
  let pxQueue : Conc.Chan Peer ←
    if h : 0 < config.maxPendingConnections then Conc.Chan.new config.maxPendingConnections h
    else Conc.Chan.new 1
  tasks.spawn <| alarm.run config.clock (fun now => control.send (.wake now))
  let env : Env :=
    { host, config, subs, events, control, alarm, tasks, outbound, nextOutbound, closing, drops, unsupported,
      versions, payloads, extSent, pxQueue }
  for _ in [0:config.connectors] do
    tasks.spawn (connector env)
  tasks.spawn <| loop env
    { router := { initialState config.params now with explicit := config.explicitPeers }
      pending := []
      nextTick := now + config.params.heartbeatInterval
      ticks := 0
      gossipIndex := 0
      params := config.params }
  let post : Core.Event → BaseIO Bool := fun e => do
    if ← closing.get then return false
    control.trySend (.event e)
  -- The host's sessions reach the router here. `current` holds the
  -- session number of each peer's last `connected`, so the notifiee
  -- drops a stale `disconnected` of a replaced session (`Host.ConnEvent`).
  let current ← Conc.OnceRef.new ([] : List (Peer × Nat))
  host.addNotifiee fun
    | .connected peer session role remoteAddr => do
      current.update fun t => (peer, session) :: t.filter (·.1 != peer)
      -- A new session may speak meshsub where the last did not.
      unsupported.update (·.filter (· != peer))
      discard <| post (.peerJoined peer .meshsub)
      -- The direction feeds `D_out`, the IP address feeds P₆.
      let ip := match remoteAddr.components with
        | f :: _ => if f.proto == .ip4 || f.proto == .ip6 then some f.value else none
        | [] => none
      discard <| post (.peerInfo peer (role == .initiator) ip)
    | .disconnected peer session => do
      let mine ← current.updateGet fun t =>
        if t.any (· == (peer, session)) then (true, t.filter (·.1 != peer)) else (false, t)
      if mine then discard <| post (.peerLeft peer)
  if let some livePeers := host.peers then
    for peer in ← livePeers do
      discard <| post (.peerJoined peer .meshsub)
  return {
    -- "MUST NOT emit" a message over the cap (phase0 "Maximum message
    -- sizes"): `publish` refuses an oversize payload here.
    publish := fun topic payload =>
      match config.payloadId with
      | some idOf =>
        -- The payload path: store the bytes, publish the handle.
        if over payload then pure false
        else do
          let some id := idOf topic.name payload | pure false
          let t ← config.clock.nowMs
          payloads.update (·.insert id (payload, t))
          post (.publish { messageOf topic .empty with data := some id.bytes })
      | none =>
        if Core.sizeOk config.params (messageOf topic payload) then
          post (.publish (messageOf topic payload))
        else pure false
    payload := fun id => do return ((← payloads.get).get? id).map (·.1)
    subscribe := fun topic callback => do
      if ← closing.get then return false
      let id ← subs.updateGet fun s =>
        (s.next,
          { next := s.next + 1
            entries := s.entries ++ [{ id := s.next, topic, callback }] })
      let sent ← post (.subscribe topic)
      if !sent then
        subs.update fun s => { s with entries := s.entries.filter (fun entry => entry.id != id) }
      return sent
    subscribeWait := fun topic callback => do
      if ← (closing.get : BaseIO Bool) then return false
      let id ← (subs.updateGet fun s =>
        (s.next,
          { next := s.next + 1
            entries := s.entries ++ [{ id := s.next, topic, callback }] }) : BaseIO Nat)
      -- Park: the loop's take frees a slot, and `stop` closes the queue.
      match ← control.send (.event (.subscribe topic)) with
      | .ok () => return true
      | .error _ =>
        (subs.update fun s => { s with entries := s.entries.filter (fun entry => entry.id != id) } :
          BaseIO Unit)
        return false
    unsubscribe := fun topic => do
      if ← (closing.get : BaseIO Bool) then return false
      (subs.update fun s => { s with entries := s.entries.filter (fun e => e.topic != topic) } :
        BaseIO Unit)
      -- Park: the loop's take frees a slot, and `stop` closes the queue.
      return (← control.send (.event (.unsubscribe topic))) matches .ok _
    peerJoined := fun peer proto => post (.peerJoined peer proto)
    peerLeft := fun peer => post (.peerLeft peer)
    report := fun id source outcome => post (.validated id source outcome)
    setAppScore := fun peer score => post (.appScore peer score)
    scores := do
      if ← (closing.get : BaseIO Bool) then return none
      let reply : Conc.Chan (List (Peer × Score)) ← Conc.Chan.new 1
      let k : Core.Params → Core.State → BaseIO Unit := fun p s =>
        discard <| reply.trySend (s.peers.map fun (q, _) => (q, Core.scoreOf p s q))
      if !(← (control.trySend (.inspect k) : BaseIO Bool)) then return none
      -- Park: the loop answers, or `stop` closes the queue, and the loop
      -- serves the queued inspect before it ends.
      reply.recv
    stats := do
      if ← (closing.get : BaseIO Bool) then return none
      let reply : Conc.Chan Stats ← Conc.Chan.new 1
      let k : Core.Params → Core.State → BaseIO Unit := fun _ s => do
        discard <| reply.trySend {
          peers := s.peers.length
          mesh := s.mesh.map fun (t, ps) => (t, ps.length)
          topics := s.topics.length
          seen := s.seen.index.size
          cached := s.mcache.byId.size
          pending := s.pending.length
          dontSend := s.dontSend.length
          dropped := ← drops.get
          v12Peers := ((← versions.get).filter (·.2 == Constants.meshsubV12Id)).length
          v13Peers := ((← versions.get).filter (·.2 == Constants.meshsubV13Id)).length }
      if !(← (control.trySend (.inspect k) : BaseIO Bool)) then return none
      -- Park: the loop answers, or `stop` closes the queue after serving it.
      reply.recv
    setTopicParams := fun topic tp => do
      if ← (closing.get : BaseIO Bool) then return false
      -- Park: the loop's take frees a slot, and `stop` closes the queue.
      return (← control.send (.setTopicParams topic tp)) matches .ok _
    sendPartial := fun peer pm => post (.sendPartial peer pm)
    judgePartial := fun peer topic valid => post (.partialJudged peer topic valid)
    partialPeers := fun topic => do
      if ← (closing.get : BaseIO Bool) then return none
      let reply : Conc.Chan (List (Peer × Bool)) ← Conc.Chan.new 1
      let k : Core.Params → Core.State → BaseIO Unit := fun _ s => do
        let targets := if Core.memB topic s.topics then Core.meshOf s topic else Core.fanoutOf s topic
        let pairs := targets.filterMap fun q =>
          let o := Core.peerPartial s q topic
          if o.sends then some (q, o.requests) else none
        discard <| reply.trySend pairs
      if !(← (control.trySend (.inspect k) : BaseIO Bool)) then return none
      -- Park: the loop answers, or `stop` closes the queue after serving it.
      reply.recv
    dropped := drops.get
    stop := do
      let first ← (closing.updateGet (fun was => (!was, true)) : BaseIO Bool)
      if first then
        (control.close : BaseIO Unit)
        (events.close : BaseIO Unit)
        (pxQueue.close : BaseIO Unit)
        for (_, ob) in ← (outbound.get : BaseIO (List (Peer × Outbound))) do
          endOutbound ob
        tasks.joinAll }

end Libp2p.Protocols.Gossipsub.Node
