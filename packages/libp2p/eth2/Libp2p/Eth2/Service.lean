import Std.Time
import Conc
import Streams
import Snappy
import Libp2p.Host
import Libp2p.Mux
import Libp2p.Security
import Libp2p.Quic
import Libp2p.Discv5
import Libp2p.Protocols.Identify
import Libp2p.Protocols.Gossipsub.HostSeam
import Libp2p.Protocols.Gossipsub.Node
import Libp2p.Protocols.ReqResp.Exchange
import Libp2p.Protocols.ReqResp.Limiter
import Libp2p.Eth2.Fork
import Libp2p.Eth2.Enr
import Libp2p.Eth2.Topic
import Libp2p.Eth2.MessageId
import Libp2p.Eth2.Messages
import Libp2p.Eth2.Gossip
import Libp2p.Eth2.Peers
import Libp2p.Eth2.Scoring
import Libp2p.Eth2.Forks
import Libp2p.Eth2.PartialColumns

/-!
# The consensus network service

One value that a consensus client runs for its networking: the host,
the gossipsub node, the discv5 node, and the req/resp methods, wired
the way the consensus spec asks. The client keeps the chain and every
consensus type. It hands the service its fork schedule (`Chain`), its
`Status`, and its `MetaData`, each as the client encodes it. It answers
the gossip validations and the block and column requests, and it reads
the events. The service carries the bytes and never decodes SSZ.

## What the service does by itself

* **Transports.** TCP with Noise and yamux or mplex, and QUIC v1 when
  the config has a QUIC port. The host ranks QUIC first
  (`Policy.quicFirst`), as phase0 "Transport" asks.
* **The identity.** One secp256k1 key is the libp2p identity and the
  ENR key. Peers derive our peer id from our ENR (`Enr.peerId`), so the
  two must be one key.
* **Status.** "The dialing client MUST send a `Status` request upon
  connection." The service sends ours on each outbound connection, and
  it answers each inbound one with ours. A peer whose `fork_digest`, the
  first 4 bytes, is not ours gets Goodbye with reason 2, and its
  connection ends ("SHOULD immediately disconnect"). The other check of
  the spec, a finalized root outside our chain, needs the chain, so it
  stays with the client.
* **Ping, MetaData, Goodbye.** The service answers Ping with our
  `seq_number`, and MetaData v3 and v2 with the client's bytes. Each
  Goodbye of a peer becomes an event. At `stop`, the service says
  Goodbye with reason 1 to every peer.
* **Liveness.** The service pings each peer on Lighthouse's intervals
  (`Peers`). A newer `seq_number` in the answer brings a MetaData
  request, and the answer becomes `Event.metaData`. A peer that does not
  answer becomes `Event.unresponsive`. The spec lets a client end that
  connection, and the client decides (`disconnect`).
* **Bans.** `ban` sends Goodbye with reason 251 and ends the peer's
  connections. The host's gater then refuses the peer until the ban
  ends, and discovery skips it. The client decides who earns a ban.
* **Discovery.** discv5 runs on its own UDP port, with the consensus
  fields in our record. Every `discoverEveryMs`, while the host has
  fewer than `targetPeers` peers, a lookup finds records with our fork
  digest and a TCP or QUIC address, and the service dials them. The
  boot records go into the table, and the service dials them at start,
  as Lighthouse does.
* **Gossip.** The client subscribes by `Kind`, under our current
  digest. Each arriving message is held (`validateMessages`). The
  service decompresses its `data`, and the client gets the SSZ, the
  message id, and the propagation source. The client answers through
  `report`. Data that does not decompress gets REJECT at once: "Clients
  MUST reject (fail validation) messages containing an incorrect type,
  or invalid payload".
* **Requests.** The service checks each request against its method's
  bounds, and it hands the client the method and the request's bytes
  (`Config.serve`). It sends at most the method's chunk count. The
  client keeps the request's own count, for example "no more than
  `count` blocks".
* **Partial columns.** The service carries the parts metadata and the
  message of each partial column to the client and back, by block root
  and column (`PartialColumns`). It gives each peer the first-delivery
  reward once per block and column.
* **Forks.** The fork loop follows the schedule (`Forks`). One epoch
  before a fork, it joins the client's kinds under the next digest. At
  the fork, our `Status` and our record take the new digest, and the
  pre-fork topics lose their score parameters. Two epochs later, it
  leaves the pre-fork topics.
* **Scoring.** The router scores peers with Lighthouse's profile
  (`Scoring`). The client keeps the chain-dependent topics current with
  `updateScores`.

## Concurrency

Every task belongs to the service's task set, and `stop` joins it
(root §4.1). The discovery loop, the liveness loop, and the fork loop
park on their timers and on `stopping`, which `stop` closes. The host notifiee and the gossipsub validation
callback run on tasks that must not park. So they call
`Config.onEvent`, which must not park either, and they spawn the work
that waits. `stop` closes the host before it joins the set, and the
host's close removes the notifiee, so no spawn comes after the join.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Conc Streams Multiformats
open Libp2p.Identity
open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub (TopicId MessageId Message)
open Libp2p.Protocols.ReqResp (Chunk Method Limiter)

/-- What the service reports. The client's callback must not park. -/
inductive Event where
  /-- A peer connected. `outbound` when we dialed it. -/
  | connected (peer : PeerId) (outbound : Bool)
  /-- A peer's last session ended. -/
  | disconnected (peer : PeerId)
  /-- A peer's `Status`, from either side of the handshake: its 92 bytes
  of SSZ. -/
  | status (peer : PeerId) (status : ByteArray)
  /-- A held gossip message: its kind, its message id, its propagation
  source, and its SSZ, decompressed. The client answers with `report`. -/
  | gossip (kind : Kind) (id : MessageId) (source : PeerId) (ssz : ByteArray)
  /-- A peer said Goodbye. -/
  | goodbye (peer : PeerId) (reason : Nat)
  /-- A peer's Ping answer named a newer `seq_number`, and its MetaData v3
  arrived: the `seq_number` of the Ping and the 25 bytes of SSZ. -/
  | metaData (peer : PeerId) (seq : Nat) (metaData : ByteArray)
  /-- A peer did not answer our Ping. The spec lets the client end the
  connection ("MAY disconnect"); the service leaves that to the client
  (`Service.disconnect`). -/
  | unresponsive (peer : PeerId)
  /-- A partial message on a column topic: the column, the block root of
  its group, the source, the parts metadata, and the message, each as
  it arrived. The client decodes and validates them, answers with
  `Service.judgePartialColumn`, and sends what the peer lacks through
  `Service.sendPartialColumn`. -/
  | partialColumn (column : Nat) (root : ByteArray) (source : PeerId)
      (metadata : Option ByteArray) (message : Option ByteArray)
  /-- The heartbeat's partial gossip on a column topic: these peers take
  partial messages there, and they get our parts metadata in place of
  an IHAVE (`partial-messages.md`, "Partial Message Gossip"). The client
  sends its metadata of each block it holds through
  `Service.sendPartialColumn`. -/
  | partialGossip (column : Nat) (peers : List PeerId)

/-- The answer of one chunk to an inbound request: the context bytes,
the `ForkDigest` of the chunk's epoch, and the SSZ. It answers `false`
when the stream failed or the answer holds the method's most chunks
(`Method.maxChunks`), and the client should stop then. The service never
sends a chunk past that cap. -/
abbrev Emit := ByteArray → ByteArray → Async Bool

/-- Our `MetaData`, as the client encodes it. The service answers Ping
with `seq`, and MetaData v3 and v2 with the bytes. `seq` is the
`seq_number` inside the bytes. -/
structure MetaData where
  seq : Nat
  /-- The SSZ of `MetaData` v3, 25 bytes. -/
  v3 : ByteArray
  /-- The SSZ of `MetaData` v2, 17 bytes. -/
  v2 : ByteArray

/-- The bytes have their widths. -/
def MetaData.wellFormed (m : MetaData) : Bool :=
  m.v3.size == metaDataV3Len && m.v2.size == metaDataV2Len

/-- How the client ends its answer to a block or column request. An
error ends the answer with one error chunk, after the chunks emitted
before it ("only the last chunk is allowed to have a non-zero error
code", phase0). The message goes out cut at the 256 bytes of
`ErrorMessage`. -/
inductive Ending where
  /-- The chunks emitted are the whole answer. -/
  | done
  /-- `1: InvalidRequest`: the request does not parse, or the client
  finds it invalid. -/
  | invalidRequest (message : String)
  /-- `2: ServerError`: the client failed to answer. -/
  | serverError (message : String)
  /-- `3: ResourceUnavailable`: the client does not keep the blocks or
  columns asked for ("SHOULD respond with error code
  `3: ResourceUnavailable`", phase0 "BeaconBlocksByRange v1"). -/
  | resourceUnavailable (message : String)

/-- The error chunk that ends an answer, if any. -/
def Ending.chunk? : Ending → Option Chunk
  | .done => none
  | .invalidRequest msg => some (errorChunk .invalidRequest msg)
  | .serverError msg => some (errorChunk .serverError msg)
  | .resourceUnavailable msg => some (errorChunk .resourceUnavailable msg)
where
  errorChunk (r : ReqResp.Result) (msg : String) : Chunk :=
    ⟨r, ByteArray.empty, msg.toUTF8.extract 0 Libp2p.Protocols.Constants.errorMessageLimit⟩

/-- The service's configuration. -/
structure Config where
  /-- The fork schedule and the slot timing. -/
  chain : Chain
  /-- Our first `Status`, its 92 bytes of SSZ. The service writes our
  digest over its first 4 bytes. The client keeps it current
  (`Service.setStatus`). -/
  status : ByteArray
  /-- Our first `MetaData`. The client keeps it current
  (`Service.setMetaData`). -/
  metaData : MetaData
  /-- The secp256k1 key: the libp2p identity and the ENR key. -/
  key : PrivKey
  /-- The IPv4 address the service binds and names in its ENR. -/
  ip : List Nat
  /-- The TCP port. 0 lets the system pick. -/
  tcpPort : Nat
  /-- The QUIC port, or `none` for no QUIC. QUIC is on by default:
  "All implementations MUST support the QUIC (UDP) libp2p transport"
  (phase0, beta.4). The default 0 lets the system pick, as `tcpPort` 0
  does, and the record names the bound port. -/
  quicPort : Option Nat := some 0
  /-- The discv5 UDP port. 0 lets the system pick. -/
  discPort : Nat
  /-- The boot records. -/
  bootEnrs : List Enr := []
  /-- Our subnets and our custody. -/
  advert : Advert
  /-- The peer count the discovery loop aims at. -/
  targetPeers : Nat := 16
  /-- The pause of the discovery loop. -/
  discoverEveryMs : Nat := 5000
  /-- The deadline of one request: Lighthouse's `RESP_TIMEOUT`, 10 s. -/
  requestTimeoutMs : Nat := 10000
  /-- Peer scoring with Lighthouse's profile (`Scoring`). The service
  starts it as Lighthouse does, at `SLOTS_PER_EPOCH` active validators
  and slot 0, and the client keeps it current (`Service.updateScores`).
  `false` runs the router unscored. -/
  scoring : Bool := true
  /-- The events. Must not park. -/
  onEvent : Event → BaseIO Unit := fun _ => pure ()
  /-- Our partial-messages choice on the column subnets (fulu
  `partial-columns/p2p-interface.md`). With `requests`, peers that can
  send partial columns send them in place of full sidecars, so the
  client must take `Event.partialColumn` and rebuild the columns. With
  `supports` alone, the client sends partial columns to peers that ask,
  and receives full sidecars. The default takes full sidecars only, so
  a client that cannot rebuild columns still gets every column. -/
  partialColumns : Gossipsub.Core.PartialOpts := {}
  /-- The client's answer to a request of one of `servedMethods`: the
  method and the request's bytes, within the method's bounds. It emits
  the chunks it has, in the order the method requires, and it names how
  the answer ends. A request that does not parse gets
  `.invalidRequest`. The default emits none, which the spec allows
  ("Clients MAY limit the number of blocks in the response"). For a
  method of `oneOrErrorMethods` with no chunk, the service then answers
  `ResourceUnavailable`. -/
  serve : PeerId → Method → ByteArray → Emit → Async Ending := fun _ _ _ _ => pure .done

/-- Milliseconds since the Unix epoch. -/
def wallMs : IO Nat := do
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat

/-- The fork digest of the wall-clock epoch. -/
def digestNow (c : Chain) : IO ByteArray := do
  return c.forkDigest (c.epochAt (← wallMs))

/-- The parts that every handler reaches: the host and the small state. -/
structure Base where
  config : Config
  host : Libp2p.Host.Host
  /-- Our `Status`, which the client keeps current (`setStatus`). Its
  first 4 bytes are our digest. -/
  status : OnceRef ByteArray
  /-- Our `MetaData`, which the client keeps current (`setMetaData`). -/
  metaData : OnceRef MetaData
  /-- The request slots of each peer: `MAX_CONCURRENT_REQUESTS` per
  protocol id (`Limiter`). -/
  limiters : OnceRef (List (PeerId × Limiter))
  /-- The Ping state of each peer, and the bans (`Peers`). Its clock is
  `IO.monoMsNow`. -/
  peers : OnceRef Peers
  tasks : TaskSet

namespace Base

/-- The limiter of a peer, made at its first request. -/
def limiterOf (b : Base) (peer : PeerId) : BaseIO Limiter := do
  if let some l := (← b.limiters.get).lookup peer then return l
  let l ← Limiter.new
  b.limiters.updateGet fun t =>
    match t.lookup peer with
    | some old => (old, t)
    | none => (l, (peer, l) :: t)

/-- Send one request and hand each chunk to `check` as it arrives.
`check` answers whether the read goes on, so the client verifies each
chunk before it consumes the next ("Before consuming the next response
chunk, the response reader SHOULD verify", deneb and fulu). A refused
chunk resets the stream. -/
def requestEach (b : Base) (peer : PeerId) (m : Method) (payload : Option ByteArray)
    (check : Chunk → Async Bool) : Async (Except ReqResp.Error Unit) := do
  let lim ← b.limiterOf peer
  let openTo := (Gossipsub.HostSeam.ofHost b.host).newStream peer
  ReqResp.requestPeer openTo lim m Clock.system b.config.requestTimeoutMs payload check

/-- Send one request and collect its chunks. -/
def request (b : Base) (peer : PeerId) (m : Method) (payload : Option ByteArray) :
    Async (Except ReqResp.Error (List Chunk)) := do
  let acc ← (OnceRef.new ([] : List Chunk) : BaseIO _)
  match ← b.requestEach peer m payload fun c => do
      (acc.update (c :: ·) : BaseIO Unit)
      return true with
  | .error e => return .error e
  | .ok () => return .ok (← (acc.get : BaseIO _)).reverse

/-- The payload of an answer of one success chunk. -/
def successOf : Except ReqResp.Error (List Chunk) → Option ByteArray
  | .ok [c] =>
    match c.result with
    | .success => some c.payload
    | _ => none
  | _ => none

/-- Say Goodbye with `reason`. The answer, zero chunks or one, has no
use here. -/
def goodbye (b : Base) (peer : PeerId) (reason : Nat) : Async Unit := do
  discard <| b.request peer goodbyeMethod (some (le64 reason))

/-- Act on a peer's `Status`, which the method's bounds hold at 92
bytes: report it, and end a peer of another fork. -/
def onStatus (b : Base) (peer : PeerId) (st : ByteArray) : Async Unit := do
  (b.config.onEvent (.status peer st) : BaseIO Unit)
  let ours ← (b.status.get : BaseIO ByteArray)
  if statusDigest st != statusDigest ours then
    b.goodbye peer Constants.goodbyeIrrelevantNetwork
    discard <| (b.host.closePeer peer : BaseIO Bool)

/-- Send our `Status`, the dialer's duty. -/
def sendStatus (b : Base) (peer : PeerId) : Async Unit := do
  let ours ← (b.status.get : BaseIO ByteArray)
  if let some st := successOf (← b.request peer statusMethod (some ours)) then b.onStatus peer st

/-- One success chunk with no context. -/
def plain (payload : ByteArray) : Chunk := ⟨.success, ByteArray.empty, payload⟩

/-- A responder over `serveStreaming`. -/
def handlerOf (b : Base) (m : Method)
    (respond : PeerId → Option ByteArray → (Chunk → Async (Except ReqResp.Error Unit)) → Async Unit) :
    Libp2p.Core.StreamHandler :=
  ReqResp.streamingHandler m Clock.system b.config.requestTimeoutMs fun ctx payload emit =>
    respond ctx.remotePeer payload emit

/-- The `ResourceUnavailable` chunk of a one-chunk method with no data. -/
def unavailable : Chunk :=
  ⟨.resourceUnavailable, ByteArray.empty, "no data".toUTF8⟩

/-- The handler of a method the client answers. -/
def serveMethod (b : Base) (m : Method) : Libp2p.Core.StreamHandler :=
  b.handlerOf m fun peer payload emit => do
    let sent ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
    let ending ← b.config.serve peer m (payload.getD ByteArray.empty) fun context ssz => do
      -- A slot under the cap, taken in one update: a chunk past the
      -- cap breaks the spec's bound, so it never goes out.
      let room ← (sent.updateGet fun n => if n < m.maxChunks then (true, n + 1) else (false, n) :
        BaseIO Bool)
      if !room then return false
      return (← emit ⟨.success, context, ssz⟩) matches .ok _
    match ending.chunk? with
    | some c => discard <| emit c
    | none =>
      -- A one-chunk method with no chunk gets the error code the spec
      -- asks for (`oneOrErrorMethods`).
      if oneOrErrorMethods.any (·.id == m.id) && (← (sent.get : BaseIO Nat)) == 0 then
        discard <| emit unavailable

/-- The handlers of the req/resp methods. -/
def handlers (b : Base) : List Libp2p.Core.StreamHandler :=
  [b.handlerOf statusMethod fun peer payload emit => do
      discard <| emit (plain (← (b.status.get : BaseIO ByteArray)))
      if let some st := payload then
        -- The answer goes first, so a Goodbye after it finds a peer
        -- that has our Status.
        (b.tasks.spawn (b.onStatus peer st) : BaseIO Unit),
   b.handlerOf pingMethod fun peer _ emit => do
      -- A Ping of the peer counts as our check of it too.
      let now ← (IO.monoMsNow : BaseIO Nat)
      (b.peers.update (·.pinged peer now) : BaseIO Unit)
      discard <| emit (plain (le64 (← (b.metaData.get : BaseIO MetaData)).seq)),
   b.handlerOf metadataV3Method fun _ _ emit => do
      discard <| emit (plain (← (b.metaData.get : BaseIO MetaData)).v3),
   b.handlerOf metadataV2Method fun _ _ emit => do
      discard <| emit (plain (← (b.metaData.get : BaseIO MetaData)).v2),
   b.handlerOf goodbyeMethod fun peer payload emit => do
      let reason := match payload with
        | some p => if p.size == 8 then le64At p 0 else 0
        | none => 0
      -- "The response MUST consist of a single `response_chunk`" (phase0,
      -- "Goodbye v1"). Lodestar answers 0 and expects one chunk back;
      -- Lighthouse answers nothing.
      discard <| emit (plain (le64 0))
      (b.config.onEvent (.goodbye peer reason) : BaseIO Unit)] ++
  servedMethods.map b.serveMethod

/-- The protocol ids the identify answer lists. -/
def servedIds : List String :=
  ([Identify.protocolId, Constants.meshsubV13Id, Constants.meshsubV12Id, Constants.meshsubId] ++
    ([statusMethod, goodbyeMethod, pingMethod, metadataV3Method, metadataV2Method] ++
      servedMethods).map (·.id)).map (·.toString)

/-- Report the host's sessions, and send `Status` on each outbound one.
A replaced session raises `disconnected` while the peer stays
connected, so the event waits for the last session. -/
def watchPeers (b : Base) : BaseIO Unit :=
  b.host.addNotifiee fun
    | .connected peer _ role _ => do
      let outbound := match role with
        | .initiator => true
        | .responder => false
      let now ← IO.monoMsNow
      b.peers.update (·.connect peer outbound now)
      b.config.onEvent (.connected peer outbound)
      if outbound then b.tasks.spawn (b.sendStatus peer)
    | .disconnected peer _ => do
      if !(← b.host.connected peer) then
        b.limiters.update (·.filter (·.1 != peer))
        b.peers.update (·.disconnect peer)
        b.config.onEvent (.disconnected peer)

/-- Dial the peer of a record, through its consensus addresses. -/
def dialRecord (b : Base) (r : Enr) : BaseIO Unit := do
  let .ok peer := r.peerId | return
  let .ok addrs := r.dialAddrs | return
  if addrs.isEmpty || peer == b.host.localPeer then return
  b.host.addAddrs peer addrs
  b.tasks.spawn (discard <| b.host.dialPeer peer)

/-- The discovery loop. Park: the timer wakes it, and so does `stop`,
which closes `stopping`. `partial`, as the IO loops are. -/
partial def discover (b : Base) (disc : Discv5.Node) (stopping : Chan Unit) : Async Unit := do
  let timer ← (Park.sleep b.config.discoverEveryMs false : BaseIO (Park Bool))
  if ← select #[Park.recv stopping (fun _ => true), timer] then return
  let peers ← (b.host.peers : BaseIO (List PeerId))
  if peers.length < b.config.targetPeers then
    let epoch := b.config.chain.epochAt (← (wallMs : IO Nat))
    let me := b.host.localPeer
    let table ← (b.peers.get : BaseIO Peers)
    let mono ← (IO.monoMsNow : BaseIO Nat)
    let wanted (r : Enr) : Bool :=
      sameDigest b.config.chain epoch r &&
        (match r.dialAddrs with | .ok (_ :: _) => true | _ => false) &&
        (match r.peerId with
         | .ok p => p != me && !peers.contains p && !table.banned p mono
         | .error _ => false)
    for r in ← disc.findPeers wanted (b.config.targetPeers - peers.length) do
      (b.dialRecord r : BaseIO Unit)
  b.discover disc stopping

/-- Ping one peer. A `seq_number` above the one we know brings a
MetaData v3 request, and its answer becomes `Event.metaData`. No
answer, or one that is not 8 bytes, becomes `Event.unresponsive`. -/
def ping (b : Base) (peer : PeerId) : Async Unit := do
  let ours := (← (b.metaData.get : BaseIO MetaData)).seq
  let some seq := (successOf (← b.request peer pingMethod (some (le64 ours)))).bind
      fun p => if p.size == 8 then some (le64At p 0) else none
    | (b.config.onEvent (.unresponsive peer) : BaseIO Unit)
  unless (← (b.peers.get : BaseIO Peers)).seqNews peer seq do return
  let some md := successOf (← b.request peer metadataV3Method none) | return
  (b.peers.update (·.setMeta peer seq) : BaseIO Unit)
  (b.config.onEvent (.metaData peer seq md) : BaseIO Unit)

/-- The pause of the liveness loop between two looks at the table. The
intervals are 15 s and 20 s, so a look each second keeps a Ping within
one second of its time. -/
def livenessTickMs : Nat := 1000

/-- The liveness loop: each tick, ping every peer that is due. Park: the
timer wakes it, and so does `stop`, which closes `stopping`. `partial`,
as the IO loops are. -/
partial def liveness (b : Base) (stopping : Chan Unit) : Async Unit := do
  let timer ← (Park.sleep livenessTickMs false : BaseIO (Park Bool))
  if ← select #[Park.recv stopping (fun _ => true), timer] then return
  let now ← (IO.monoMsNow : BaseIO Nat)
  let due ← (b.peers.updateGet (·.takeDue now) : BaseIO (List PeerId))
  for p in due do
    (b.tasks.spawn (b.ping p) : BaseIO Unit)
  b.liveness stopping

end Base

/-- The running service. -/
structure Service where
  base : Base
  gossip : Gossipsub.Node.Node
  disc : Discv5.Node
  /-- The addresses the host listens on. -/
  listenAddrs : List Multiaddr
  /-- `stop` closes it. -/
  stopping : Chan Unit
  /-- Our place in the fork schedule (`ForkState`). The fork loop alone
  changes it. -/
  forks : OnceRef ForkState
  /-- The kinds the client subscribed to. The fork loop carries them to
  each new digest. -/
  kinds : OnceRef (List Kind)
  /-- The active validator count and the slot of the last
  `updateScores`, for the score parameters of new topics. -/
  scoreInputs : OnceRef (Nat × Nat)
  /-- The first-delivery rewards of partial columns
  (`PartialColumns.Rewards`). -/
  partials : OnceRef PartialColumns.Rewards

/-- The column topics of every digest of the schedule from `epoch` on,
by name. -/
def columnTopicNames (c : Chain) (epoch : Nat) : Std.HashSet String :=
  (c.digestsFrom epoch).foldl (fun set d =>
    (List.range Constants.dataColumnSidecarSubnetCount).foldl
      (fun set i => set.insert (topicOf d (.dataColumnSidecar i))) set) {}

/-- The column of a column topic. -/
def columnOf? (topic : TopicId) : Option Nat :=
  match topicParse? topic.name with
  | some (_, .dataColumnSidecar i) => some i
  | _ => none

namespace Service

/-- The topic of a kind under `digest`. -/
def topicAt (digest : ByteArray) (k : Kind) : TopicId := ⟨topicOf digest k⟩

/-- Join the topic of a kind under `digest`, and give it the profile's
score parameters. The parameters of the start cover our first digest
only, so every later digest takes them here. -/
def join (s : Service) (digest : ByteArray) (k : Kind) : Async Bool := do
  let ok ← s.gossip.subscribeWait (topicAt digest k) fun _ => pure ()
  if ok && s.base.config.scoring then
    let (active, slot) ← (s.scoreInputs.get : BaseIO (Nat × Nat))
    if let some tp := Scoring.kindParams (Scoring.settings s.base.config.chain) active slot k then
      discard <| s.gossip.setTopicParams (topicAt digest k) (some tp)
  return ok

/-- Perform one duty of the fork loop at `epoch`. -/
def performFork (s : Service) (epoch : Nat) : ForkAction → Async Unit
  | .subscribe d => do
    for k in ← (s.kinds.get : BaseIO (List Kind)) do
      discard <| s.join d k
  | .switch old new => do
    let cfg := s.base.config
    (s.base.status.update (withDigest · new) : BaseIO Unit)
    -- The record names the new digest, the next fork, and `nfd`.
    discard <| (s.disc.updateEnr (advertPairs cfg.chain epoch cfg.advert) : BaseIO Bool)
    -- "Peers who propagate messages on the pre-fork topics MUST NOT be
    -- scored negatively": the pre-fork topics lose their parameters.
    for k in ← (s.kinds.get : BaseIO (List Kind)) do
      discard <| s.gossip.setTopicParams (topicAt old k) none
  | .unsubscribe d => do
    for k in ← (s.kinds.get : BaseIO (List Kind)) do
      discard <| s.gossip.unsubscribe (topicAt d k)

/-- One look of the fork loop at `epoch`: the transition and its duties. -/
def forkTick (s : Service) (epoch : Nat) : Async Unit := do
  let chain := s.base.config.chain
  let acts ← (s.forks.updateGet (ForkState.step chain epoch) : BaseIO (List ForkAction))
  for a in acts do s.performFork epoch a

/-- The pause of the fork loop between two looks at the clock. -/
def forkTickMs : Nat := 1000

/-- The fork loop: each tick, follow the fork schedule at the wall-clock
epoch. Park: the timer wakes it, and so does `stop`, which closes
`stopping`. `partial`, as the IO loops are. -/
partial def forkWatch (s : Service) : Async Unit := do
  let timer ← (Park.sleep forkTickMs false : BaseIO (Park Bool))
  if ← select #[Park.recv s.stopping (fun _ => true), timer] then return
  s.forkTick (s.base.config.chain.epochAt (← (wallMs : IO Nat)))
  s.forkWatch

/-- Lift an `Except` into `IO`, with the message for a failure. -/
private def orThrow {ε α : Type} (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error _ => throw (IO.userError s!"eth2: {what}")

/-- Start the service: the host and its handlers, the listeners, the
gossipsub node, and discv5 with our record. -/
def start (cfg : Config) : Async Service := do
  unless cfg.chain.wellFormed do
    throw (IO.userError "eth2: the fork schedule is not well formed (Chain.wellFormed)")
  unless cfg.status.size == statusLen do
    throw (IO.userError s!"eth2: the Status must have {statusLen} bytes")
  unless cfg.metaData.wellFormed do
    throw (IO.userError "eth2: the MetaData bytes do not have their widths")
  let pub ← orThrow "the key has no public form" cfg.key.toPublic
  let scalar ← if h : cfg.key.keyType = .secp256k1 then pure (cfg.key.secp256k1Scalar h)
    else throw (IO.userError "eth2: the key must be secp256k1, the key of ENR scheme v4")
  let noise ← orThrow "the Noise key does not generate" (← (Security.Noise.Config.generate cfg.key).run)
  let tls ← orThrow "the TLS certificate does not generate" (← Security.Tls.Config.generate cfg.key)
  -- The gater refuses a banned peer: at the dial, when the dial names it,
  -- and after the handshake, which proves an inbound peer's id.
  let peers ← (OnceRef.new ({} : Peers) : BaseIO _)
  let allowed (p : PeerId) : BaseIO Bool := do
    return !(← peers.get).banned p (← IO.monoMsNow)
  let gater : Libp2p.Core.ConnectionGater := {
    allowDial := fun p _ => match p with
      | some p => allowed p
      | none => pure true
    allowInbound := fun _ _ => pure true
    allowSecured := fun _ p _ _ => allowed p }
  -- The connection caps of Lighthouse (`service/mod.rs`,
  -- `with_max_established`): the target, plus `PEER_EXCESS_FACTOR` (0.1)
  -- and `PRIORITY_PEER_EXCESS` (0.2) of it, rounded up. Lighthouse allows
  -- one connection per peer. The host dedups a pair of crossed dials only
  -- after both handshakes, and a cap of one would make each side refuse
  -- the other's connection, so the cap is two.
  let (resources, _) ← (Libp2p.Host.Limits.manager
    { connections := (cfg.targetPeers * 13 + 9) / 10, connectionsPerPeer := 2 } : BaseIO _)
  let hostCfg : Libp2p.Host.Config := {
    identity := cfg.key
    gater
    resources
    transports := [Streams.Tcp.transport]
    securedTransports := if cfg.quicPort.isSome then [Libp2p.Quic.transport tls] else []
    security := [Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux, Libp2p.Mux.mplex] }
  let host ← orThrow "the host does not start" (← (Libp2p.Host.Host.new hostCfg : BaseIO _))
  let epoch := cfg.chain.epochAt (← wallMs)
  let digest := cfg.chain.forkDigest epoch
  let base : Base := {
    config := cfg, host
    status := ← OnceRef.new (withDigest cfg.status digest)
    metaData := ← OnceRef.new cfg.metaData
    limiters := ← OnceRef.new []
    peers
    tasks := ← TaskSet.new }
  for h in base.handlers do (host.setHandler h : BaseIO Unit)
  base.watchPeers
  -- Gossip: the payload path, and the held validation. The callback
  -- needs the node, which exists only after the start, so it reads it
  -- through a cell.
  let nodeRef ← (OnceRef.new (none : Option Gossipsub.Node.Node) : BaseIO _)
  let onValidate : Message → MessageId → PeerId → BaseIO Unit := fun m id src => do
    let some n ← nodeRef.get | return
    let some data ← n.payload id | return
    let some (_, kind) := topicParse? m.topic.name
      | discard <| n.report id src .reject
    match Snappy.decompress data Constants.maxPayloadSize with
    | .ok ssz => cfg.onEvent (.gossip kind id src ssz)
    | .error _ => discard <| n.report id src .reject
  let base0 := if cfg.scoring then
      Scoring.scoredParams cfg.chain digest cfg.chain.slotsPerEpoch 0
    else gossipParams cfg.chain
  -- The column topics of every digest ahead take the client's choice,
  -- so a fork needs no change of the router's parameters.
  let partialTopics :=
    Gossipsub.Core.PartialTopics.ofSet (columnTopicNames cfg.chain epoch) cfg.partialColumns
  let params := { base0 with partialTopics }
  -- Partial columns: the callbacks hand the bytes to the client, and
  -- `onEvent` does not park, so the gossipsub loop never waits.
  let partials ← (OnceRef.new ({} : PartialColumns.Rewards) : BaseIO _)
  let onPartial : PeerId → Gossipsub.Rpc.PartialMessage → BaseIO Unit := fun src pm => do
    let topic : TopicId := ⟨(pm.topicId.bind fun b => Bytes.toString? (Bytes.ofNatList b)).getD ""⟩
    let some column := columnOf? topic | return
    -- "Implementations MUST ignore unknown versions."
    let some root := (pm.groupId.map Bytes.ofNatList).bind PartialColumns.rootOf? | return
    cfg.onEvent (.partialColumn column root src (pm.partsMetadata.map Bytes.ofNatList)
      (pm.partialMessage.map Bytes.ofNatList))
  let onPartialGossip : TopicId → List PeerId → BaseIO Unit := fun topic peers => do
    let some column := columnOf? topic | return
    cfg.onEvent (.partialGossip column peers)
  let gossip ← (Gossipsub.Node.start (Gossipsub.HostSeam.ofHost host)
    { params
      maxRpcSize := Constants.gossipMaxMessageSize
      payloadId := some messageId
      onValidate, onPartial, onPartialGossip } : BaseIO _)
  (nodeRef.set (some gossip) : BaseIO Unit)
  -- The listeners.
  let tcpAt ← orThrow "the TCP address" (Enr.address .ip4 cfg.ip .tcp cfg.tcpPort)
  let tcp ← orThrow "the TCP listener does not start" (← host.startListening tcpAt)
  let quic ← match cfg.quicPort with
    | some p =>
      let quicAt ← orThrow "the QUIC address" (Enr.quicAddress .ip4 cfg.ip p)
      pure [← orThrow "the QUIC listener does not start" (← host.startListening quicAt)]
    | none => pure []
  let listenAddrs := tcp :: quic
  -- The identify answer names the listeners, which exist only now. No
  -- connection comes before them: the first dial is the boot dial below.
  (host.setHandler (Identify.respondHandler pub (listenAddrs.map (·.toBytes)) Base.servedIds
    "leanp2p") : BaseIO Unit)
  -- Discovery, with the consensus fields and the libp2p ports in our
  -- record. discv5 writes `ip` and `udp` itself.
  let advert := advertPairs cfg.chain epoch cfg.advert
  let ports ← orThrow "the ENR ports" (Enr.consensusPairs listenAddrs)
  let disc ← Discv5.Node.start scalar cfg.ip cfg.discPort (advert ++ ports)
  for r in cfg.bootEnrs do
    (disc.addEnr r : BaseIO Unit)
    (base.dialRecord r : BaseIO Unit)
  let stopping ← (Chan.new 1 (by decide) : BaseIO (Chan Unit))
  (base.tasks.spawn (base.discover disc stopping) : BaseIO Unit)
  (base.tasks.spawn (base.liveness stopping) : BaseIO Unit)
  let s : Service := {
    base, gossip, disc, listenAddrs, stopping
    forks := ← OnceRef.new { current := digest }
    kinds := ← OnceRef.new []
    scoreInputs := ← OnceRef.new (cfg.chain.slotsPerEpoch, 0)
    partials }
  -- The first look at the schedule runs now, so a fork one epoch away
  -- finds its topics joined before the first subscribe.
  s.forkTick epoch
  (base.tasks.spawn s.forkWatch : BaseIO Unit)
  return s

/-- The topic of a kind under our digest. -/
def topic (s : Service) (k : Kind) : BaseIO TopicId := do
  return topicAt (← s.forks.get).current k

/-- Subscribe to a kind, under our digest, and under the next digest
once the fork is a lead away. The fork loop carries the kind to each
later digest. The messages arrive as `Event.gossip`. The post parks
while the gossipsub node's control queue is full
(`Node.subscribeWait`), since a consensus node subscribes to about 200
topics at once. `false` once the node stops. -/
def subscribe (s : Service) (k : Kind) : Async Bool := do
  (s.kinds.update fun ks => if ks.contains k then ks else ks ++ [k] : BaseIO Unit)
  let st ← (s.forks.get : BaseIO ForkState)
  let ok ← s.join st.current k
  if let some next := st.next then discard <| s.join next k
  return ok

/-- Leave a kind, under every digest we hold. -/
def unsubscribe (s : Service) (k : Kind) : Async Bool := do
  (s.kinds.update (·.filter (· != k)) : BaseIO Unit)
  let st ← (s.forks.get : BaseIO ForkState)
  let digests := st.current :: (st.next.toList ++ st.retiring.map (·.1))
  digests.allM fun d => s.gossip.unsubscribe (topicAt d k)

/-- Bring the chain-dependent score parameters up to date: the block, the
aggregate, and every attestation subnet, for `active` validators at
`slot`. Lighthouse calls this every 60 s (`update_gossipsub_parameters`).
`false` once the node stops, or with scoring off. -/
def updateScores (s : Service) (active slot : Nat) : Async Bool := do
  if !s.base.config.scoring then return false
  (s.scoreInputs.set (active, slot) : BaseIO Unit)
  let st := Scoring.settings s.base.config.chain
  let (block, aggregate, attestation) := Scoring.dynamicParams st active slot
  let kinds : List (Kind × Gossipsub.Score.TopicParams) :=
    [(.beaconBlock, block), (.beaconAggregateAndProof, aggregate)] ++
      (List.range Constants.attestationSubnetCount).map fun i => (.beaconAttestation i, attestation)
  kinds.allM fun (k, tp) => do s.gossip.setTopicParams (← s.topic k) (some tp)

/-- Answer a held message. -/
def report (s : Service) (id : MessageId) (source : PeerId) (v : Gossipsub.Core.Validation) :
    BaseIO Bool :=
  s.gossip.report id source v

/-- Publish the SSZ of a message of `k`: the service compresses it. -/
def publish (s : Service) (k : Kind) (ssz : ByteArray) : IO Bool := do
  match Snappy.compress ssz with
  | .ok data => s.gossip.publish (← s.topic k) data
  | .error _ => return false

/-- The peers to offer partial messages on the topic of `column`, each
with its request flag (`Node.partialPeers`). The full
`DataColumnSidecar` goes through `publish`. The router skips the peers
that requested partial messages when it sends it, as the spec asks
("Avoid forwarding the full `DataColumnSidecar` message to peers that
requested partial messages"). `none` when the node does not answer. -/
def partialColumnPeers (s : Service) (column : Nat) :
    Async (Option (List (PeerId × Bool))) := do
  s.gossip.partialPeers (← (s.topic (.dataColumnSidecar column) : BaseIO TopicId))

/-- Send a partial message on the topic of `column` to `peer`: the group
of the block `root`, and the client's parts metadata and message, each
the SSZ the client encodes. The router sends the metadata alone to a
peer that only supports partial messages there, and nothing to a peer
that takes none. Each call only queues. `false` when the node does not
take it. -/
def sendPartialColumn (s : Service) (peer : PeerId) (root : ByteArray) (column : Nat)
    (metadata message : Option ByteArray) : BaseIO Bool := do
  let topic ← s.topic (.dataColumnSidecar column)
  s.gossip.sendPartial peer
    { topicId := some (Bytes.toNatList topic.name.toUTF8)
      groupId := some (Bytes.toNatList (PartialColumns.groupIdOf root))
      partialMessage := message.map Bytes.toNatList
      partsMetadata := metadata.map Bytes.toNatList }

/-- The client's answer to a partial column (`Event.partialColumn`).
Invalid data costs the peer an invalid delivery ("On receiving invalid
data, the client should report to gossipsub an invalid message
delivery"). Valid data earns the first-delivery reward once per peer,
block, and column (`PartialColumns.Rewards.earn`), as the spec asks:
"Clients SHOULD limit the rate at which a peer gets the first message
delivery reward". -/
def judgePartialColumn (s : Service) (peer : PeerId) (root : ByteArray) (column : Nat)
    (valid : Bool) : BaseIO Bool := do
  let topic ← s.topic (.dataColumnSidecar column)
  if !valid then return ← s.gossip.judgePartial peer topic false
  let earns ← s.partials.updateGet (·.earn peer root column)
  if earns then s.gossip.judgePartial peer topic true else return true

/-- Our `Status`, its 92 bytes of SSZ, from the client's chain. The
service writes our digest over its first 4 bytes, the digest our topics
carry. It takes the digest from the stored `Status` in the same update,
so a fork switch between two calls cannot leave the old digest.
`false`, and no change, for another width. -/
def setStatus (s : Service) (status : ByteArray) : BaseIO Bool := do
  if status.size != statusLen then return false
  s.base.status.update fun old => withDigest status (statusDigest old)
  return true

/-- Our `MetaData`. Peers learn of the change from our next Ping
answer. `false`, and no change, when the bytes do not have their
widths. -/
def setMetaData (s : Service) (m : MetaData) : BaseIO Bool := do
  if !m.wellFormed then return false
  s.base.metaData.set m
  return true

/-- Send one request to a peer, and collect its chunks. -/
def request (s : Service) (peer : PeerId) (m : Method) (payload : Option ByteArray) :
    Async (Except ReqResp.Error (List Chunk)) :=
  s.base.request peer m payload

/-- Send one request to a peer, and check each chunk before the next.
A `check` that answers `false` ends the read and resets the stream. -/
def requestEach (s : Service) (peer : PeerId) (m : Method) (payload : Option ByteArray)
    (check : Chunk → Async Bool) : Async (Except ReqResp.Error Unit) :=
  s.base.requestEach peer m payload check

/-- The connected peers. -/
def peers (s : Service) : BaseIO (List PeerId) := s.base.host.peers

/-- Say Goodbye with `reason`, and end the peer's connections. -/
def disconnect (s : Service) (peer : PeerId) (reason : Nat) : Async Unit := do
  s.base.goodbye peer reason
  discard <| (s.base.host.closePeer peer : BaseIO Bool)

/-- Ban a peer for `ms` milliseconds, `Constants.banMs` by default. The
ban comes first, so a redial in the meantime meets the gater. Then the
peer gets Goodbye with `Constants.goodbyeBanned`, and its connections
end. The gater refuses its dials and its handshakes until the ban ends.
Whether a peer earns a ban is the client's choice: penalties are
scoring, and they stay with the client. -/
def ban (s : Service) (peer : PeerId) (ms : Nat := Constants.banMs) : Async Unit := do
  let now ← (IO.monoMsNow : BaseIO Nat)
  (s.base.peers.update (·.ban peer now (now + ms)) : BaseIO Unit)
  s.disconnect peer Constants.goodbyeBanned

/-- Whether a peer is banned now. -/
def isBanned (s : Service) (peer : PeerId) : BaseIO Bool := do
  return (← s.base.peers.get).banned peer (← IO.monoMsNow)

/-- Our record. -/
def localEnr (s : Service) : BaseIO Enr := s.disc.localEnr

/-- Stop: Goodbye with reason 1 to every peer, then the loops, the
gossipsub node, discv5, the host, and the task set, in that order. -/
def stop (s : Service) : Async Unit := do
  (s.stopping.close : BaseIO Unit)
  let bye ← (TaskSet.new : BaseIO TaskSet)
  for p in ← s.peers do
    (bye.spawn (s.base.goodbye p Constants.goodbyeClientShutdown) : BaseIO Unit)
  bye.joinAll
  s.gossip.stop
  s.disc.stop
  s.base.host.close
  s.base.tasks.joinAll

end Service

end Libp2p.Eth2
