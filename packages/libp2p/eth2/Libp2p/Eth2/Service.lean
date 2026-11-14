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

/-!
# The consensus network service

One value that a consensus client runs for its networking: the host,
the gossipsub node, the discv5 node, and the req/resp methods, wired
the way the consensus spec asks. The client keeps the chain. It answers
the gossip validations and the block and column requests, and it reads
the events.

## What the service does by itself

* **Transports.** TCP with Noise and yamux or mplex, and QUIC v1 when
  the config has a QUIC port. The host ranks QUIC first
  (`Policy.quicFirst`), as phase0 "Transport" asks.
* **The identity.** One secp256k1 key is the libp2p identity and the
  ENR key. Peers derive our peer id from our ENR (`Enr.peerId`), so the
  two must be one key.
* **Status.** "The dialing client MUST send a `Status` request upon
  connection." The service sends ours on each outbound connection, and
  it answers each inbound one with ours. A peer whose `fork_digest` is
  not ours gets Goodbye with reason 2, and its connection ends ("SHOULD
  immediately disconnect"). The other check of the spec, a finalized
  root outside our chain, needs the chain, so it stays with the client.
* **Ping, MetaData, Goodbye.** The service answers Ping with our
  `MetaData.seq_number`, and MetaData v3 and v2 with ours. Each Goodbye
  of a peer becomes an event. At `stop`, the service says Goodbye with
  reason 1 to every peer.
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

## Concurrency

Every task belongs to the service's task set, and `stop` joins it
(root §4.1). The discovery loop and the liveness loop park on their
timers and on `stopping`, which `stop` closes. The host notifiee and the gossipsub validation
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
  /-- A peer's `Status`, from either side of the handshake. -/
  | status (peer : PeerId) (s : Status)
  /-- A held gossip message: its kind, its message id, its propagation
  source, and its SSZ, decompressed. The client answers with `report`. -/
  | gossip (kind : Kind) (id : MessageId) (source : PeerId) (ssz : ByteArray)
  /-- A peer said Goodbye. -/
  | goodbye (peer : PeerId) (reason : Nat)
  /-- A peer's Ping answer named a newer `seq_number`, and its MetaData v3
  arrived. -/
  | metaData (peer : PeerId) (md : MetaData)
  /-- A peer did not answer our Ping. The spec lets the client end the
  connection ("MAY disconnect"); the service leaves that to the client
  (`Service.disconnect`). -/
  | unresponsive (peer : PeerId)

/-- A block or column request that a peer sent us. -/
inductive Inbound where
  | blocksByRange (startSlot count : Nat)
  | blocksByRoot (roots : List ByteArray)
  | columnsByRange (startSlot count : Nat) (columns : List Nat)
  /-- The raw SSZ of a `DataColumnsByRootIdentifiers` list. -/
  | columnsByRoot (ssz : ByteArray)

/-- The answer of one chunk to an inbound request: the context bytes,
the `ForkDigest` of the chunk's epoch, and the SSZ. It answers `false`
when the stream failed, and the client should stop then. -/
abbrev Emit := ByteArray → ByteArray → Async Bool

/-- The service's configuration. -/
structure Config where
  chain : Chain
  /-- The secp256k1 key: the libp2p identity and the ENR key. -/
  key : PrivKey
  /-- The IPv4 address the service binds and names in its ENR. -/
  ip : List Nat
  /-- The TCP port. 0 lets the system pick. -/
  tcpPort : Nat
  /-- The QUIC port, or `none` for no QUIC. -/
  quicPort : Option Nat := none
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
  /-- The events. Must not park. -/
  onEvent : Event → BaseIO Unit := fun _ => pure ()
  /-- The client's answer to a block or column request. It emits the
  chunks it has, in the order the method requires. The default emits
  none, which the spec allows ("Clients MAY limit the number of blocks
  in the response"). -/
  serve : PeerId → Inbound → Emit → Async Unit := fun _ _ _ => pure ()

/-- Milliseconds since the Unix epoch. -/
def wallMs : IO Nat := do
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat

/-- The fork digest of the wall-clock epoch. -/
def digestNow (c : Chain) : IO ByteArray := do
  match c.forkDigest (c.epochAt (← wallMs)) with
  | .ok d => return d
  | .error _ => throw (IO.userError "eth2: the SHA-256 of the fork digest failed")

/-- The parts that every handler reaches: the host and the small state. -/
structure Base where
  config : Config
  host : Libp2p.Host.Host
  /-- Our `Status`, which the client keeps current (`setStatus`). -/
  status : OnceRef Status
  /-- Our `MetaData.seq_number`. -/
  metaSeq : OnceRef Nat
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

/-- Send one request and collect its chunks. -/
def request (b : Base) (peer : PeerId) (m : Method) (payload : Option ByteArray) :
    Async (Except ReqResp.Error (List Chunk)) := do
  let acc ← (OnceRef.new ([] : List Chunk) : BaseIO _)
  let lim ← b.limiterOf peer
  let openTo := (Gossipsub.HostSeam.ofHost b.host).newStream peer
  match ← ReqResp.requestPeer openTo lim m Clock.system b.config.requestTimeoutMs payload
      (fun c => (acc.update (c :: ·) : BaseIO Unit)) with
  | .error e => return .error e
  | .ok () => return .ok (← (acc.get : BaseIO _)).reverse

/-- The payload of an answer of one success chunk. -/
def successOf : Except ReqResp.Error (List Chunk) → Option ByteArray
  | .ok [c] =>
    match c.result with
    | .success => some c.payload
    | _ => none
  | _ => none

/-- Say Goodbye with `reason`. The peer answers nothing. -/
def goodbye (b : Base) (peer : PeerId) (reason : Nat) : Async Unit := do
  discard <| b.request peer goodbyeMethod (some (Chain.le64 reason))

/-- Act on a peer's `Status`: report it, and end a peer of another
fork. -/
def onStatus (b : Base) (peer : PeerId) (st : Status) : Async Unit := do
  (b.config.onEvent (.status peer st) : BaseIO Unit)
  let ours ← (b.status.get : BaseIO Status)
  if st.forkDigest != ours.forkDigest then
    b.goodbye peer Constants.goodbyeIrrelevantNetwork
    discard <| (b.host.closePeer peer : BaseIO Bool)

/-- Send our `Status`, the dialer's duty. -/
def sendStatus (b : Base) (peer : PeerId) : Async Unit := do
  let ours ← (b.status.get : BaseIO Status)
  let answer ← b.request peer statusMethod (some ours.encode)
  if let some st := (successOf answer).bind Status.decode? then b.onStatus peer st

/-- Our `MetaData`. -/
def metaData (b : Base) : BaseIO MetaData := do
  return { seqNumber := ← b.metaSeq.get, attnets := b.config.advert.attnets,
           syncnets := b.config.advert.syncnets, custodyGroupCount := b.config.advert.cgc }

/-- One success chunk with no context. -/
def plain (payload : ByteArray) : Chunk := ⟨.success, ByteArray.empty, payload⟩

/-- A responder over `serveStreaming`. -/
def handlerOf (b : Base) (m : Method)
    (respond : PeerId → Option ByteArray → (Chunk → Async (Except ReqResp.Error Unit)) → Async Unit) :
    Libp2p.Core.StreamHandler :=
  ReqResp.streamingHandler m Clock.system b.config.requestTimeoutMs fun ctx payload emit =>
    respond ctx.remotePeer payload emit

/-- The `InvalidRequest` chunk of a request that does not parse. -/
def invalid : Chunk := ⟨.invalidRequest, ByteArray.empty, "malformed request".toUTF8⟩

/-- The inbound request of a method's payload, when it parses. -/
def inboundOf (m : Method) (p : ByteArray) : Option Inbound :=
  if m.id == blocksByRangeMethod.id then
    if p.size == 24 then some (.blocksByRange (le64At p 0) (le64At p 8)) else none
  else if m.id == blocksByRootMethod.id then
    if p.size % 32 == 0 then
      some (.blocksByRoot ((List.range (p.size / 32)).map fun i => p.extract (32 * i) (32 * i + 32)))
    else none
  else if m.id == columnsByRangeMethod.id then
    if 20 ≤ p.size && (p.size - 20) % 8 == 0 && le64At (p.extract 16 20 ++ ⟨#[0, 0, 0, 0]⟩) 0 == 20 then
      some (.columnsByRange (le64At p 0) (le64At p 8)
        ((List.range ((p.size - 20) / 8)).map fun i => le64At p (20 + 8 * i)))
    else none
  else if m.id == columnsByRootMethod.id then some (.columnsByRoot p)
  else none

/-- The handlers of the req/resp methods. -/
def handlers (b : Base) : List Libp2p.Core.StreamHandler :=
  let serveMethod (m : Method) := b.handlerOf m fun peer payload emit => do
    match inboundOf m (payload.getD ByteArray.empty) with
    | none => discard <| emit invalid
    | some req =>
      b.config.serve peer req fun context ssz => do
        return (← emit ⟨.success, context, ssz⟩) matches .ok _
  [b.handlerOf statusMethod fun peer payload emit => do
      discard <| emit (plain (← (b.status.get : BaseIO Status)).encode)
      if let some st := payload.bind Status.decode? then
        -- The answer goes first, so a Goodbye after it finds a peer
        -- that has our Status.
        (b.tasks.spawn (b.onStatus peer st) : BaseIO Unit),
   b.handlerOf pingMethod fun peer _ emit => do
      -- A Ping of the peer counts as our check of it too.
      let now ← (IO.monoMsNow : BaseIO Nat)
      (b.peers.update (·.pinged peer now) : BaseIO Unit)
      discard <| emit (plain (Chain.le64 (← (b.metaSeq.get : BaseIO Nat)))),
   b.handlerOf metadataV3Method fun _ _ emit => do
      discard <| emit (plain (← b.metaData).encodeV3),
   b.handlerOf metadataV2Method fun _ _ emit => do
      discard <| emit (plain (← b.metaData).encodeV2),
   b.handlerOf goodbyeMethod fun peer payload _ => do
      let reason := match payload with
        | some p => if p.size == 8 then le64At p 0 else 0
        | none => 0
      (b.config.onEvent (.goodbye peer reason) : BaseIO Unit),
   serveMethod blocksByRangeMethod,
   serveMethod blocksByRootMethod,
   serveMethod columnsByRangeMethod,
   serveMethod columnsByRootMethod]

/-- The protocol ids the identify answer lists. -/
def servedIds : List String :=
  [Identify.protocolId, Constants.meshsubV13Id, Constants.meshsubV12Id, Constants.meshsubId,
   statusMethod.id, goodbyeMethod.id, pingMethod.id, metadataV3Method.id, metadataV2Method.id,
   blocksByRangeMethod.id, blocksByRootMethod.id, columnsByRangeMethod.id,
   columnsByRootMethod.id].map (·.toString)

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
  let ours ← (b.metaSeq.get : BaseIO Nat)
  let some seq := (successOf (← b.request peer pingMethod (some (Chain.le64 ours)))).bind
      fun p => if p.size == 8 then some (le64At p 0) else none
    | (b.config.onEvent (.unresponsive peer) : BaseIO Unit)
  unless (← (b.peers.get : BaseIO Peers)).seqNews peer seq do return
  let some md := (successOf (← b.request peer metadataV3Method none)).bind MetaData.decodeV3?
    | return
  (b.peers.update (·.setMeta peer md.seqNumber) : BaseIO Unit)
  (b.config.onEvent (.metaData peer md) : BaseIO Unit)

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

namespace Service

/-- Lift an `Except` into `IO`, with the message for a failure. -/
private def orThrow {ε α : Type} (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error _ => throw (IO.userError s!"eth2: {what}")

/-- Start the service: the host and its handlers, the listeners, the
gossipsub node, and discv5 with our record. -/
def start (cfg : Config) : Async Service := do
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
  let hostCfg : Libp2p.Host.Config := {
    identity := cfg.key
    gater
    transports := [Streams.Tcp.transport]
    securedTransports := if cfg.quicPort.isSome then [Libp2p.Quic.transport tls] else []
    security := [Security.Noise.securityProtocol noise]
    muxers := [Libp2p.Mux.yamux, Libp2p.Mux.mplex] }
  let host ← orThrow "the host does not start" (← (Libp2p.Host.Host.new hostCfg : BaseIO _))
  let epoch := cfg.chain.epochAt (← wallMs)
  let digest ← orThrow "the fork digest fails" (cfg.chain.forkDigest epoch)
  -- The genesis checkpoint has the zero root (phase0 "Status v1"), until
  -- the client's first `setStatus`.
  let zero : ByteArray := ⟨Array.replicate 32 0⟩
  let base : Base := {
    config := cfg, host
    status := ← OnceRef.new ⟨digest, zero, 0, zero, 0, 0⟩
    metaSeq := ← OnceRef.new 0
    limiters := ← OnceRef.new []
    peers
    tasks := ← TaskSet.new }
  for h in base.handlers do (host.setHandler h : BaseIO Unit)
  (host.setHandler (Identify.respondHandler pub [] Base.servedIds "leanp2p") : BaseIO Unit)
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
  let gossip ← (Gossipsub.Node.start (Gossipsub.HostSeam.ofHost host)
    { params := gossipParams cfg.chain
      maxRpcSize := Constants.gossipMaxMessageSize
      payloadId := some messageId
      onValidate } : BaseIO _)
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
  -- Discovery, with the consensus fields and the libp2p ports in our
  -- record. discv5 writes `ip` and `udp` itself.
  let advert ← orThrow "the ENR fields" (advertPairs cfg.chain epoch cfg.advert)
  let ports ← orThrow "the ENR ports" (Enr.consensusPairs listenAddrs)
  let disc ← Discv5.Node.start scalar cfg.ip cfg.discPort (advert ++ ports)
  for r in cfg.bootEnrs do
    (disc.addEnr r : BaseIO Unit)
    (base.dialRecord r : BaseIO Unit)
  let stopping ← (Chan.new 1 (by decide) : BaseIO (Chan Unit))
  (base.tasks.spawn (base.discover disc stopping) : BaseIO Unit)
  (base.tasks.spawn (base.liveness stopping) : BaseIO Unit)
  return { base, gossip, disc, listenAddrs, stopping }

/-- The topic of a kind under our digest now. -/
def topic (s : Service) (k : Kind) : IO TopicId := do
  return ⟨topicOf (← digestNow s.base.config.chain) k⟩

/-- Subscribe to a kind. The messages arrive as `Event.gossip`. The post
parks while the gossipsub node's control queue is full
(`Node.subscribeWait`), since a consensus node subscribes to about 200
topics at once. `false` once the node stops. -/
def subscribe (s : Service) (k : Kind) : Async Bool := do
  s.gossip.subscribeWait (← s.topic k) fun _ => pure ()

/-- Answer a held message. -/
def report (s : Service) (id : MessageId) (source : PeerId) (v : Gossipsub.Core.Validation) :
    BaseIO Bool :=
  s.gossip.report id source v

/-- Publish the SSZ of a message of `k`: the service compresses it. -/
def publish (s : Service) (k : Kind) (ssz : ByteArray) : IO Bool := do
  match Snappy.compress ssz with
  | .ok data => s.gossip.publish (← s.topic k) data
  | .error _ => return false

/-- Our `Status` from the client's chain. The digest is the wall-clock
one. -/
def setStatus (s : Service) (finalizedRoot : ByteArray) (finalizedEpoch : Nat)
    (headRoot : ByteArray) (headSlot earliestAvailableSlot : Nat) : IO Unit := do
  let forkDigest ← digestNow s.base.config.chain
  s.base.status.set { forkDigest, finalizedRoot, finalizedEpoch, headRoot, headSlot, earliestAvailableSlot }

/-- Send one request to a peer. -/
def request (s : Service) (peer : PeerId) (m : Method) (payload : Option ByteArray) :
    Async (Except ReqResp.Error (List Chunk)) :=
  s.base.request peer m payload

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
