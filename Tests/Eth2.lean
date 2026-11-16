import Tests.Support
import Libp2p.Eth2

/-!
# eth2 suite

The suite checks `libp2p/eth2` in this order:
- partial columns: the group ID, the reward rule, and two services that
  carry the client's bytes
- the fork schedule that the client hands in, and the record that a
  Lighthouse node of a devnet published
- the message id, against SHA-256 values that Python's `hashlib`
  computed from the spec's formula
- the req/resp methods and the fixed places the service reads
- the score profile, the fork loop, and the peer table
- two services over loopback: the dial from a boot record, the
  `Status` handshake, gossip with the held validation, the requests the
  client serves, MetaData, Ping, Goodbye, and bans
- the start refusals, a fork on a live service, the connection cap, and
  the responder's rate limit

The devnet values are the shadow node's (`etheorem-shadow-node` at
`8cd3247`, `helper/tests/fixtures`): the digest `8049f250`, and the
record of its Lighthouse node. The service treats every payload as
opaque bytes, so the checks of the services use filler bytes. Where a
check plays the client, it writes the few request fields it needs.
-/

set_option autoImplicit false

namespace Tests.Eth2

open Conc Libp2p.Eth2 Libp2p.Identity

private def hex (s : String) : ByteArray := (Bytes.ofHex? s).getD .empty

private def expectOk {ε α : Type} (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error _ => throw (IO.userError s!"{what} failed")

/-! ## The fork schedule and the devnet record -/

/-- The devnet's digest. -/
private def devnetDigest : ByteArray := hex "8049f250"

/-- The devnet's `ENRForkID`: the digest, Fulu's version as the next
version, and `FAR_FUTURE_EPOCH`. -/
private def devnetForkId : ByteArray := hex "8049f25070000038ffffffffffffffff"

/-- The record of a Lighthouse node of the devnet. -/
private def devnetEnr : String :=
  "enr:-NO4QEamopaXI3y7x4t2Kiir5IR2VxQSTZaH1QSKvsGH3rnBLdpFNQP_-dMWVqyrQakXBc0Ad5yy-W0cce1UHhEKgmMHh2F0dG5ldHOIgAEAAAAAAACDY2djgYCEZXRoMpCASfJQcAAAOP__________gmlkgnY0gmlwhKwQAA2DbmZkhAAAAACEcXVpY4IjKYlzZWNwMjU2azGhAtAWrNSOtz-KzskCSwPbP21-C9qVUN1FCgogvYX0EBtRiHN5bmNuZXRzD4N0Y3CCIyiDdWRwgiMo"

/-- A schedule entry at `epoch` with the filler digest `d d d d`. The
service compares digests and never computes one. -/
private def entry (epoch : Nat) (d : UInt8) : ForkEntry :=
  { epoch, digest := ⟨#[d, d, d, d]⟩, enrForkId := ⟨#[d, d, d, d] ++ Array.replicate 12 0⟩ }

/-- The devnet's schedule at mainnet timing, with later entries. -/
private def devnetChain (time : Nat := 1700000000) (later : List ForkEntry := []) : Chain :=
  { schedule := { epoch := 0, digest := devnetDigest, enrForkId := devnetForkId } :: later
    slotDurationMs := 12000, slotsPerEpoch := 32, genesisTime := time }

private def chainChecks (r : Runner) : IO Unit := do
  let c := devnetChain
  r.check "eth2: the devnet schedule is well formed" c.wellFormed
  r.check "eth2: the digest at epoch 0 is the entry's" (c.forkDigest 0 == devnetDigest)
  r.check "eth2: no fork follows"
    (c.nextForkEpoch 0 == Constants.farFutureEpoch && c.nextForkDigest 0 == ⟨#[0, 0, 0, 0]⟩)
  let rec_ ← expectOk "the devnet ENR" (Enr.ofText? devnetEnr)
  r.check "eth2: Lighthouse's record carries the devnet digest" (forkDigest? rec_ == some devnetDigest)
  r.check "eth2: Lighthouse's ENRForkID is the devnet's byte for byte"
    (enrForkId? rec_ == some (c.enrForkId 0))
  r.check "eth2: Lighthouse's nfd is ours" (bytesOf? rec_ nfdKey == some (c.nextForkDigest 0))
  r.check "eth2: the record names a supernode's custody" (cgc? rec_ == some 128)
  r.check "eth2: the record is of our fork" (sameFork c 0 rec_ && sameDigest c 0 rec_)
  r.check "eth2: the record has a dial address"
    (match rec_.dialAddrs with | .ok (_ :: _) => true | _ => false)
  -- A later entry, a Blob-Parameters-Only fork for one: the next fork,
  -- its digest from its epoch on, and the `nfd` before it.
  let bpo := devnetChain (later := [entry 5 0xaa])
  r.check "eth2: a later entry is the next fork" (bpo.nextForkEpoch 0 == 5 && bpo.nextForkEpoch 4 == 5)
  r.check "eth2: the digest changes at the entry's epoch"
    (bpo.forkDigest 4 == devnetDigest && bpo.forkDigest 5 == ⟨#[0xaa, 0xaa, 0xaa, 0xaa]⟩)
  r.check "eth2: the nfd before the entry is its digest" (bpo.nextForkDigest 0 == bpo.forkDigest 5)
  r.check "eth2: the digests from an epoch on"
    (bpo.digestsFrom 0 == [devnetDigest, bpo.forkDigest 5] && bpo.digestsFrom 5 == [bpo.forkDigest 5])
  r.check "eth2: an empty schedule is refused" (!{ c with schedule := [] }.wellFormed)
  r.check "eth2: a schedule that starts after epoch 0 is refused"
    (!{ c with schedule := [entry 1 1] }.wellFormed)
  r.check "eth2: a schedule out of order is refused"
    (!{ c with schedule := [entry 0 1, entry 7 2, entry 7 3] }.wellFormed)
  r.check "eth2: a digest of 3 bytes is refused"
    (!{ c with schedule := [{ entry 0 1 with digest := ⟨#[1, 1, 1]⟩ }] }.wellFormed)
  r.check "eth2: epoch 1 starts 384 s after genesis, and epoch 0 holds before genesis"
    (c.epochAt (1700000000 * 1000 + 384000) == 1 && c.epochAt (1700000000 * 1000 + 383999) == 0 &&
      c.epochAt 0 == 0)

/-! ## The message id -/

private def topic : String := "/eth2/8049f250/beacon_block/ssz_snappy"

private def messageIdChecks (r : Runner) : IO Unit := do
  r.check "eth2: data that does not decompress takes the invalid domain"
    (messageIdBytes topic ⟨#[0xff, 0xff, 0xff]⟩ == some (hex "cdeedbbf61c3f27499d55d88a971e19d2e1da339"))
  let raw := "hello consensus".toUTF8
  let data ← expectOk "snappy compress" (Snappy.compress raw)
  r.check "eth2: compressed data takes the valid domain over the raw bytes"
    (messageIdBytes topic data == some (hex "b4ba60d2bba298249bed48c66fb8611d872e9dbc"))
  r.check "eth2: the message id has 20 bytes"
    ((messageId topic data).map (·.bytes.length) == some 20)
  r.check "eth2: the topic enters the id"
    (messageIdBytes "/eth2/8049f250/voluntary_exit/ssz_snappy" data != messageIdBytes topic data)

/-! ## The methods -/

private def methodChecks (r : Runner) : IO Unit := do
  let st : ByteArray := ⟨Array.replicate statusLen 7⟩
  r.check "eth2: the digest of a Status is its first 4 bytes"
    (statusDigest (withDigest st devnetDigest) == devnetDigest)
  r.check "eth2: a new digest keeps the other 88 bytes"
    ((withDigest st devnetDigest).extract 4 statusLen == st.extract 4 statusLen)
  r.check "eth2: Status, Ping, Goodbye, and MetaData have their fixed sizes"
    (statusMethod.request == some (exactly 92) && pingMethod.response == exactly 8 &&
      goodbyeMethod.request == some (exactly 8) && metadataV3Method.response == exactly 25 &&
      metadataV2Method.response == exactly 17)
  r.check "eth2: the fixed requests have their sizes"
    (blocksByRangeMethod.request == some (exactly 24) && blocksByHeadMethod.request == some (exactly 40) &&
      lightClientBootstrapMethod.request == some (exactly 32) &&
      lightClientUpdatesByRangeMethod.request == some (exactly 16))
  r.check "eth2: a block chunk is bounded by MAX_PAYLOAD_SIZE"
    (blocksByRangeMethod.response.maxLen == Libp2p.Protocols.Constants.maxPayloadSize)
  r.check "eth2: the client serves nine methods, three of them one chunk or an error"
    (servedMethods.length == 9 && oneOrErrorMethods.length == 3 &&
      oneOrErrorMethods.all fun m => servedMethods.any (·.id == m.id))
  r.check "eth2: Ping and Goodbye carry a little-endian Uint64"
    (le64 3 == ⟨#[3, 0, 0, 0, 0, 0, 0, 0]⟩ && le64At (le64 70000) 0 == 70000)

/-! ## Two services over loopback -/

/-- Poll `cond` in real time, every 50 ms, for at most `ms`. -/
private partial def waitUntil (cond : Async Bool) (ms : Nat) : Async Bool := do
  if ← cond then return true
  if ms == 0 then return false
  select #[← (Park.sleep 50 () : BaseIO (Park Unit))]
  waitUntil cond (ms - min ms 50)

/-! ## The score profile

The expected values come from `gossipsub_scoring_parameters.rs` of
Lighthouse, computed in Python's float64 at mainnet timing (12 s slots,
32 slots per epoch) for 500000 active validators at slot 100000, then
scaled by 1000 and rounded half away from zero. -/

private def scoringChecks (r : Runner) : IO Unit := do
  let c := devnetChain
  let st := Scoring.settings c
  let (block, aggregate, attestation) := Scoring.dynamicParams st 500000 100000
  r.check "scoring: the block topic equals Lighthouse's"
    (block.topicWeight == 500 && block.timeInMeshWeight == 33 && block.timeInMeshCap == 300 &&
      block.timeInMeshQuantum == 12000 &&
      block.firstMessageDeliveriesWeight == 1147 && block.firstMessageDeliveriesDecay == 993 &&
      block.firstMessageDeliveriesCap == 34869 &&
      block.meshMessageDeliveriesWeight == -500 && block.meshMessageDeliveriesDecay == 972 &&
      block.meshMessageDeliveriesThreshold == 685 && block.meshMessageDeliveriesCap == 2055 &&
      block.meshMessageDeliveriesActivation == 384000 && block.meshMessageDeliveriesWindow == 2000 &&
      block.meshFailurePenaltyWeight == -500 &&
      block.invalidMessageDeliveriesWeight == -215000 && block.invalidMessageDeliveriesDecay == 997)
  r.check "scoring: the aggregate topic equals Lighthouse's"
    (aggregate.firstMessageDeliveriesWeight == 21 && aggregate.firstMessageDeliveriesDecay == 866 &&
      aggregate.firstMessageDeliveriesCap == 1942891 &&
      aggregate.meshMessageDeliveriesDecay == 931 &&
      aggregate.meshMessageDeliveriesThreshold == 279238 &&
      aggregate.meshMessageDeliveriesCap == 1116952)
  r.check "scoring: an attestation subnet equals Lighthouse's"
    (attestation.topicWeight == 16 && attestation.firstMessageDeliveriesWeight == 88 &&
      attestation.firstMessageDeliveriesCap == 455365 &&
      attestation.meshMessageDeliveriesWeight == -16 &&
      attestation.meshMessageDeliveriesDecay == 965 &&
      attestation.meshMessageDeliveriesThreshold == 133290 &&
      attestation.meshMessageDeliveriesCap == 2132644 &&
      attestation.meshMessageDeliveriesActivation == 204000 &&
      attestation.invalidMessageDeliveriesWeight == -6880000)
  let exit := Scoring.kindParams st 500000 100000 .voluntaryExit
  r.check "scoring: the voluntary exit topic equals Lighthouse's"
    (exit.map (fun tp => tp.topicWeight == 50 && tp.firstMessageDeliveriesWeight == 1841 &&
      tp.firstMessageDeliveriesDecay == 999 && tp.firstMessageDeliveriesCap == 21730 &&
      tp.meshMessageDeliveriesWeight == 0 && tp.invalidMessageDeliveriesWeight == -2150000) ==
      some true)
  let g := Scoring.globalParams st
  r.check "scoring: the global parameters equal Lighthouse's"
    (g.behaviourPenaltyWeight == -15879 && g.behaviourPenaltyDecay == 986 &&
      g.behaviourPenaltyThreshold == 6000 && g.topicScoreCap == 53750 &&
      g.ipColocationFactorWeight == -53750 && g.ipColocationFactorThreshold == 8 &&
      g.decayInterval == 12000 && g.decayToZero == 10)
  let (young, _, _) := Scoring.dynamicParams st 500000 0
  r.check "scoring: on a young chain the mesh delivery terms are off, the failure term stays"
    (young.meshMessageDeliveriesWeight == 0 && young.meshMessageDeliveriesThreshold == 0 &&
      young.meshFailurePenaltyWeight == -500)
  let kinds : List Kind := [.beaconBlock, .beaconAggregateAndProof, .beaconAttestation 0,
    .voluntaryExit, .proposerSlashing, .attesterSlashing]
  r.check "scoring: every scored kind passes the validity check"
    (kinds.all fun k => (Scoring.kindParams st 500000 100000 k).all (·.validB))
  r.check "scoring: the global parameters pass the validity check" g.validB
  let digest := c.forkDigest 0
  let params := Scoring.scoredParams c digest 500000 100000
  r.check s!"scoring: the router parameters meet the spec's constraints {params.problems}"
    params.problems.isEmpty
  let ours (k : Kind) : Libp2p.Protocols.Gossipsub.TopicId := ⟨topicOf digest k⟩
  r.check "scoring: a topic of our digest is scored, a column topic is not"
    ((params.score.topics (ours .beaconBlock)).isSome &&
      (params.score.topics (ours (.dataColumnSidecar 3))).isNone)
  r.check "scoring: a topic of another digest is not scored"
    (params.score.topics ⟨topicOf ⟨#[1, 2, 3, 4]⟩ .beaconBlock⟩).isNone
  r.check "scoring: the score retention is 100 epochs" (params.retainScore == 38400000)
  r.check "gossip: the subscription caps are Lighthouse's, for 205 topics a fork"
    (topicsPerFork == 205 && params.maxSubscriptionsPerRpc == some 410 &&
      params.maxSubscribedTopics == some 820)

/-! ## The fork loop -/

private def forkChecks (r : Runner) : IO Unit := do
  let c := devnetChain (later := [entry 10 0xaa])
  let pre := c.forkDigest 9
  let post := c.forkDigest 10
  let run (st : ForkState) (epoch : Nat) : List ForkAction × ForkState := st.step c epoch
  let isSub (d : ByteArray) : ForkAction → Bool
    | .subscribe d' => d' == d
    | _ => false
  let isSwitch : ForkAction → Bool
    | .switch o n => o == pre && n == post
    | _ => false
  let isUnsub (d : ByteArray) : ForkAction → Bool
    | .unsubscribe d' => d' == d
    | _ => false
  let s0 : ForkState := { current := pre }
  let (a8, s8) := run s0 8
  r.check "forks: two epochs before the fork, nothing is due" a8.isEmpty
  let (a9, s9) := run s8 9
  r.check "forks: one epoch before the fork, the post-fork topics are joined"
    (a9.length == 1 && a9.all (isSub post) && s9.next == some post)
  let (a9b, _) := run s9 9
  r.check "forks: a second look in the same epoch joins nothing" a9b.isEmpty
  let (a10, s10) := run s9 10
  r.check "forks: at the fork, the digest switches with no second join"
    (a10.length == 1 && a10.all isSwitch && s10.current == post)
  let (a11, s11) := run s10 11
  r.check "forks: one epoch after the fork, the pre-fork topics stay" a11.isEmpty
  let (a12, s12) := run s11 12
  r.check "forks: two epochs after the fork, the pre-fork topics go"
    (a12.length == 1 && a12.all (isUnsub pre) && s12.retiring.isEmpty)
  let (late, _) := run s8 10
  r.check "forks: a fork the loop did not see ahead joins and switches at once"
    (late.length == 2 && (late.head?.map (isSub post)) == some true &&
      (late.getLast?.map isSwitch) == some true)
  -- Two forks one epoch apart, at 10 and 11: each pre-fork digest goes
  -- two epochs after its own fork.
  let c2 := devnetChain (later := [entry 10 0xaa, entry 11 0xbb])
  let post2 := c2.forkDigest 11
  let run2 (st : ForkState) (epoch : Nat) : List ForkAction × ForkState := st.step c2 epoch
  let (_, t10) := run2 s9 10
  let (_, t11) := run2 t10 11
  let (b12, t12) := run2 t11 12
  let (b13, t13) := run2 t12 13
  r.check "forks: two forks an epoch apart, each pre-fork digest goes in its turn"
    (t11.current == post2 && b12.length == 1 && b12.all (isUnsub pre) &&
      b13.length == 1 && b13.all (isUnsub post) && t13.retiring.isEmpty)

/-! ## The peer table -/

private def peersChecks (r : Runner) : IO Unit := do
  let key (seed : UInt8) : IO PeerId := do
    let k ← expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 seed⟩)
    let pub ← expectOk "public key" k.toPublic
    expectOk "peer id" (PeerId.ofPubKey pub)
  let p ← key 1
  let q ← key 2
  let t := ({} : Peers).connect p true 0 |>.connect q false 0
  r.check "peers: no Ping is due before the interval"
    ((t.takeDue 14999).1 == [])
  r.check "peers: an outbound peer is due at 15 s, an inbound one at 20 s"
    ((t.takeDue 15000).1 == [p] && (t.takeDue 20000).1 == [p, q])
  let (_, t1) := t.takeDue 15000
  r.check "peers: a peer taken as due is not due again at once" ((t1.takeDue 16000).1 == [])
  r.check "peers: an inbound Ping counts as our check"
    (((t.pinged q 10000).takeDue 20000).1 == [p])
  r.check "peers: an unknown seq number is news" (t.seqNews p 0)
  r.check "peers: a known seq number is not news, a higher one is"
    (!(t.setMeta p 3).seqNews p 3 && (t.setMeta p 3).seqNews p 4)
  r.check "peers: a peer not in the table is no news" (!(t.disconnect p).seqNews p 9)
  let b := t.ban p 0 100
  r.check "peers: a ban holds until its end" (b.banned p 99 && !b.banned p 100 && !b.banned q 50)
  r.check "peers: a second ban keeps the later end" ((b.ban p 10 50).banned p 99)
  let full := (List.range (Constants.maxBans + 5)).foldl
    (fun (acc : Peers) i => { acc with bans := acc.bans ++ [(p, 1000 + i)] }) {}
  r.check "peers: a new ban keeps the table at the cap"
    ((full.ban q 0 5000).bans.length == Constants.maxBans && (full.ban q 0 5000).banned q 10)

/-! ## The client's bytes

Filler bytes stand for the client's SSZ, and the requests carry the few
fields a check needs, as a client would write them. -/

/-- A `Status` of filler bytes. The service writes the digest. -/
private def testStatus : ByteArray := ⟨Array.replicate statusLen 0x11⟩

/-- A `MetaData` of filler bytes with `seq_number` 5. -/
private def testMeta : MetaData :=
  { seq := 5, v3 := ⟨Array.replicate metaDataV3Len 0x33⟩, v2 := ⟨Array.replicate metaDataV2Len 0x22⟩ }

/-- A `BeaconBlocksByRange` request: `start_slot`, `count`, `step` 1. -/
private def rangeRequest (start count : Nat) : ByteArray := le64 start ++ le64 count ++ le64 1

/-- The `serve` of the checks. It does what a client's `serve` does,
over filler payloads whose first byte names the chunk. -/
private def testServe (digest : ByteArray) : PeerId → Libp2p.Protocols.ReqResp.Method → ByteArray →
    Emit → Async Ending := fun _ m req emit => do
  -- `count` blocks from `start_slot` on, each with our digest.
  if m.id == blocksByRangeMethod.id then
    let start := le64At req 0
    for i in [0:le64At req 8] do
      if !(← emit digest ⟨Array.replicate 100 (start + i).toUInt8⟩) then break
    return .done
  -- The ancestry of the root, newest first: blocks 9, 8, ... here.
  else if m.id == blocksByHeadMethod.id then
    for i in [0:le64At req 32] do
      discard <| emit digest ⟨Array.replicate 100 (9 - i).toUInt8⟩
    return .done
  -- One column, then the end of what we keep.
  else if m.id == columnsByRangeMethod.id then
    discard <| emit digest ⟨Array.replicate 100 (le64At req 0).toUInt8⟩
    return .resourceUnavailable "pruned"
  else if m.id == lightClientBootstrapMethod.id then
    discard <| emit digest ⟨Array.replicate 300 3⟩
    return .done
  -- The finality and optimistic updates take the default: no chunk.
  else return .done

/-- A service on loopback with a recorded event list. -/
private def startOn (c : Chain) (seed : UInt8) (events : OnceRef (List Event))
    (boot : List Enr := []) (partialColumns : Libp2p.Protocols.Gossipsub.Core.PartialOpts := {}) :
    Async Service := do
  let key ← expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 seed⟩)
  Service.start {
    chain := c, status := testStatus, metaData := testMeta
    key, ip := [127, 0, 0, 1], tcpPort := 0, discPort := 0
    bootEnrs := boot, advert := { cgc := 4 }, discoverEveryMs := 500, partialColumns
    onEvent := fun e => events.update (· ++ [e]), serve := testServe (c.forkDigest 0) }

private def serviceChecks (r : Runner) : Async Unit := do
  -- The genesis is now, so the wall-clock epoch is 0.
  let c := devnetChain ((← wallMs) / 1000)
  let digest := c.forkDigest 0
  let evA ← (OnceRef.new ([] : List Event) : BaseIO _)
  let evB ← (OnceRef.new ([] : List Event) : BaseIO _)
  let a ← startOn c 1 evA
  let b ← startOn c 2 evB [← (a.localEnr : BaseIO Enr)]
  let aPeer := a.base.host.localPeer
  let bPeer := b.base.host.localPeer
  let has (ev : OnceRef (List Event)) (f : Event → Bool) : Async Bool := do
    return (← (ev.get : BaseIO (List Event))).any f
  r.check "eth2 service: QUIC is on by default, beside TCP" (a.listenAddrs.length == 2)
  r.check "eth2 service: the boot record's peer connects"
    (← waitUntil (has evB fun | .connected p true => p == aPeer | _ => false) 5000)
  r.check "eth2 service: the listener sees the inbound peer"
    (← waitUntil (has evA fun | .connected p false => p == bPeer | _ => false) 5000)
  r.check "eth2 service: the dialer gets the listener's Status, our digest then the client's bytes"
    (← waitUntil (has evB fun
      | .status p s => p == aPeer && s == withDigest testStatus digest
      | _ => false) 5000)
  r.check "eth2 service: the listener gets the dialer's Status"
    (← waitUntil (has evA fun | .status p _ => p == bPeer | _ => false) 5000)
  -- B's identify answer names B's listeners.
  let named ← match ← a.base.host.newStream bPeer [Libp2p.Protocols.Identify.protocolId] with
    | .error _ => pure []
    | .ok (_, st) =>
      match ← Libp2p.Protocols.Identify.client st Clock.system 5000 (some bPeer) with
      | .ok (some (m, _)) => pure m.listenAddrs
      | _ => pure []
  r.check "eth2 service: the identify answer names the listeners"
    (!b.listenAddrs.isEmpty && b.listenAddrs.all fun la => named.contains la.toBytes)
  -- Gossip: both subscribe, and B publishes once A is in B's mesh.
  r.check "eth2 service: the subscribes post" ((← a.subscribe .beaconBlock) && (← b.subscribe .beaconBlock))
  -- A burst past the control queue of the gossipsub node (`inputSlots`,
  -- 64): every post parks until the loop takes it, so none is lost.
  let burst ← (List.range Constants.dataColumnSidecarSubnetCount).allM fun i =>
    a.subscribe (.dataColumnSidecar i)
  r.check "eth2 service: a burst of 128 subscribes loses none" burst
  -- 66 score updates, past the 64 slots of the control queue.
  r.check "eth2 service: the score update posts every topic" (← a.updateScores 500000 100)
  let allTopics : Async Bool := do
    match ← a.gossip.stats with
    | some st => return st.topics == 129
    | none => return false
  r.check "eth2 service: the router holds the block topic and the 128 column topics"
    (← waitUntil allTopics 5000)
  let meshed : Async Bool := do
    match ← b.gossip.stats with
    | some st => return st.mesh.any (·.2 ≥ 1)
    | none => return false
  r.check "eth2 service: the block topic meshes" (← waitUntil meshed 10000)
  let block : ByteArray := ⟨Array.replicate 1000 7⟩
  r.check "eth2 service: the block publishes" (← (b.publish .beaconBlock block : IO Bool))
  let isBlock : Event → Bool
    | .gossip .beaconBlock _ p ssz => p == bPeer && ssz == block
    | _ => false
  r.check "eth2 service: the listener holds the block for validation" (← waitUntil (has evA isBlock) 5000)
  let ids := (← (evA.get : BaseIO (List Event))).filterMap fun
    | .gossip _ id _ _ => some id
    | _ => none
  let data ← expectOk "compress" (Snappy.compress block)
  r.check "eth2 service: the held id is the consensus message id"
    (ids.head? ==
      messageId (← (a.topic .beaconBlock : IO Libp2p.Protocols.Gossipsub.TopicId)).name data)
  if let some id := ids.head? then
    r.check "eth2 service: the validation answer posts" (← (a.report id bPeer .accept : BaseIO Bool))
  -- A block request with its context bytes.
  match ← b.request aPeer blocksByRangeMethod (some (rangeRequest 10 3)) with
  | .ok chunks =>
    r.check "eth2 service: the range request gets three chunks" (chunks.length == 3)
    r.check "eth2 service: each chunk carries our digest as context"
      (chunks.all (·.context == digest))
    r.check "eth2 service: the chunks keep their order"
      (chunks.map (·.payload.get! 0) == [10, 11, 12])
  | .error _ => r.check "eth2 service: the range request answers" false
  -- A client that emits past the method's cap: the service stops it there.
  match ← b.request aPeer blocksByRangeMethod (some (rangeRequest 0 (Constants.maxRequestBlocksDeneb + 2))) with
  | .ok chunks =>
    r.check "eth2 service: the cap of MAX_REQUEST_BLOCKS_DENEB holds"
      (chunks.length == Constants.maxRequestBlocksDeneb)
  | .error _ => r.check "eth2 service: the long range request answers" false
  -- A request of another size than the method's fixed one is refused.
  r.check "eth2 service: a range request of 23 bytes gets no block"
    (match ← b.request aPeer blocksByRangeMethod (some ⟨Array.replicate 23 0⟩) with
     | .ok chunks => !chunks.any (·.result matches .success)
     | .error _ => true)
  -- A check that refuses the second block ends the read there.
  let checked ← (OnceRef.new ([] : List Nat) : BaseIO (OnceRef (List Nat)))
  let each ← b.requestEach aPeer blocksByRangeMethod (some (rangeRequest 10 3)) fun c => do
    (checked.update (· ++ [(c.payload.get! 0).toNat]) : BaseIO Unit)
    return c.payload.get! 0 != 11
  r.check "eth2 service: a check of each chunk stops the read at the refused block"
    ((match each with | .ok () => true | .error _ => false) && (← checked.get) == [10, 11])
  -- The light-client methods.
  match ← b.request aPeer lightClientBootstrapMethod (some ⟨Array.replicate 32 5⟩) with
  | .ok chunks =>
    r.check "eth2 service: a light-client bootstrap answers one chunk with our digest"
      (chunks.map (·.payload.size) == [300] && chunks.all (·.context == digest))
  | .error _ => r.check "eth2 service: the light-client bootstrap answers" false
  match ← b.request aPeer lightClientFinalityUpdateMethod none with
  | .ok chunks =>
    r.check "eth2 service: a light-client request with no data gets ResourceUnavailable"
      (chunks.map (·.result) == [.resourceUnavailable])
  | .error _ => r.check "eth2 service: the finality update answers" false
  match ← b.request aPeer lightClientUpdatesByRangeMethod (some (le64 4 ++ le64 2)) with
  | .ok chunks =>
    r.check "eth2 service: an updates range with no data answers no chunk" chunks.isEmpty
  | .error _ => r.check "eth2 service: the light-client updates answer" false
  r.check "eth2 service: the light-client topics parse"
    ((topicParse? (topicOf digest .lightClientOptimisticUpdate)).map (·.2) ==
      some .lightClientOptimisticUpdate)
  match ← b.request aPeer columnsByRangeMethod (some (le64 5 ++ le64 1)) with
  | .ok chunks =>
    r.check "eth2 service: a column range ends with ResourceUnavailable after its column"
      (chunks.map (·.result) == [.success, .resourceUnavailable] &&
        (chunks.getLast?.map (·.payload)) == some "pruned".toUTF8)
  | .error _ => r.check "eth2 service: the column range request answers" false
  match ← b.request aPeer blocksByHeadMethod (some (⟨Array.replicate 32 1⟩ ++ le64 3)) with
  | .ok chunks =>
    r.check "eth2 service: the head request gets the ancestry, newest first"
      (chunks.map (·.payload.get! 0) == [9, 8, 7] && chunks.all (·.context == digest))
  | .error _ => r.check "eth2 service: the head request answers" false
  match ← b.request aPeer goodbyeMethod (some (le64 3)) with
  | .ok chunks =>
    r.check "eth2 service: Goodbye answers one chunk of 0, as the spec asks"
      (chunks.map (·.payload) == [le64 0])
  | .error _ => r.check "eth2 service: Goodbye answers" false
  match ← b.request aPeer metadataV3Method none with
  | .ok [m] => r.check "eth2 service: MetaData v3 answers the client's bytes" (m.payload == testMeta.v3)
  | _ => r.check "eth2 service: MetaData v3 answers" false
  match ← b.request aPeer metadataV2Method none with
  | .ok [m] => r.check "eth2 service: MetaData v2 answers the client's bytes" (m.payload == testMeta.v2)
  | _ => r.check "eth2 service: MetaData v2 answers" false
  match ← b.request aPeer pingMethod (some (le64 0)) with
  | .ok [p] => r.check "eth2 service: Ping answers the seq number" (p.payload == le64 testMeta.seq)
  | _ => r.check "eth2 service: Ping answers" false
  -- Liveness: the first Ping of a peer brings its MetaData, since we
  -- know none of it yet. The second finds the same seq number.
  b.base.ping aPeer
  b.base.ping aPeer
  let metas := (← (evB.get : BaseIO (List Event))).filter fun
    | .metaData p _ _ => p == aPeer
    | _ => false
  r.check "eth2 service: a Ping with a new seq number brings MetaData once"
    (match metas with
     | [.metaData _ seq md] => seq == testMeta.seq && md == testMeta.v3
     | _ => false)
  r.check "eth2 service: an answered Ping is no unresponsive event"
    (!(← has evB fun | .unresponsive _ => true | _ => false))
  -- The client's updates: a new Status keeps our digest, and bytes of
  -- another width change nothing.
  let newer : ByteArray := ⟨Array.replicate statusLen 0x55⟩
  r.check "eth2 service: a new Status of 92 bytes is taken" (← (a.setStatus newer : BaseIO Bool))
  r.check "eth2 service: the new Status keeps our digest"
    ((← (a.base.status.get : BaseIO ByteArray)) == withDigest newer digest)
  r.check "eth2 service: a Status of 91 bytes is refused"
    (!(← (a.setStatus (newer.extract 0 91) : BaseIO Bool)))
  r.check "eth2 service: a MetaData of the wrong width is refused"
    (!(← (a.setMetaData { testMeta with v2 := testMeta.v3 } : BaseIO Bool)))
  r.check "eth2 service: a new MetaData is taken" (← (a.setMetaData { testMeta with seq := 6 } : BaseIO Bool))
  match ← b.request aPeer pingMethod (some (le64 0)) with
  | .ok [p] => r.check "eth2 service: Ping answers the new seq number" (p.payload == le64 6)
  | _ => r.check "eth2 service: Ping answers after the update" false
  -- Goodbye at stop.
  b.stop
  r.check "eth2 service: the stop says Goodbye with reason 1"
    (← waitUntil (has evA fun | .goodbye p 1 => p == bPeer | _ => false) 5000)
  r.check "eth2 service: the listener sees the peer leave"
    (← waitUntil (has evA fun | .disconnected p => p == bPeer | _ => false) 5000)
  -- A ban: C connects, A bans it, and C's discovery redials every 500 ms.
  let evC ← (OnceRef.new ([] : List Event) : BaseIO _)
  let cs ← startOn c 3 evC [← (a.localEnr : BaseIO Enr)]
  let cPeer := cs.base.host.localPeer
  r.check "eth2 service: the third peer connects"
    (← waitUntil (has evA fun | .connected p false => p == cPeer | _ => false) 5000)
  a.ban cPeer
  r.check "eth2 service: a ban says Goodbye with reason 251"
    (← waitUntil (has evC fun | .goodbye p 251 => p == aPeer | _ => false) 5000)
  r.check "eth2 service: the banned peer leaves"
    (← waitUntil (has evA fun | .disconnected p => p == cPeer | _ => false) 5000)
  r.check "eth2 service: the peer is banned" (← (a.isBanned cPeer : BaseIO Bool))
  -- With C's listen addresses in the peerstore, only the gater can refuse.
  (a.base.host.addAddrs cPeer cs.listenAddrs : BaseIO Unit)
  r.check "eth2 service: the gater refuses our dial to a banned peer"
    (match ← a.base.host.dialPeer cPeer with | .error _ => true | .ok _ => false)
  IO.sleep 2000
  let connects := (← (evA.get : BaseIO (List Event))).filter fun
    | .connected p _ => p == cPeer
    | _ => false
  r.check "eth2 service: the gater refuses the banned peer's redials" (connects.length == 1)
  cs.stop
  a.stop

/-- The service refuses a config whose bytes or schedule are malformed. -/
private def startRefusals (r : Runner) : Async Unit := do
  let key ← expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 31⟩)
  let base : Config := {
    chain := devnetChain, status := testStatus, metaData := testMeta
    key, ip := [127, 0, 0, 1], tcpPort := 0, quicPort := none, discPort := 0, advert := { cgc := 4 } }
  let refused (cfg : Config) : Async Bool := do
    try
      let s ← Service.start cfg
      s.stop
      return false
    catch _ => return true
  r.check "eth2 service: a Status of 91 bytes is refused at the start"
    (← refused { base with status := testStatus.extract 0 91 })
  r.check "eth2 service: a schedule that starts after epoch 0 is refused at the start"
    (← refused { base with chain := { devnetChain with schedule := [entry 3 1] } })
  r.check "eth2 service: a MetaData of the wrong width is refused at the start"
    (← refused { base with metaData := { testMeta with v3 := testMeta.v2 } })

/-- A fork on a live service: 1 s slots, 2 slots per epoch, and a new
entry at epoch 2, 4 s after genesis. The fork loop joins the post-fork
topic at epoch 1, switches at epoch 2, and leaves the pre-fork topic at
epoch 4. The run takes about 9 s. -/
private def liveForkChecks (r : Runner) : Async Unit := do
  let c := { devnetChain ((← wallMs) / 1000) [entry 2 0xaa] with slotDurationMs := 1000, slotsPerEpoch := 2 }
  let pre := c.forkDigest 0
  let post := c.forkDigest 2
  let ev ← (OnceRef.new ([] : List Event) : BaseIO _)
  let a ← startOn c 4 ev
  r.check "eth2 fork: the subscribe posts" (← a.subscribe .beaconBlock)
  let topics (n : Nat) : Async Bool := do
    match ← a.gossip.stats with
    | some st => return st.topics == n
    | none => return false
  r.check "eth2 fork: ahead of the fork, both digests carry the topic" (← waitUntil (topics 2) 5000)
  let switched : Async Bool := do
    return statusDigest (← (a.base.status.get : BaseIO ByteArray)) == post
  r.check "eth2 fork: at the fork, our Status names the new digest" (← waitUntil switched 5000)
  r.check "eth2 fork: the Status keeps the client's other bytes"
    (((← (a.base.status.get : BaseIO ByteArray)).extract 4 statusLen) == testStatus.extract 4 statusLen)
  r.check "eth2 fork: our record names the new digest"
    (forkDigest? (← (a.localEnr : BaseIO Enr)) == some post)
  r.check "eth2 fork: the topic of a kind is the new digest's"
    ((← (a.topic .beaconBlock : BaseIO Libp2p.Protocols.Gossipsub.TopicId)).name ==
      topicOf post .beaconBlock)
  r.check "eth2 fork: two epochs later, the pre-fork topic goes" (← waitUntil (topics 1) 7000)
  r.check "eth2 fork: the two digests differ" (pre != post)
  a.stop

/-- The connection cap: a target of one peer allows two connections
(Lighthouse's 1.3 times the target, rounded up), so of three peers that
dial, two at most stay. -/
private def limitChecks (r : Runner) : Async Unit := do
  let c := devnetChain ((← wallMs) / 1000)
  let ev ← (OnceRef.new ([] : List Event) : BaseIO _)
  let key ← expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 9⟩)
  let a ← Service.start {
    chain := c, status := testStatus, metaData := testMeta
    key, ip := [127, 0, 0, 1], tcpPort := 0, discPort := 0, advert := { cgc := 4 }
    targetPeers := 1, onEvent := fun e => ev.update (· ++ [e]) }
  let boot ← (a.localEnr : BaseIO Enr)
  let others ← [11, 12, 13].mapM fun (seed : UInt8) => do
    let evo ← (OnceRef.new ([] : List Event) : BaseIO _)
    startOn c seed evo [boot]
  let connected : Async Bool := do return (← (a.peers : BaseIO (List PeerId))).length ≥ 2
  r.check "eth2 limits: two peers connect" (← waitUntil connected 5000)
  IO.sleep 2000
  r.check "eth2 limits: the third connection is refused"
    ((← (a.peers : BaseIO (List PeerId))).length == 2)
  for o in others do o.stop
  a.stop

/-- The responder's rate limit, between two services over loopback:
chunks past the bucket wait and still arrive, a request past
`MAX_CONCURRENT_REQUESTS` open ones gets no chunk, and the stop wakes
the withheld chunks. -/
private def rateLimitChecks (r : Runner) : Async Unit := do
  let c := devnetChain ((← wallMs) / 1000)
  let evA ← (OnceRef.new ([] : List Event) : BaseIO _)
  let evB ← (OnceRef.new ([] : List Event) : BaseIO _)
  let a ← startOn c 21 evA
  let b ← startOn c 22 evB [← (a.localEnr : BaseIO Enr)]
  let aPeer := a.base.host.localPeer
  let bPeer := b.base.host.localPeer
  let up : Async Bool := do return (← (b.peers : BaseIO (List PeerId))).contains aPeer
  r.check "eth2 rate limit: the peers connect" (← waitUntil up 5000)
  let successes : Except Libp2p.Protocols.ReqResp.Error (List Libp2p.Protocols.ReqResp.Chunk) → Nat
    | .ok cs => (cs.filter (·.result matches .success)).length
    | .error _ => 0
  -- The Status quota is 5 per 15 s, and B's dial sent one Status. So 4
  -- more go at once, and the fifth waits about one step of 3 s.
  let ours := withDigest testStatus (c.forkDigest 0)
  let t0 ← (IO.monoMsNow : BaseIO Nat)
  let burst ← (List.range 4).mapM fun _ => b.request aPeer statusMethod (some ours)
  let quick := (← (IO.monoMsNow : BaseIO Nat)) - t0
  let t1 ← (IO.monoMsNow : BaseIO Nat)
  let late ← b.request aPeer statusMethod (some ours)
  let waited := (← (IO.monoMsNow : BaseIO Nat)) - t1
  r.check "eth2 rate limit: the rest of the bucket goes at once"
    (burst.all (successes · == 1) && quick < 1500)
  r.check "eth2 rate limit: a chunk past the bucket waits, then arrives"
    (successes late == 1 && 1500 ≤ waited)
  -- The bootstrap quota is 1 per 10 s. One request takes it, so the next
  -- two wait, and a third beside them is past the cap of 2.
  let root : ByteArray := ⟨Array.replicate 32 5⟩
  discard <| b.request aPeer lightClientBootstrapMethod (some root)
  let answers ← (OnceRef.new ([] : List Nat) : BaseIO _)
  let raw ← (TaskSet.new : BaseIO TaskSet)
  for _ in [0:3] do
    (raw.spawn do
      match ← b.base.host.newStream aPeer [lightClientBootstrapMethod.id] with
      | .ok (_, st) =>
        let got ← Libp2p.Protocols.ReqResp.requestAll st lightClientBootstrapMethod Clock.system
          30000 (some root)
        (answers.update (successes got :: ·) : BaseIO Unit)
      | .error _ => pure () : BaseIO Unit)
  r.check "eth2 rate limit: the third open request of a method raises tooManyRequests"
    (← waitUntil (do return (← (evA.get : BaseIO (List Event))).any fun
      | .tooManyRequests p m => p == bPeer && m == lightClientBootstrapMethod.id
      | _ => false) 5000)
  r.check "eth2 rate limit: the refused request gets no chunk"
    (← waitUntil (do return (← (answers.get : BaseIO (List Nat))) == [0]) 5000)
  -- The two withheld answers park until the stop, which wakes them.
  let t1 ← (IO.monoMsNow : BaseIO Nat)
  a.stop
  raw.joinAll
  r.check "eth2 rate limit: the stop wakes the withheld chunks"
    ((← (IO.monoMsNow : BaseIO Nat)) - t1 < 5000)
  b.stop

/-! ## Partial columns -/

private def partialChecks (r : Runner) : IO Unit := do
  let root : ByteArray := ⟨Array.replicate 32 7⟩
  let gid := PartialColumns.groupIdOf root
  r.check "partial: the group ID is 0x00 then the root" (gid.size == 33 && gid.get! 0 == 0)
  r.check "partial: the group ID gives back its root" (PartialColumns.rootOf? gid == some root)
  r.check "partial: an unknown version is ignored"
    (PartialColumns.rootOf? (ByteArray.mk #[1] ++ root)).isNone
  let pa := PeerId.inline (ByteArray.mk #[1]) (by decide)
  let pb := PeerId.inline (ByteArray.mk #[2]) (by decide)
  let (first, s1) := ({} : PartialColumns.Rewards).earn pa root 0
  let (second, s2) := s1.earn pa root 0
  r.check "partial: the reward goes once per peer, block, and column" (first && !second)
  r.check "partial: another column and another peer each earn it"
    ((s2.earn pa root 1).1 && (s2.earn pb root 0).1)
  let five := (List.range 5).foldl (fun (st : PartialColumns.Rewards) i =>
    (st.earn pa ⟨Array.replicate 32 i.toUInt8⟩ 0).2) {}
  r.check "partial: the state keeps four blocks, and the oldest goes"
    (five.blocks.length == 4 && !five.blocks.any (·.1 == ⟨Array.replicate 32 0⟩))

/-- Two services with partial columns on column 0: A sends B its parts
metadata and a message, and B gets both bytes as they went out. -/
private def partialServiceChecks (r : Runner) : Async Unit := do
  let c := devnetChain ((← wallMs) / 1000)
  let opts : Libp2p.Protocols.Gossipsub.Core.PartialOpts := { requests := true, supports := true }
  let evA ← (OnceRef.new ([] : List Event) : BaseIO _)
  let evB ← (OnceRef.new ([] : List Event) : BaseIO _)
  let a ← startOn c 21 evA [] opts
  let b ← startOn c 22 evB [← (a.localEnr : BaseIO Enr)] opts
  let aPeer := a.base.host.localPeer
  let bPeer := b.base.host.localPeer
  r.check "partial service: both subscribe to column 0"
    ((← a.subscribe (.dataColumnSidecar 0)) && (← b.subscribe (.dataColumnSidecar 0)))
  let knows : Async Bool := do
    match ← a.partialColumnPeers 0 with
    | some ps => return ps.any fun (p, req) => p == bPeer && req
    | none => return false
  r.check "partial service: A learns that B asks for partial columns" (← waitUntil knows 10000)
  let root : ByteArray := ⟨Array.replicate 32 5⟩
  let parts : ByteArray := ⟨#[1, 2, 3]⟩
  let msg : ByteArray := ⟨Array.replicate 500 9⟩
  r.check "partial service: A sends its metadata and a message"
    (← (a.sendPartialColumn bPeer root 0 (some parts) (some msg) : BaseIO Bool))
  let got : Async Bool := do
    return (← (evB.get : BaseIO (List Event))).any fun
      | .partialColumn 0 r p m x => r == root && p == aPeer && m == some parts && x == some msg
      | _ => false
  r.check "partial service: B gets the bytes, the block root, and the source" (← waitUntil got 5000)
  -- A group ID of version 1: B ignores it.
  let topic ← (a.topic (.dataColumnSidecar 0) : BaseIO Libp2p.Protocols.Gossipsub.TopicId)
  let other : ByteArray := ⟨Array.replicate 32 6⟩
  discard <| (a.gossip.sendPartial bPeer
    { topicId := some (Bytes.toNatList topic.name.toUTF8)
      groupId := some (Bytes.toNatList (ByteArray.mk #[1] ++ other))
      partialMessage := some (Bytes.toNatList msg), partsMetadata := some (Bytes.toNatList parts) } :
      BaseIO Bool)
  -- A known group after it, so the wait has an end.
  discard <| (a.sendPartialColumn bPeer other 0 (some parts) none : BaseIO Bool)
  let later : Async Bool := do
    return (← (evB.get : BaseIO (List Event))).any fun
      | .partialColumn 0 r _ _ none => r == other
      | _ => false
  r.check "partial service: the known group after it arrives" (← waitUntil later 5000)
  r.check "partial service: B ignores the group ID of an unknown version"
    (((← (evB.get : BaseIO (List Event))).filter (fun
      | .partialColumn 0 r _ _ _ => r == other
      | _ => false)).length == 1)
  r.check "partial service: B judges the cells valid, and the reward posts"
    (← (b.judgePartialColumn aPeer root 0 true : BaseIO Bool))
  r.check "partial service: a second judgment of the same block earns nothing more"
    (!((← (b.partials.get : BaseIO PartialColumns.Rewards)).earn aPeer root 0).1)
  b.stop
  a.stop

def run (r : Runner) : IO Unit := do
  r.section "eth2" "vendor/consensus-specs: specs/*/p2p-interface.md to fulu, fulu partial-columns"
  partialChecks r
  Async.run (partialServiceChecks r)
  chainChecks r
  messageIdChecks r
  methodChecks r
  scoringChecks r
  forkChecks r
  peersChecks r
  Async.run (startRefusals r)
  Async.run (serviceChecks r)
  Async.run (liveForkChecks r)
  Async.run (limitChecks r)
  Async.run (rateLimitChecks r)

end Tests.Eth2
