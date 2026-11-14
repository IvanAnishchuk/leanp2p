import Tests.Support
import Libp2p.Eth2

/-!
# eth2 suite

The suite checks `libp2p/eth2` in this order:
- the chain of a devnet config, and its fork digest against the record
  that a Lighthouse node of that devnet published
- the message id, against SHA-256 values that Python's `hashlib`
  computed from the spec's formula
- the small req/resp messages
- two services over loopback: the dial from a boot record, the
  `Status` handshake, gossip with the held validation, a block request
  with its context bytes, MetaData, and Goodbye at stop

The devnet fixture is the shadow node's (`etheorem-shadow-node` at
`8cd3247`, `helper/tests/fixtures`). The suite keeps the lines of
`config.yaml` that the chain reads, the genesis validators root, and
the ENR. Its fork digest `8049f250` is the one Python computes from the
same values, and the one the record carries.
-/

set_option autoImplicit false

namespace Tests.Eth2

open Conc Libp2p.Eth2 Libp2p.Identity

private def hex (s : String) : ByteArray := (Bytes.ofHex? s).getD .empty

private def expectOk {ε α : Type} (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error _ => throw (IO.userError s!"{what} failed")

/-! ## The devnet chain and its record -/

/-- The lines of the devnet's `config.yaml` that the chain reads, with
the comments and the far-future forks of the file. -/
private def devnetConfig : String :=
  "PRESET_BASE: 'mainnet'\n" ++
  "CONFIG_NAME: 'testnet' # needs to exist because of Prysm\n" ++
  "GENESIS_FORK_VERSION: 0x10000038\n" ++
  "ALTAIR_FORK_VERSION: 0x20000038\nALTAIR_FORK_EPOCH: 0\n" ++
  "BELLATRIX_FORK_VERSION: 0x30000038\nBELLATRIX_FORK_EPOCH: 0\n" ++
  "CAPELLA_FORK_VERSION: 0x40000038\nCAPELLA_FORK_EPOCH: 0\n" ++
  "DENEB_FORK_VERSION: 0x50000038\nDENEB_FORK_EPOCH: 0\n" ++
  "ELECTRA_FORK_VERSION: 0x60000038\nELECTRA_FORK_EPOCH: 0\n" ++
  "FULU_FORK_VERSION: 0x70000038\nFULU_FORK_EPOCH: 0\n" ++
  "GLOAS_FORK_VERSION: 0x80000038\nGLOAS_FORK_EPOCH: 18446744073709551615\n" ++
  "SLOT_DURATION_MS: 12000\n" ++
  "MAX_BLOBS_PER_BLOCK_ELECTRA: 9\n" ++
  "BLOB_SCHEDULE:\n  - EPOCH: 0\n    MAX_BLOBS_PER_BLOCK: 21\n" ++
  "DEPOSIT_CHAIN_ID: 3151908\n"

private def devnetGvr : String := "02f14ddf4f37508bccf9ca39ac94d4a559cfdbd1e94e2f335114be1e50d02a7f"

/-- The record of a Lighthouse node of the devnet. -/
private def devnetEnr : String :=
  "enr:-NO4QEamopaXI3y7x4t2Kiir5IR2VxQSTZaH1QSKvsGH3rnBLdpFNQP_-dMWVqyrQakXBc0Ad5yy-W0cce1UHhEKgmMHh2F0dG5ldHOIgAEAAAAAAACDY2djgYCEZXRoMpCASfJQcAAAOP__________gmlkgnY0gmlwhKwQAA2DbmZkhAAAAACEcXVpY4IjKYlzZWNwMjU2azGhAtAWrNSOtz-KzskCSwPbP21-C9qVUN1FCgogvYX0EBtRiHN5bmNuZXRzD4N0Y3CCIyiDdWRwgiMo"

/-- The first 40 bytes of a `genesis.ssz`. -/
private def genesisPrefix (time : Nat) : ByteArray := Chain.le64 time ++ hex devnetGvr

private def devnetChain (time : Nat := 1700000000) : IO Chain :=
  match Config.chainOf devnetConfig (genesisPrefix time) with
  | .ok c => pure c
  | .error e => throw (IO.userError e)

private def chainChecks (r : Runner) : IO Unit := do
  let c ← devnetChain
  r.check "eth2: the config gives six scheduled forks after genesis" (c.forks.length == 6)
  r.check "eth2: the config gives Fulu at epoch 0" (c.fuluEpoch == some 0)
  r.check "eth2: the config gives the one blob schedule entry"
    (c.blobSchedule.map (fun b => (b.epoch, b.maxBlobsPerBlock)) == [(0, 21)])
  r.check "eth2: the config gives the mainnet epoch and the slot length"
    (c.slotsPerEpoch == 32 && c.slotDurationMs == 12000 && c.maxBlobsElectra == 9)
  r.check "eth2: the genesis prefix gives the root and the time"
    (c.genesisValidatorsRoot == hex devnetGvr && c.genesisTime == 1700000000)
  r.check "eth2: the fork version at epoch 0 is Fulu's" (c.forkVersion 0 == hex "70000038")
  r.check "eth2: the digest is the one Python computes"
    ((c.forkDigest 0).toOption == some (hex "8049f250"))
  r.check "eth2: no fork follows" (c.nextForkEpoch 0 == Constants.farFutureEpoch)
  let rec_ ← expectOk "the devnet ENR" (Enr.ofText? devnetEnr)
  r.check "eth2: Lighthouse's record carries our digest" (forkDigest? rec_ == (c.forkDigest 0).toOption)
  r.check "eth2: Lighthouse's ENRForkID is ours byte for byte"
    (enrForkId? rec_ == (c.enrForkId 0).toOption)
  r.check "eth2: Lighthouse's nfd is ours" (bytesOf? rec_ nfdKey == (c.nextForkDigest 0).toOption)
  r.check "eth2: the record names a supernode's custody" (cgc? rec_ == some 128)
  r.check "eth2: the record is of our fork" (sameFork c 0 rec_)
  r.check "eth2: the record has a dial address"
    (match rec_.dialAddrs with | .ok (_ :: _) => true | _ => false)
  -- A Blob-Parameters-Only fork at epoch 5: a new digest with the same
  -- version, and the next fork epoch is the entry's.
  let bpo := { c with blobSchedule := c.blobSchedule ++ [({ epoch := 5, maxBlobsPerBlock := 48 } : BlobEntry)] }
  r.check "eth2: a BPO entry is the next fork" (bpo.nextForkEpoch 0 == 5)
  r.check "eth2: a BPO entry changes the digest"
    ((bpo.forkDigest 5).toOption != (bpo.forkDigest 0).toOption)
  r.check "eth2: a BPO entry keeps the version" (bpo.forkVersion 5 == bpo.forkVersion 0)
  r.check "eth2: the nfd of a BPO entry is its digest"
    ((bpo.nextForkDigest 0).toOption == (bpo.forkDigest 5).toOption)
  -- Before Fulu, the digest is the plain fork data root.
  let early := { c with fuluEpoch := some 10 }
  r.check "eth2: before Fulu the digest has no blob mask"
    ((early.forkDigest 0).toOption ==
      ((Chain.forkDataRoot (early.forkVersion 0) early.genesisValidatorsRoot).toOption.map
        (·.extract 0 4)))

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

/-! ## The small messages -/

private def messageChecks (r : Runner) : IO Unit := do
  let s : Status := ⟨hex "8049f250", ⟨Array.replicate 32 1⟩, 7, ⟨Array.replicate 32 2⟩, 230, 4⟩
  let b := s.encode
  r.check "eth2: Status v2 has 92 bytes" (b.size == statusLen)
  r.check "eth2: Status v2 reads back"
    ((Status.decode? b).map (fun t => (t.forkDigest, t.finalizedEpoch, t.headRoot, t.headSlot,
      t.earliestAvailableSlot)) == some (s.forkDigest, 7, s.headRoot, 230, 4))
  r.check "eth2: a Status of 84 bytes is refused" (Status.decode? (b.extract 0 84)).isNone
  let m : MetaData := ⟨3, ⟨#[0x80, 0, 0, 0, 0, 0, 0, 1]⟩, ⟨#[0x0f]⟩, 128⟩
  r.check "eth2: MetaData v3 has 25 bytes and reads back"
    (m.encodeV3.size == 25 &&
      ((MetaData.decodeV3? m.encodeV3).map (fun t => (t.seqNumber, t.custodyGroupCount))) == some (3, 128))
  r.check "eth2: MetaData v2 has 17 bytes" (m.encodeV2.size == 17)

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
  let c := { (← devnetChain) with slotDurationMs := 12000, slotsPerEpoch := 32 }
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
  let digest ← expectOk "digest" (c.forkDigest 0)
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
  r.check "gossip: the subscription caps are Lighthouse's, for 203 topics a fork"
    (topicsPerFork == 203 && params.maxSubscriptionsPerRpc == some 406 &&
      params.maxSubscribedTopics == some 812)

/-! ## The fork schedule -/

private def forkChecks (r : Runner) : IO Unit := do
  let c0 ← devnetChain
  -- A Blob-Parameters-Only fork at epoch 10 changes the digest.
  let c := { c0 with blobSchedule := c0.blobSchedule ++
    [({ epoch := 10, maxBlobsPerBlock := 99 } : BlobEntry)] }
  let pre ← expectOk "digest" (c.forkDigest 9)
  let post ← expectOk "digest" (c.forkDigest 10)
  let run (st : ForkState) (epoch : Nat) : IO (List ForkAction × ForkState) :=
    expectOk "step" (st.step c epoch)
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
  let (a8, s8) ← run s0 8
  r.check "forks: two epochs before the fork, nothing is due" a8.isEmpty
  let (a9, s9) ← run s8 9
  r.check "forks: one epoch before the fork, the post-fork topics are joined"
    (a9.length == 1 && a9.all (isSub post) && s9.next == some post)
  let (a9b, _) ← run s9 9
  r.check "forks: a second look in the same epoch joins nothing" a9b.isEmpty
  let (a10, s10) ← run s9 10
  r.check "forks: at the fork, the digest switches with no second join"
    (a10.length == 1 && a10.all isSwitch && s10.current == post)
  let (a11, s11) ← run s10 11
  r.check "forks: one epoch after the fork, the pre-fork topics stay" a11.isEmpty
  let (a12, s12) ← run s11 12
  r.check "forks: two epochs after the fork, the pre-fork topics go"
    (a12.length == 1 && a12.all (isUnsub pre) && s12.retiring.isNone)
  let (late, _) ← run s8 10
  r.check "forks: a fork the loop did not see ahead joins and switches at once"
    (late.length == 2 && (late.head?.map (isSub post)) == some true &&
      (late.getLast?.map isSwitch) == some true)

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

/-- A service on loopback with a recorded event list. -/
private def startOn (c : Chain) (seed : UInt8) (events : OnceRef (List Event))
    (boot : List Enr := []) (serve : PeerId → Inbound → Emit → Async Ending := fun _ _ _ => pure .done) :
    Async Service := do
  let key ← expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 seed⟩)
  Service.start {
    chain := c, key, ip := [127, 0, 0, 1], tcpPort := 0, discPort := 0
    bootEnrs := boot, advert := { cgc := 4 }, discoverEveryMs := 500
    onEvent := fun e => events.update (· ++ [e]), serve }

private def serviceChecks (r : Runner) : Async Unit := do
  -- The genesis is now, so the wall-clock epoch is 0.
  let c ← devnetChain ((← wallMs) / 1000)
  let digest ← expectOk "digest" (c.forkDigest 0)
  let evA ← (OnceRef.new ([] : List Event) : BaseIO _)
  let evB ← (OnceRef.new ([] : List Event) : BaseIO _)
  -- A serves blocks of 404 bytes from `startSlot` on, each with our
  -- digest as its context. It tries two past `count`, and the service's
  -- cap refuses those two.
  let refused ← (OnceRef.new 0 : BaseIO (OnceRef Nat))
  let serve : PeerId → Inbound → Emit → Async Ending := fun _ req emit => do
    match req with
    | .blocksByRange start count =>
      for i in [0:count + 2] do
        if !(← emit digest ⟨Array.replicate 404 (start + i).toUInt8⟩) then
          (refused.update (· + 1) : BaseIO Unit)
      return .done
    -- The ancestry of the root, newest first: blocks 9, 8, ... here.
    | .blocksByHead root count =>
      if root.size == 32 then
        for i in [0:count] do
          discard <| emit digest ⟨Array.replicate 404 (9 - i).toUInt8⟩
      return .done
    -- One column, then the end of what A keeps.
    | .columnsByRange start _ _ =>
      discard <| emit digest ⟨Array.replicate 356 start.toUInt8⟩
      return .resourceUnavailable "pruned"
    | _ => return .done
  let a ← startOn c 1 evA (serve := serve)
  let b ← startOn c 2 evB [← (a.localEnr : BaseIO Enr)]
  let aPeer := a.base.host.localPeer
  let bPeer := b.base.host.localPeer
  let has (ev : OnceRef (List Event)) (f : Event → Bool) : Async Bool := do
    return (← (ev.get : BaseIO (List Event))).any f
  r.check "eth2 service: the boot record's peer connects"
    (← waitUntil (has evB fun | .connected p true => p == aPeer | _ => false) 5000)
  r.check "eth2 service: the listener sees the inbound peer"
    (← waitUntil (has evA fun | .connected p false => p == bPeer | _ => false) 5000)
  r.check "eth2 service: the dialer gets the listener's Status"
    (← waitUntil (has evB fun | .status p s => p == aPeer && s.forkDigest == digest | _ => false) 5000)
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
  match ← b.request aPeer blocksByRangeMethod (some (blocksByRangeRequest 10 3)) with
  | .ok chunks =>
    r.check "eth2 service: the range request gets three chunks" (chunks.length == 3)
    r.check "eth2 service: each chunk carries our digest as context"
      (chunks.all (·.context == digest))
    r.check "eth2 service: the chunks keep their order"
      (chunks.map (·.payload.get! 0) == [10, 11, 12])
    r.check "eth2 service: the cap refuses the two chunks past count" ((← refused.get) == 2)
  | .error _ => r.check "eth2 service: the range request answers" false
  -- A check that refuses the second block ends the read there.
  let checked ← (OnceRef.new ([] : List Nat) : BaseIO (OnceRef (List Nat)))
  let each ← b.requestEach aPeer blocksByRangeMethod (some (blocksByRangeRequest 10 3)) fun c => do
    (checked.update (· ++ [(c.payload.get! 0).toNat]) : BaseIO Unit)
    return c.payload.get! 0 != 11
  r.check "eth2 service: a check of each chunk stops the read at the refused block"
    ((match each with | .ok () => true | .error _ => false) && (← checked.get) == [10, 11])
  match ← b.request aPeer columnsByRangeMethod (some (columnsByRangeRequest 5 1 [1, 2])) with
  | .ok chunks =>
    r.check "eth2 service: a column range ends with ResourceUnavailable after its column"
      (chunks.map (·.result) == [.success, .resourceUnavailable] &&
        (chunks.getLast?.map (·.payload)) == some "pruned".toUTF8)
  | .error _ => r.check "eth2 service: the column range request answers" false
  match ← b.request aPeer blocksByHeadMethod (some (blocksByHeadRequest ⟨Array.replicate 32 1⟩ 3)) with
  | .ok chunks =>
    r.check "eth2 service: the head request gets the ancestry, newest first"
      (chunks.map (·.payload.get! 0) == [9, 8, 7] && chunks.all (·.context == digest))
  | .error _ => r.check "eth2 service: the head request answers" false
  match ← b.request aPeer goodbyeMethod (some (Chain.le64 3)) with
  | .ok chunks =>
    r.check "eth2 service: Goodbye answers one chunk of 0, as the spec asks"
      (chunks.map (·.payload) == [Chain.le64 0])
  | .error _ => r.check "eth2 service: Goodbye answers" false
  match ← b.request aPeer metadataV3Method none with
  | .ok [m] =>
    r.check "eth2 service: MetaData v3 names the custody"
      ((MetaData.decodeV3? m.payload).map (·.custodyGroupCount) == some 4)
  | _ => r.check "eth2 service: MetaData v3 answers" false
  match ← b.request aPeer pingMethod (some (Chain.le64 0)) with
  | .ok [p] => r.check "eth2 service: Ping answers the seq number" (p.payload == Chain.le64 0)
  | _ => r.check "eth2 service: Ping answers" false
  -- Liveness: the first Ping of a peer brings its MetaData, since we
  -- know none of it yet. The second finds the same seq number.
  b.base.ping aPeer
  b.base.ping aPeer
  let metas := (← (evB.get : BaseIO (List Event))).filter fun
    | .metaData p _ => p == aPeer
    | _ => false
  r.check "eth2 service: a Ping with a new seq number brings MetaData once"
    (match metas with
     | [.metaData _ md] => md.custodyGroupCount == 4
     | _ => false)
  r.check "eth2 service: an answered Ping is no unresponsive event"
    (!(← has evB fun | .unresponsive _ => true | _ => false))
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

/-- A fork on a live service: 1 s slots, 2 slots per epoch, and a
Blob-Parameters-Only fork at epoch 2, 4 s after genesis. The fork loop
joins the post-fork topic at epoch 1, switches at epoch 2, and leaves the
pre-fork topic at epoch 4. The run takes about 9 s. -/
private def liveForkChecks (r : Runner) : Async Unit := do
  let c0 ← devnetChain ((← wallMs) / 1000)
  let c := { c0 with slotDurationMs := 1000, slotsPerEpoch := 2
                     blobSchedule := c0.blobSchedule ++
                       [({ epoch := 2, maxBlobsPerBlock := 99 } : BlobEntry)] }
  let pre ← expectOk "digest" (c.forkDigest 0)
  let post ← expectOk "digest" (c.forkDigest 2)
  let ev ← (OnceRef.new ([] : List Event) : BaseIO _)
  let a ← startOn c 4 ev
  r.check "eth2 fork: the subscribe posts" (← a.subscribe .beaconBlock)
  let topics (n : Nat) : Async Bool := do
    match ← a.gossip.stats with
    | some st => return st.topics == n
    | none => return false
  r.check "eth2 fork: ahead of the fork, both digests carry the topic" (← waitUntil (topics 2) 5000)
  let switched : Async Bool := do
    return (← (a.base.status.get : BaseIO Status)).forkDigest == post
  r.check "eth2 fork: at the fork, our Status names the new digest" (← waitUntil switched 5000)
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
  let c ← devnetChain ((← wallMs) / 1000)
  let ev ← (OnceRef.new ([] : List Event) : BaseIO _)
  let key ← expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 9⟩)
  let a ← Service.start {
    chain := c, key, ip := [127, 0, 0, 1], tcpPort := 0, discPort := 0, advert := { cgc := 4 }
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

def run (r : Runner) : IO Unit := do
  r.section "eth2" "vendor/consensus-specs: specs/*/p2p-interface.md to fulu, fulu beacon-chain.md"
  chainChecks r
  messageIdChecks r
  messageChecks r
  scoringChecks r
  forkChecks r
  peersChecks r
  Async.run (serviceChecks r)
  Async.run (liveForkChecks r)
  Async.run (limitChecks r)

end Tests.Eth2
