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
    (messageIdBytes topic ⟨#[0xff, 0xff, 0xff]⟩ == hex "cdeedbbf61c3f27499d55d88a971e19d2e1da339")
  let raw := "hello consensus".toUTF8
  let data ← expectOk "snappy compress" (Snappy.compress raw)
  r.check "eth2: compressed data takes the valid domain over the raw bytes"
    (messageIdBytes topic data == hex "b4ba60d2bba298249bed48c66fb8611d872e9dbc")
  r.check "eth2: the message id has 20 bytes" ((messageId topic data).bytes.length == 20)
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

/-- A service on loopback with a recorded event list. -/
private def startOn (c : Chain) (seed : UInt8) (events : OnceRef (List Event))
    (boot : List Enr := []) (serve : PeerId → Inbound → Emit → Async Unit := fun _ _ _ => pure ()) :
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
  -- A serves `count` blocks of 404 bytes from `startSlot` on, each with
  -- our digest as its context.
  let serve : PeerId → Inbound → Emit → Async Unit := fun _ req emit => do
    match req with
    | .blocksByRange start count =>
      for i in [0:count] do
        discard <| emit digest ⟨Array.replicate 404 (start + i).toUInt8⟩
    | _ => pure ()
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
  -- Gossip: both subscribe, and B publishes once A is in B's mesh.
  r.check "eth2 service: the subscribes post" ((← a.subscribe .beaconBlock) && (← b.subscribe .beaconBlock))
  -- A burst past the control queue of the gossipsub node (`inputSlots`,
  -- 64): every post parks until the loop takes it, so none is lost.
  let burst ← (List.range Constants.dataColumnSidecarSubnetCount).allM fun i =>
    a.subscribe (.dataColumnSidecar i)
  r.check "eth2 service: a burst of 128 subscribes loses none" burst
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
      some (messageId (← (a.topic .beaconBlock : IO Libp2p.Protocols.Gossipsub.TopicId)).name data))
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
  | .error _ => r.check "eth2 service: the range request answers" false
  match ← b.request aPeer metadataV3Method none with
  | .ok [m] =>
    r.check "eth2 service: MetaData v3 names the custody"
      ((MetaData.decodeV3? m.payload).map (·.custodyGroupCount) == some 4)
  | _ => r.check "eth2 service: MetaData v3 answers" false
  match ← b.request aPeer pingMethod (some (Chain.le64 0)) with
  | .ok [p] => r.check "eth2 service: Ping answers the seq number" (p.payload == Chain.le64 0)
  | _ => r.check "eth2 service: Ping answers" false
  -- Goodbye at stop.
  b.stop
  r.check "eth2 service: the stop says Goodbye with reason 1"
    (← waitUntil (has evA fun | .goodbye p 1 => p == bPeer | _ => false) 5000)
  r.check "eth2 service: the listener sees the peer leave"
    (← waitUntil (has evA fun | .disconnected p => p == bPeer | _ => false) 5000)
  a.stop

def run (r : Runner) : IO Unit := do
  r.section "eth2" "vendor/consensus-specs: specs/*/p2p-interface.md to fulu, fulu beacon-chain.md"
  chainChecks r
  messageIdChecks r
  messageChecks r
  Async.run (serviceChecks r)

end Tests.Eth2
