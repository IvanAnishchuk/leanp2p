import Crypto
import Libp2p.Eth2.Constants

/-!
# The fork schedule and the fork digest

A consensus node names its chain and its fork on the wire by a 4-byte
`ForkDigest`. The topics carry it, the `Status` handshake compares it,
the ENR `eth2` field holds it, and the `ForkDigest`-context of a
req/resp chunk is one. This module computes it from the chain's config.

* `compute_fork_version` (fulu `p2p-interface.md`): the version of the
  last fork whose epoch has come.
* `compute_fork_data_root` (phase0 `beacon-chain.md`): the
  `hash_tree_root` of `ForkData(current_version, genesis_validators_root)`.
  The container has two 32-byte chunks, the version padded with zeros
  and the root. So the root is one SHA-256 of the 64 bytes.
* `compute_fork_digest` (fulu `beacon-chain.md`, EIP-7892): the first 4
  bytes of that root. From `FULU_FORK_EPOCH` on, the digest is XORed
  with the first 4 bytes of `sha256(epoch ‖ max_blobs_per_block)` of the
  blob schedule entry in force, both as little-endian `Uint64`. So a
  Blob-Parameters-Only fork changes the digest with no new version.

The config values are data the client reads from its `config.yaml`
(`Libp2p.Eth2.Config`). This module holds no network's numbers.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

/-- A fork after genesis: its epoch and its 4-byte version. -/
structure Fork where
  epoch : Nat
  version : ByteArray

/-- One entry of `BLOB_SCHEDULE` (fulu `beacon-chain.md`, EIP-7892). -/
structure BlobEntry where
  epoch : Nat
  maxBlobsPerBlock : Nat

/-- The chain as the networking layer sees it. -/
structure Chain where
  /-- `GENESIS_FORK_VERSION`. -/
  genesisVersion : ByteArray
  /-- The forks after genesis in config order, Altair first. A fork at
  `FAR_FUTURE_EPOCH` is not scheduled, and the reader leaves it out. -/
  forks : List Fork
  /-- `ELECTRA_FORK_EPOCH` and `MAX_BLOBS_PER_BLOCK_ELECTRA`: the blob
  parameters before the first schedule entry (`get_blob_parameters`). -/
  electraEpoch : Nat
  maxBlobsElectra : Nat
  /-- `FULU_FORK_EPOCH`, when scheduled. -/
  fuluEpoch : Option Nat
  /-- `BLOB_SCHEDULE`. -/
  blobSchedule : List BlobEntry
  /-- `SLOT_DURATION_MS`. -/
  slotDurationMs : Nat
  /-- `SLOTS_PER_EPOCH` of the preset. -/
  slotsPerEpoch : Nat
  /-- `state.genesis_validators_root`. -/
  genesisValidatorsRoot : ByteArray
  /-- `state.genesis_time`, in seconds. -/
  genesisTime : Nat

namespace Chain

/-- The 8 little-endian bytes of a `Uint64`. -/
def le64 (n : Nat) : ByteArray :=
  ⟨(List.range 8).map (fun i => (n / 256 ^ i % 256).toUInt8) |>.toArray⟩

/-- `compute_fork_version(epoch)`: the version of the last fork in
config order whose epoch has come. Later forks win a tie, so a devnet
that starts every fork at epoch 0 runs the last one. -/
def forkVersion (c : Chain) (epoch : Nat) : ByteArray :=
  c.forks.foldl (fun v f => if f.epoch ≤ epoch then f.version else v) c.genesisVersion

/-- `compute_fork_data_root(version, genesis_validators_root)`. -/
def forkDataRoot (version gvr : ByteArray) : Except Crypto.CryptoError ByteArray :=
  Crypto.sha256 (version ++ ⟨Array.replicate 28 0⟩ ++ gvr)

/-- `get_blob_parameters(epoch)`: the schedule entry with the largest
epoch that has come, or Electra's parameters before every entry. -/
def blobParameters (c : Chain) (epoch : Nat) : BlobEntry :=
  let due := c.blobSchedule.filter (·.epoch ≤ epoch)
  due.foldl (fun b e => if b.epoch ≤ e.epoch then e else b) ⟨c.electraEpoch, c.maxBlobsElectra⟩

/-- `compute_fork_digest(genesis_validators_root, epoch)`, Fulu's
form. -/
def forkDigest (c : Chain) (epoch : Nat) : Except Crypto.CryptoError ByteArray := do
  let base := (← forkDataRoot (c.forkVersion epoch) c.genesisValidatorsRoot).extract 0 4
  match c.fuluEpoch with
  | some f =>
    if epoch < f then return base
    let b := c.blobParameters epoch
    let mask := (← Crypto.sha256 (le64 b.epoch ++ le64 b.maxBlobsPerBlock)).extract 0 4
    return ⟨(List.range 4).map (fun i => base.get! i ^^^ mask.get! i) |>.toArray⟩
  | none => return base

/-- The epoch of the next fork after `epoch`, a regular fork or a
Blob-Parameters-Only fork, or `FAR_FUTURE_EPOCH` when none is planned
(fulu, "`eth2` field"). -/
def nextForkEpoch (c : Chain) (epoch : Nat) : Nat :=
  let regular := c.forks.map (·.epoch)
  let bpo := match c.fuluEpoch with
    | some f => (c.blobSchedule.map (·.epoch)).filter (f ≤ ·)
    | none => []
  (regular ++ bpo).foldl (fun n e => if epoch < e && e < n then e else n) Constants.farFutureEpoch

/-- The SSZ of `ENRForkID` at `epoch`: the digest, the next fork's
version, and the next fork's epoch (phase0 and fulu, "`eth2` field").
With no next fork, the version is the current one. -/
def enrForkId (c : Chain) (epoch : Nat) : Except Crypto.CryptoError ByteArray := do
  let next := c.nextForkEpoch epoch
  let version := if next == Constants.farFutureEpoch then c.forkVersion epoch else c.forkVersion next
  return (← c.forkDigest epoch) ++ version ++ le64 next

/-- The ENR `nfd` value at `epoch`: the digest of the next fork, or 4
zero bytes when none is planned (fulu, "Next fork digest"). -/
def nextForkDigest (c : Chain) (epoch : Nat) : Except Crypto.CryptoError ByteArray := do
  let next := c.nextForkEpoch epoch
  if next == Constants.farFutureEpoch then return ⟨#[0, 0, 0, 0]⟩
  c.forkDigest next

/-- The epoch at Unix time `nowMs`, epoch 0 before genesis. -/
def epochAt (c : Chain) (nowMs : Nat) : Nat :=
  let sinceMs := nowMs - c.genesisTime * 1000
  sinceMs / (max c.slotDurationMs 1) / (max c.slotsPerEpoch 1)

/-- The epoch of `slot`. -/
def epochOfSlot (c : Chain) (slot : Nat) : Nat := slot / (max c.slotsPerEpoch 1)

end Chain

end Libp2p.Eth2
