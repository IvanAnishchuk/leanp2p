import Libp2p.Eth2.Constants

/-!
# The fork schedule

A consensus node names its chain and its fork on the wire by a 4-byte
`ForkDigest`. The topics carry it, the `Status` handshake compares it,
the ENR `eth2` field holds it, and the `ForkDigest`-context of a
req/resp chunk is one.

The client computes each digest (`compute_fork_digest`) and the SSZ of
each `ENRForkID` from its chain, and it hands the schedule to the
service as a `Chain`. This module only looks values up in it: the entry
in force at an epoch, and the next one. It also maps wall-clock time to
epochs, which the fork loop and the gossip parameters need.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

/-- One entry of the fork schedule, a regular fork or a
Blob-Parameters-Only fork (EIP-7892). The client computes both values. -/
structure ForkEntry where
  /-- The first epoch of the entry. -/
  epoch : Nat
  /-- The `ForkDigest` from `epoch` on, 4 bytes. -/
  digest : ByteArray
  /-- The ENR `eth2` value from `epoch` on: the 16-byte SSZ of
  `ENRForkID` (phase0 and fulu, "`eth2` field"). -/
  enrForkId : ByteArray

/-- The chain as the network layer sees it. -/
structure Chain where
  /-- The schedule by ascending epoch. The first entry has epoch 0. -/
  schedule : List ForkEntry
  /-- `SLOT_DURATION_MS`. -/
  slotDurationMs : Nat
  /-- `SLOTS_PER_EPOCH` of the preset. -/
  slotsPerEpoch : Nat
  /-- `genesis_time`, in seconds. -/
  genesisTime : Nat

namespace Chain

/-- The schedule starts at epoch 0, its epochs ascend strictly, and each
digest and `ENRForkID` has its width. The slot and the epoch are not
empty. The service refuses a chain that fails this. -/
def wellFormed (c : Chain) : Bool :=
  let epochs := c.schedule.map (·.epoch)
  epochs.head? == some 0 &&
    (epochs.zip epochs.tail).all (fun (a, b) => a < b) &&
    c.schedule.all (fun e => e.digest.size == 4 && e.enrForkId.size == Constants.enrForkIdLen) &&
    0 < c.slotDurationMs && 0 < c.slotsPerEpoch

/-- The entry in force at `epoch`: the last one whose epoch has come. -/
def entryAt? (c : Chain) (epoch : Nat) : Option ForkEntry :=
  c.schedule.foldl (fun acc e => if e.epoch ≤ epoch then some e else acc) none

/-- The first entry after `epoch`. -/
def nextEntry? (c : Chain) (epoch : Nat) : Option ForkEntry :=
  c.schedule.find? (epoch < ·.epoch)

/-- Our digest at `epoch`. A well-formed chain has an entry at every
epoch, so the 4 zero bytes never go out. -/
def forkDigest (c : Chain) (epoch : Nat) : ByteArray :=
  ((c.entryAt? epoch).map (·.digest)).getD ⟨#[0, 0, 0, 0]⟩

/-- Our `ENRForkID` at `epoch`. -/
def enrForkId (c : Chain) (epoch : Nat) : ByteArray :=
  ((c.entryAt? epoch).map (·.enrForkId)).getD ⟨Array.replicate Constants.enrForkIdLen 0⟩

/-- The epoch of the next entry, or `FAR_FUTURE_EPOCH` when none is
planned. -/
def nextForkEpoch (c : Chain) (epoch : Nat) : Nat :=
  ((c.nextEntry? epoch).map (·.epoch)).getD Constants.farFutureEpoch

/-- The ENR `nfd` value at `epoch`: the digest of the next entry, or 4
zero bytes when none is planned (fulu, "Next fork digest"). -/
def nextForkDigest (c : Chain) (epoch : Nat) : ByteArray :=
  ((c.nextEntry? epoch).map (·.digest)).getD ⟨#[0, 0, 0, 0]⟩

/-- The digests from `epoch` on: ours, then each later one. -/
def digestsFrom (c : Chain) (epoch : Nat) : List ByteArray :=
  (c.entryAt? epoch).toList.map (·.digest) ++ (c.schedule.filter (epoch < ·.epoch)).map (·.digest)

/-- The epoch at Unix time `nowMs`, epoch 0 before genesis. -/
def epochAt (c : Chain) (nowMs : Nat) : Nat :=
  let sinceMs := nowMs - c.genesisTime * 1000
  sinceMs / (max c.slotDurationMs 1) / (max c.slotsPerEpoch 1)

/-- The epoch of `slot`. -/
def epochOfSlot (c : Chain) (slot : Nat) : Nat := slot / (max c.slotsPerEpoch 1)

end Chain

end Libp2p.Eth2
