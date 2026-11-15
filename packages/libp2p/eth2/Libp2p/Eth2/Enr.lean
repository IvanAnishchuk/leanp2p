import Libp2p.Identity
import Libp2p.Eth2.Fork

/-!
# The consensus fields of an ENR

A consensus node's record carries, beside the EIP-778 keys:

| key | value | spec |
|---|---|---|
| `eth2` | the 16-byte SSZ of `ENRForkID` | phase0 and fulu, "`eth2` field" |
| `attnets` | `Bitvector[64]`, 8 bytes | phase0, "Attestation subnet bitfield" |
| `syncnets` | `Bitvector[4]`, 1 byte | altair, "Sync committee bitfield" |
| `cgc` | the custody group count, big-endian with no leading zero | fulu, "Custody group count" |
| `nfd` | the 4-byte digest of the next fork | fulu, "Next fork digest" |

The ports `tcp`, `quic`, and `udp` and the address keys are the job of
`Libp2p.Identity.Enr` (`consensusPairs`, `dialAddrs`). An `attnets` of
all zeros may stay out ("MAY optionally include"). This module always
writes it, as Lighthouse does.

"Clients SHOULD connect to peers with `fork_digest`,
`next_fork_version`, and `next_fork_epoch` that match local values."
`sameFork` compares the whole `ENRForkID`, and `sameDigest` the digest
alone, which the spec's "MAY connect" case allows.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Identity

/-- The keys of the consensus fields. -/
def eth2Key : Enr.Key := Enr.Key.ofName Constants.nameEth2
def attnetsKey : Enr.Key := Enr.Key.ofName Constants.nameAttnets
def syncnetsKey : Enr.Key := Enr.Key.ofName Constants.nameSyncnets
def cgcKey : Enr.Key := Enr.Key.ofName Constants.nameCgc
def nfdKey : Enr.Key := Enr.Key.ofName Constants.nameNfd

/-- What a node advertises about its subnets and its custody. -/
structure Advert where
  /-- `attnets`: bit `i` of byte `i / 8` (SSZ bit order) for subnet `i`. -/
  attnets : ByteArray := ⟨Array.replicate 8 0⟩
  /-- `syncnets`: the low 4 bits. -/
  syncnets : ByteArray := ⟨#[0]⟩
  /-- `custody_group_count`. -/
  cgc : Nat

/-- The bytes of an item. -/
private def bytesItem (b : ByteArray) : Rlp.Item := .bytes (b.toList.map (·.toNat))

/-- The consensus pairs of the node's record at `epoch`. -/
def advertPairs (c : Chain) (epoch : Nat) (a : Advert) : List Enr.Pair :=
  [⟨eth2Key, bytesItem (c.enrForkId epoch)⟩,
   ⟨attnetsKey, bytesItem a.attnets⟩,
   ⟨syncnetsKey, bytesItem a.syncnets⟩,
   ⟨cgcKey, .bytes (Rlp.ofScalar a.cgc)⟩,
   ⟨nfdKey, bytesItem (c.nextForkDigest epoch)⟩]

/-- The byte string under `k`, or `none`. -/
def bytesOf? (r : Enr) (k : Enr.Key) : Option ByteArray :=
  match r.get? k with
  | some (.bytes b) => some ⟨b.toArray.map (·.toUInt8)⟩
  | _ => none

/-- The `ENRForkID` of a record, when it has 16 bytes. -/
def enrForkId? (r : Enr) : Option ByteArray := do
  let b ← bytesOf? r eth2Key
  if b.size == Constants.enrForkIdLen then some b else none

/-- The fork digest of a record. -/
def forkDigest? (r : Enr) : Option ByteArray := (enrForkId? r).map (·.extract 0 4)

/-- The custody group count of a record: a minimal big-endian scalar of
at most 8 bytes. -/
def cgc? (r : Enr) : Option Nat := do
  match r.get? cgcKey with
  | some (.bytes b) => Rlp.scalar? 8 b
  | _ => none

/-- The `attnets` bitvector of a record, when it has 8 bytes. -/
def attnets? (r : Enr) : Option ByteArray := do
  let b ← bytesOf? r attnetsKey
  if b.size == 8 then some b else none

/-- Whether bit `i` of an SSZ bitvector is set: bit `i % 8` of byte
`i / 8`. -/
def bitSet (b : ByteArray) (i : Nat) : Bool :=
  i / 8 < b.size && (b.get! (i / 8)).toNat / 2 ^ (i % 8) % 2 == 1

/-- The record's digest is our digest at `epoch`. -/
def sameDigest (c : Chain) (epoch : Nat) (r : Enr) : Bool :=
  forkDigest? r == some (c.forkDigest epoch)

/-- The record's whole `ENRForkID` is ours at `epoch`. -/
def sameFork (c : Chain) (epoch : Nat) (r : Enr) : Bool :=
  enrForkId? r == some (c.enrForkId epoch)

#guard bitSet ⟨#[0x80, 0x01]⟩ 7 && bitSet ⟨#[0x80, 0x01]⟩ 8 && !bitSet ⟨#[0x80, 0x01]⟩ 0

end Libp2p.Eth2
