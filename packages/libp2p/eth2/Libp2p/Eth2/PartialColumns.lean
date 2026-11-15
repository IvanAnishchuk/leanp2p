import Libp2p.Identity
import Libp2p.Eth2.Constants

/-!
# Partial columns

Fulu sends a data column in parts over gossipsub's partial messages
(fulu `partial-columns/p2p-interface.md`). The gossipsub layer carries a
group ID, parts metadata, and a message, each opaque to it.

* **The group ID** is the version byte `0x00`, then the 32-byte block
  root. "Implementations MUST ignore unknown versions." This module
  builds and reads it, so the service can name the block and drop an
  unknown version.
* **The parts metadata** and **the message** are the SSZ of
  `PartialDataColumnPartsMetadata` and `PartialDataColumnSidecar`. The
  client encodes and decodes them, validates the cells, and decides
  what each peer gets.

The service keeps one rule of the spec for the client: "Clients SHOULD
limit the rate at which a peer gets the first message delivery reward".
A peer earns the reward once per block and column (`Rewards.earn`). The
state keeps the latest `Constants.partialColumnBlocks` blocks, the bound
of Lighthouse's header tracker (`partial_column_header_tracker.rs`).
-/

set_option autoImplicit false

namespace Libp2p.Eth2.PartialColumns

open Libp2p.Identity (PeerId)

/-- The width of a block root. -/
def rootLen : Nat := 32

/-- The group ID of a block root: the version byte, then the root. -/
def groupIdOf (root : ByteArray) : ByteArray :=
  ByteArray.mk #[Constants.partialColumnsVersion] ++ root

/-- The block root of a group ID. `none` for an unknown version or
another length: "Implementations MUST ignore unknown versions." -/
def rootOf? (gid : ByteArray) : Option ByteArray :=
  if gid.size == rootLen + 1 && gid.get! 0 == Constants.partialColumnsVersion then
    some (gid.extract 1 (rootLen + 1))
  else none

/-- The first-delivery rewards of the latest blocks: each block root,
newest first, with the columns and peers that earned. -/
structure Rewards where
  blocks : List (ByteArray × List (Nat × PeerId)) := []

/-- Whether `peer` earns the first-delivery reward for `column` of the
block `root`, and the state after. A block the state does not hold goes
first, and the oldest block past the bound goes out. -/
def Rewards.earn (r : Rewards) (peer : PeerId) (root : ByteArray) (column : Nat) : Bool × Rewards :=
  match r.blocks.find? (·.1 == root) with
  | some (_, earned) =>
    if earned.contains (column, peer) then (false, r)
    else (true, { blocks := r.blocks.map fun (b, e) => if b == root then (b, (column, peer) :: e) else (b, e) })
  | none => (true, { blocks := ((root, [(column, peer)]) :: r.blocks).take Constants.partialColumnBlocks })

#guard rootOf? (groupIdOf ⟨Array.replicate 32 7⟩) == some ⟨Array.replicate 32 7⟩
#guard rootOf? (ByteArray.mk #[1] ++ ⟨Array.replicate 32 7⟩) == none
#guard rootOf? ⟨Array.replicate 32 0⟩ == none

end Libp2p.Eth2.PartialColumns
