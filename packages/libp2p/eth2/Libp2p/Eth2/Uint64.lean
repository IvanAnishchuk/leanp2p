/-!
# The little-endian `Uint64`

The consensus networking spec writes three numbers as 8 little-endian
bytes: the topic length in the message id (`uint64_le`), and the
payloads of `Ping` and `Goodbye`, each "a single SSZ-field".
-/

set_option autoImplicit false

namespace Libp2p.Eth2

/-- The 8 little-endian bytes of a `Uint64`. -/
def le64 (n : Nat) : ByteArray :=
  ⟨(List.range 8).map (fun i => (n / 256 ^ i % 256).toUInt8) |>.toArray⟩

/-- The little-endian `Uint64` at byte `i`. -/
def le64At (b : ByteArray) (i : Nat) : Nat :=
  (List.range 8).foldl (fun n k => n + (b.get! (i + k)).toNat * 256 ^ k) 0

#guard le64At (le64 (2 ^ 64 - 2)) 0 == 2 ^ 64 - 2
#guard le64 1 == ⟨#[1, 0, 0, 0, 0, 0, 0, 0]⟩

end Libp2p.Eth2
