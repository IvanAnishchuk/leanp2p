import Bytes
import Libp2p.Identity

/-!
# discv5: the node table

The Kademlia table of devp2p `discv5-theory.md`, "Node Table": for each
`0 ≤ i < 256` a k-bucket of the nodes at `logdistance(self, n) = i + 1`,
with `k = 16`, and a replacement cache beside each bucket ("Table
Maintenance In Practice"). The table is pure data; the shell keeps it in
the protocol core's state.

A bucket lists its entries most recently seen first. An insert into a
full bucket goes to the replacement cache; a `remove` (a node that
failed its liveness check) promotes the most recent replacement.
-/

set_option autoImplicit false

namespace Libp2p.Discv5

open Bytes Libp2p.Identity

/-- `k`, the bucket size. -/
def bucketSize : Nat := 16

/-- The replacement cache size per bucket. -/
def replacementSize : Nat := 16

/-- The big-endian number of a 32-byte id. -/
def idNat (id : ByteArray) : Nat := id.foldl (fun n b => n * 256 + b.toNat) 0

/-- `logdistance(a, b)`: the bit length of `a XOR b`, 0 for equal ids. -/
def logDistance (a b : ByteArray) : Nat :=
  (Nat.xor (idNat a) (idNat b)).log2 + (if idNat a == idNat b then 0 else 1)

/-- One table entry: the node id and its newest record. -/
structure Entry where
  id : ByteArray
  record : Enr

/-- The table. -/
structure Table where
  localId : ByteArray
  buckets : Array (List Entry) := Array.replicate 256 []
  replacements : Array (List Entry) := Array.replicate 256 []

namespace Table

/-- An empty table around `localId`. -/
def empty (localId : ByteArray) : Table := { localId }

/-- The bucket index of a node: `logdistance - 1`; `none` for ourselves. -/
def bucketOf (t : Table) (id : ByteArray) : Option Nat :=
  match logDistance t.localId id with
  | 0 => none
  | d + 1 => some d

/-- Insert or refresh a record. A known node moves to the front with the
newer record; a new node joins the front of a bucket with room, or else
the replacement cache. -/
def insert (t : Table) (e : Entry) : Table :=
  match t.bucketOf e.id with
  | none => t
  | some i =>
    let b := t.buckets[i]!
    if b.any (·.id == e.id) then
      let old := (b.find? (·.id == e.id)).map (·.record.seq) |>.getD 0
      let e := if e.record.seq ≥ old then e else (b.find? (·.id == e.id)).getD e
      { t with buckets := t.buckets.set! i (e :: b.filter (·.id != e.id)) }
    else if b.length < bucketSize then
      { t with buckets := t.buckets.set! i (e :: b) }
    else
      let r := (e :: t.replacements[i]!.filter (·.id != e.id)).take replacementSize
      { t with replacements := t.replacements.set! i r }

/-- Remove a node, as after a failed liveness check, and promote the most
recent replacement of its bucket. -/
def remove (t : Table) (id : ByteArray) : Table :=
  match t.bucketOf id with
  | none => t
  | some i =>
    let b := t.buckets[i]!.filter (·.id != id)
    match t.replacements[i]! with
    | r :: rs => { t with buckets := t.buckets.set! i (b ++ [r]), replacements := t.replacements.set! i rs }
    | [] => { t with buckets := t.buckets.set! i b }

/-- The records at log distance `d` from us; `d = 0` is ours, which the
caller adds. -/
def atDistance (t : Table) (d : Nat) : List Enr :=
  if d = 0 || d > 256 then [] else (t.buckets[d - 1]!).map (·.record)

/-- Every entry. -/
def entries (t : Table) : List Entry := t.buckets.toList.flatten

/-- The `n` known nodes closest to `target` by XOR distance. -/
def closest (t : Table) (target : ByteArray) (n : Nat) : List Entry :=
  let tn := idNat target
  (t.entries.mergeSort fun a b => Nat.xor (idNat a.id) tn ≤ Nat.xor (idNat b.id) tn).take n

/-- The number of nodes in the buckets. -/
def size (t : Table) : Nat := t.entries.length

end Table

end Libp2p.Discv5
