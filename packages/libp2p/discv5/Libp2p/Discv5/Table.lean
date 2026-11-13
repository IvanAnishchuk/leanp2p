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

Two client policies guard against eclipse attacks, with Lighthouse's
numbers: a /24 of global IPv4 addresses holds at most 2 places in a
bucket and 10 in the table, and nodes that contacted us take at most
half a bucket.
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

/-- One table entry: the node id, its newest record, and whether it has
ever answered our PING. FINDNODE relays only live entries
(discv5-theory.md, "Table Maintenance In Practice": "implementations must
avoid relaying any nodes whose liveness has not been verified"). -/
structure Entry where
  id : ByteArray
  record : Enr
  live : Bool := false
  /-- The node contacted us first (it came in through our challenge). -/
  incoming : Bool := false

/-- The nodes of one /24 a bucket takes, and the whole table takes: the
eclipse limits of the sigp discv5 crate Lighthouse runs (`ip_limit`) and
of geth. They are client policy; the spec sets none. -/
def subnetBucketLimit : Nat := 2
def subnetTableLimit : Nat := 10

/-- The incoming nodes a bucket takes: half the bucket, as Lighthouse
sets `incoming_bucket_limit(8)`, so peers that contact us cannot fill
it. -/
def incomingLimit : Nat := 8

/-- An IPv4 address outside the loopback, private, link-local, shared,
and unspecified ranges. The subnet limits apply only to these, as geth
exempts LAN addresses, so a local network still works. -/
def isGlobal4 : List Nat → Bool
  | [a, b, _, _] =>
    !(a == 0 || a == 10 || a == 127 || (a == 169 && b == 254) || (a == 172 && 16 ≤ b && b ≤ 31) ||
      (a == 192 && b == 168) || (a == 100 && 64 ≤ b && b ≤ 127))
  | _ => false

/-- The /24 of a record's global IPv4 address. -/
def subnet24? (e : Enr) : Option (List Nat) :=
  match (e.ip?).toOption.join with
  | some ip => if isGlobal4 ip then some (ip.take 3) else none
  | none => none

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
    if let some prev := b.find? (·.id == e.id) then
      -- The newer record wins; a node once live stays live.
      let rec_ := if e.record.seq ≥ prev.record.seq then e.record else prev.record
      let e : Entry := { e with record := rec_, live := e.live || prev.live, incoming := prev.incoming }
      { t with buckets := t.buckets.set! i (e :: b.filter (·.id != e.id)) }
    else
      -- A new node: past a subnet limit it is refused outright.
      let sameNet (x : Entry) : Bool := subnet24? x.record == subnet24? e.record
      let overNet := match subnet24? e.record with
        | some _ => (b.filter sameNet).length ≥ subnetBucketLimit ||
            ((t.buckets.toList.flatten).filter sameNet).length ≥ subnetTableLimit
        | none => false
      let overIncoming := e.incoming && (b.filter (·.incoming)).length ≥ incomingLimit
      if overNet then t
      else if b.length < bucketSize && !overIncoming then
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

/-- Mark a node live: it answered our PING. A node not in a bucket is
left as it is. -/
def markLive (t : Table) (id : ByteArray) : Table :=
  match t.bucketOf id with
  | none => t
  | some i => { t with buckets := t.buckets.modify i (·.map fun e => if e.id == id then { e with live := true } else e) }

/-- The live records at log distance `d` from us; `d = 0` is ours, which
the caller adds. -/
def atDistance (t : Table) (d : Nat) : List Enr :=
  if d = 0 || d > 256 then [] else ((t.buckets[d - 1]!).filter (·.live)).map (·.record)

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
