import Std.Data.HashMap

/-!
# Req/resp: the responder's rate limit

"The responder MAY rate-limit chunks by withholding each chunk until
capacity is available. The responder MUST NOT respond with an error or
close the stream when rate limiting" (phase0 `p2p-interface.md`,
"Responding side"). The spec's rationale names "a two-level token/leaky
bucket with a per-peer limit and a global limit", with a cost per chunk
as the finer choice.

A bucket here is the generic cell rate algorithm (GCRA), as Lighthouse's
`rpc/rate_limiter.rs` runs it. A `Quota` of `tokens` per `periodMs`
gives back one token every `periodMs / tokens`, and a full bucket holds
`tokens`. The state of a key is one number, its theoretical arrival
time (TAT): the time at which its bucket is full again.

`reserve` takes one token at once and answers how long the chunk waits.
A reservation moves the TAT forward, so two chunks that reserve at the
same time get different waits. The shell applies each reservation in
one `OnceRef.updateGet` (ARCHITECTURE §4.1, rule 3), then waits, then
sends. A key with no entry has a full bucket.

Times are microseconds, so a quota of 128 per 10 s keeps its exact
step of 78125 µs.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp

/-- `tokens` chunks per `periodMs` milliseconds. Both are above 0. -/
structure Quota where
  tokens : Nat
  periodMs : Nat
  deriving Repr, DecidableEq

namespace Quota

/-- The time a full bucket takes to fill, in µs (Lighthouse's `tau`). -/
def tauUs (q : Quota) : Nat := q.periodMs * 1000

/-- The time one token takes to come back, in µs (Lighthouse's `t`). -/
def stepUs (q : Quota) : Nat := q.tauUs / max q.tokens 1

/-- Reserve one token at `nowUs` for a key whose TAT is `tat?`: the wait
in µs before the chunk may go, and the new TAT. The chunk conforms at
`tat + step - tau`, and the new TAT is one step past the later of `now`
and the old TAT. -/
def reserve (q : Quota) (tat? : Option Nat) (nowUs : Nat) : Nat × Nat :=
  let tat := tat?.getD nowUs
  let earliest := tat + q.stepUs - q.tauUs
  (earliest - nowUs, max nowUs tat + q.stepUs)

/-- A key with a full bucket waits for nothing. -/
theorem reserve_fresh (q : Quota) (nowUs : Nat) (h : q.stepUs ≤ q.tauUs) :
    (q.reserve none nowUs).1 = 0 := by
  simp only [reserve, Option.getD_none]
  omega

/-- A reservation never moves the TAT back. -/
theorem reserve_tat_ge (q : Quota) (tat? : Option Nat) (nowUs : Nat) :
    tat?.getD nowUs ≤ (q.reserve tat? nowUs).2 := by
  simp only [reserve]
  omega

end Quota

/-- The buckets of many keys under one quota. -/
structure Buckets (κ : Type) [BEq κ] [Hashable κ] where
  quota : Quota
  tats : Std.HashMap κ Nat := {}

namespace Buckets

variable {κ : Type} [BEq κ] [Hashable κ]

/-- Reserve one token of `key` at `nowUs`: the wait, and the buckets. -/
def reserve (b : Buckets κ) (key : κ) (nowUs : Nat) : Nat × Buckets κ :=
  let (wait, tat) := b.quota.reserve b.tats[key]? nowUs
  (wait, { b with tats := b.tats.insert key tat })

/-- Drop the keys whose bucket is full again at `nowUs`: their TAT has
passed, and a missing key reads as a full bucket. So the table holds
only the keys that sent within the last period. -/
def prune (b : Buckets κ) (nowUs : Nat) : Buckets κ :=
  { b with tats := b.tats.filter fun _ tat => nowUs < tat }

end Buckets

/-- The open inbound requests per key, against a limit: the responder's
side of `MAX_CONCURRENT_REQUESTS` ("The responder MAY penalise peers that
concurrently open more than `MAX_CONCURRENT_REQUESTS` streams for the
same request type"). -/
structure Inbound (κ : Type) [BEq κ] [Hashable κ] where
  counts : Std.HashMap κ Nat := {}

namespace Inbound

variable {κ : Type} [BEq κ] [Hashable κ]

/-- The open requests of `key`. -/
def count (t : Inbound κ) (key : κ) : Nat := t.counts[key]?.getD 0

/-- Admit one request of `key` when fewer than `limit` are open. -/
def admit (t : Inbound κ) (key : κ) (limit : Nat) : Bool × Inbound κ :=
  if t.count key < limit then (true, { counts := t.counts.insert key (t.count key + 1) })
  else (false, t)

/-- End one request of `key`. The entry goes at 0, so the table holds
only the keys with open requests. -/
def finish (t : Inbound κ) (key : κ) : Inbound κ :=
  match t.count key with
  | 0 | 1 => { counts := t.counts.erase key }
  | n + 1 => { counts := t.counts.insert key n }

end Inbound

-- A quota of 2 per 10 s: two chunks go at once, the third waits 5 s.
#guard
  let b : Buckets Nat := { quota := ⟨2, 10000⟩ }
  let (w1, b) := b.reserve 7 0
  let (w2, b) := b.reserve 7 0
  let (w3, _) := b.reserve 7 0
  [w1, w2, w3] == [0, 0, 5000000]

-- Another key keeps its own bucket.
#guard
  let b : Buckets Nat := { quota := ⟨1, 10000⟩ }
  let (_, b) := b.reserve 1 0
  (b.reserve 2 0).1 == 0 && (b.reserve 1 0).1 == 10000000

-- A bucket refills: after one step, one more chunk goes at once.
#guard
  let b : Buckets Nat := { quota := ⟨2, 10000⟩ }
  let (_, b) := b.reserve 7 0
  let (_, b) := b.reserve 7 0
  (b.reserve 7 5000000).1 == 0 && (b.prune 20000000).tats.isEmpty

#guard
  let t : Inbound Nat := {}
  let (a1, t) := t.admit 3 2
  let (a2, t) := t.admit 3 2
  let (a3, t) := t.admit 3 2
  a1 && a2 && !a3 && ((t.finish 3).admit 3 2).1 && ((t.finish 3).finish 3).counts.isEmpty

end Libp2p.Protocols.ReqResp
