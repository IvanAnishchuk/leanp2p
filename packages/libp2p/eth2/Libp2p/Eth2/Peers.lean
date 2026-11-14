import Libp2p.Identity
import Libp2p.Eth2.Constants

/-!
# The peer table of the service

The pure state behind two duties of the service: the Ping liveness
check, and the bans.

* **Ping.** "Sent intermittently, the `Ping` protocol checks liveness of
  connected peers" (phase0, "Ping v1"). A peer is due when no Ping
  passed between us, in either direction, for its interval. A peer we
  dialed has a shorter interval than a peer that dialed us
  (`Constants.pingIntervalOutboundMs`), so two peers do not ping each
  other at the same time. Lighthouse skips a peer that pinged us within
  the interval, and so does this table: an inbound Ping counts.
* **MetaData.** A Ping answer carries the peer's `seq_number`. A number
  above the one we know means newer MetaData, which the client "MAY
  request" (phase0). `seqNews` answers whether to ask.
* **Bans.** A ban holds until its end, in wall-clock milliseconds. The
  table holds at most `Constants.maxBans`, so a peer cannot grow it
  without bound (root ARCHITECTURE §5.1). A new ban past the cap drops
  the ban that ends first.

Every function here is a pure transition, so the service changes the
table with one `OnceRef.update` (root §4.1, rule 3).
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Identity

/-- What the table keeps of one connected peer. -/
structure PeerEntry where
  peer : PeerId
  /-- `true` when we dialed the peer. -/
  outbound : Bool
  /-- The last Ping between us, either way, in milliseconds. -/
  lastPing : Nat
  /-- The `seq_number` of the last MetaData we have from the peer. -/
  metaSeq : Option Nat := none

/-- The peers and the bans. -/
structure Peers where
  entries : List PeerEntry := []
  /-- Each banned peer with the end of its ban. -/
  bans : List (PeerId × Nat) := []

namespace Peers

/-- The Ping interval of an entry. -/
def interval (e : PeerEntry) : Nat :=
  if e.outbound then Constants.pingIntervalOutboundMs else Constants.pingIntervalInboundMs

/-- A peer connected at `now`. Its first Ping is one interval away, since
the Status exchange opens the connection. A peer already in the table
stays as it is. -/
def connect (t : Peers) (peer : PeerId) (outbound : Bool) (now : Nat) : Peers :=
  if t.entries.any (·.peer == peer) then t
  else { t with entries := t.entries ++ [{ peer, outbound, lastPing := now }] }

/-- The peer's last session ended. -/
def disconnect (t : Peers) (peer : PeerId) : Peers :=
  { t with entries := t.entries.filter (·.peer != peer) }

/-- A Ping passed between us and the peer at `now`. -/
def pinged (t : Peers) (peer : PeerId) (now : Nat) : Peers :=
  { t with entries := t.entries.map fun e => if e.peer == peer then { e with lastPing := now } else e }

/-- The peers due for a Ping at `now`. The table marks them pinged, so a
second look before the answer does not ping them again. -/
def takeDue (t : Peers) (now : Nat) : List PeerId × Peers :=
  let isDue (e : PeerEntry) : Bool := e.lastPing + interval e ≤ now
  let due := (t.entries.filter isDue).map (·.peer)
  (due, { t with entries := t.entries.map fun e => if isDue e then { e with lastPing := now } else e })

/-- Whether a Ping answer of `seq` names newer MetaData than we have. -/
def seqNews (t : Peers) (peer : PeerId) (seq : Nat) : Bool :=
  match t.entries.find? (·.peer == peer) with
  | some e => e.metaSeq.all (· < seq)
  | none => false

/-- The peer's MetaData of `seq` arrived. -/
def setMeta (t : Peers) (peer : PeerId) (seq : Nat) : Peers :=
  { t with entries := t.entries.map fun e => if e.peer == peer then { e with metaSeq := some seq } else e }

/-- Ban the peer until `endMs`. The bans that ended by `now` go first.
A peer banned already takes the later end. Past `Constants.maxBans`,
the ban that ends first goes. -/
def ban (t : Peers) (peer : PeerId) (now endMs : Nat) : Peers :=
  let live := t.bans.filter fun (p, e) => now < e && p != peer
  let old := (t.bans.find? (·.1 == peer)).map (·.2) |>.getD 0
  let bans := (peer, max endMs old) :: live
  let bans := if Constants.maxBans < bans.length then
      let sorted := bans.mergeSort fun a b => decide (b.2 ≤ a.2)
      sorted.take Constants.maxBans
    else bans
  { t with bans }

/-- Whether the peer is banned at `now`. -/
def banned (t : Peers) (peer : PeerId) (now : Nat) : Bool :=
  t.bans.any fun (p, e) => p == peer && now < e

end Peers

end Libp2p.Eth2
