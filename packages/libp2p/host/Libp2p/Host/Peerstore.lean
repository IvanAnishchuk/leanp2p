import Std.Data.HashMap
import Multiformats
import Libp2p.Identity

/-!
# The peerstore

The third host registry (ARCHITECTURE §3.8): the addresses of each
peer. `dialPeer` walks them. The table changes only through the pure
updates here, applied under `OnceRef.update` (the package
ARCHITECTURE, contract 1). The spike's peerstore lost addresses
through a get-then-set; one atomic update per add closes that race
(PRINCIPLES 3.3).

An add skips the addresses the peer already has, so a redial that
re-adds its address grows nothing. The addresses keep the order they
first arrived in.

## Limits and TTLs (root §9, delta 3)

Discovery feeds the store from untrusted records, so the store has
three bounds:

* A peer keeps at most `Limits.addrsPerPeer` addresses. An add past
  the cap drops the oldest.
* An address may carry an expiry. `addrsOf` hides it after that, and
  `prune` removes it. A new add of the address refreshes the expiry.
* The store keeps at most `Limits.peers` peers, and refuses a new peer
  past the cap. The addresses of the connected peers matter more than
  a stranger's. The store cannot tell them apart, so it keeps what it
  has.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Multiformats Libp2p.Identity

/-- One stored address and its expiry on the host clock. An address
with `none` never expires. -/
structure PeerAddr where
  addr : Multiaddr
  expiresMs : Option Nat

/-- The bounds of the store. -/
structure Limits where
  /-- The most addresses one peer keeps. go-libp2p's peerstore has no
  per-peer cap. Its connection manager trims peers instead. -/
  addrsPerPeer : Nat := 16
  /-- The most peers the store keeps. -/
  peers : Nat := 10000

/-- The addresses of each peer, in the order they first arrived. A
synonym with no invariant of its own (§3.7). -/
abbrev Peerstore := Std.HashMap PeerId (Array PeerAddr)

namespace Peerstore

/-- True while `a` has not expired at `nowMs`. -/
def PeerAddr.live (nowMs : Nat) (a : PeerAddr) : Bool :=
  match a.expiresMs with
  | none => true
  | some t => nowMs < t

/-- Add `addrs` to the addresses of `peer`, each once. An address the
peer has takes the later expiry. The newest `limits.addrsPerPeer`
stay. The store refuses a new peer past `limits.peers`. -/
def addAddrs (peer : PeerId) (addrs : List Multiaddr) (s : Peerstore)
    (nowMs : Nat := 0) (ttlMs : Option Nat := none) (limits : Limits := {}) : Peerstore :=
  if !s.contains peer && limits.peers ≤ s.size then s
  else
    let expiresMs := ttlMs.map (nowMs + ·)
    let later (a b : Option Nat) : Option Nat :=
      match a, b with
      | none, _ | _, none => none
      | some x, some y => some (max x y)
    let known := s.getD peer #[]
    let grown := addrs.foldl (fun acc a =>
      match acc.findIdx? (·.addr == a) with
      | some i => acc.modify i fun e => { e with expiresMs := later e.expiresMs expiresMs }
      | none => acc.push { addr := a, expiresMs }) known
    let kept := grown.extract (grown.size - limits.addrsPerPeer) grown.size
    s.insert peer kept

/-- The live addresses of `peer` at `nowMs`, in the order they first
arrived. Empty when the store knows none. -/
def addrsOf (s : Peerstore) (peer : PeerId) (nowMs : Nat := 0) : List Multiaddr :=
  ((s.getD peer #[]).filter (PeerAddr.live nowMs)).toList.map (·.addr)

/-- Drop the expired addresses, and the peers left with none. -/
def prune (s : Peerstore) (nowMs : Nat) : Peerstore :=
  s.fold (fun acc peer as =>
    let live := as.filter (PeerAddr.live nowMs)
    if live.isEmpty then acc else acc.insert peer live) {}

end Peerstore

end Libp2p.Host
