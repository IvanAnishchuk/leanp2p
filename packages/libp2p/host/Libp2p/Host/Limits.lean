import Std.Data.HashMap
import Conc
import Libp2p.Core

/-!
# The limiting resource manager (root §9, delta 4)

A `ResourceManager` that counts. The limits of delta 4: per connection,
the stream count and the buffered bytes; per peer, the connections,
the streams, and the bytes; and over the host, the connections and a
memory ceiling.

The counts sit in one table, changed only by the pure functions of
`Table` under one `OnceRef.updateGet` each (contract 1; PRINCIPLES
3.3). A reservation holds its own cell, and its release runs once.

A connection counts against its peer only after `setPeer`. Its
reservations before that count against the connection and the host
alone, and `setPeer` moves them onto the peer, or refuses when they do
not fit.
-/

set_option autoImplicit false

namespace Libp2p.Host.Limits

open Conc Libp2p.Core Libp2p.Identity

/-- The bounds. The defaults are spike placeholders with no source; a
consensus client sets its own. -/
structure Bounds where
  /-- Connections over the host. -/
  connections : Nat := 256
  /-- Connections per peer. -/
  connectionsPerPeer : Nat := 8
  /-- Streams per connection. -/
  streamsPerConnection : Nat := 512
  /-- Streams per peer. -/
  streamsPerPeer : Nat := 1024
  /-- Buffered bytes per connection. -/
  memoryPerConnection : Nat := 32 * 2 ^ 20
  /-- Buffered bytes over the host. -/
  memory : Nat := 512 * 2 ^ 20

/-- The use of one peer. -/
structure PeerUse where
  connections : Nat := 0
  streams : Nat := 0
  memory : Nat := 0

/-- The use of one connection. -/
structure ConnUse where
  peer : Option PeerId := none
  streams : Nat := 0
  memory : Nat := 0

/-- The whole table: the host totals, each peer, each open connection
by its number. -/
structure Table where
  connections : Nat := 0
  memory : Nat := 0
  peers : Std.HashMap PeerId PeerUse := {}
  conns : Std.HashMap Nat ConnUse := {}
  next : Nat := 0

namespace Table

/-- The use of a peer, zero when it has none. -/
def peerUse (t : Table) (p : PeerId) : PeerUse := t.peers.getD p {}

/-- Store a peer's use; a peer with no connection leaves the table. -/
def setPeerUse (t : Table) (p : PeerId) (u : PeerUse) : Table :=
  if u.connections = 0 && u.streams = 0 && u.memory = 0 then { t with peers := t.peers.erase p }
  else { t with peers := t.peers.insert p u }

/-- Open a connection: its number, when the host total allows. -/
def openConn (b : Bounds) (t : Table) : Option Nat × Table :=
  if b.connections ≤ t.connections then (none, t)
  else (some t.next, { t with connections := t.connections + 1, next := t.next + 1,
                              conns := t.conns.insert t.next {} })

/-- Name the connection's peer, moving its use onto the peer. -/
def setPeer (b : Bounds) (id : Nat) (p : PeerId) (t : Table) : Bool × Table :=
  match t.conns.get? id with
  | none => (false, t)
  | some c =>
    if c.peer.isSome then (false, t) else
    let u := t.peerUse p
    if b.connectionsPerPeer ≤ u.connections || b.streamsPerPeer < u.streams + c.streams then (false, t)
    else
      let t := t.setPeerUse p { connections := u.connections + 1, streams := u.streams + c.streams,
                                memory := u.memory + c.memory }
      (true, { t with conns := t.conns.insert id { c with peer := some p } })

/-- Admit one stream on the connection. -/
def addStream (b : Bounds) (id : Nat) (t : Table) : Bool × Table :=
  match t.conns.get? id with
  | none => (false, t)
  | some c =>
    if b.streamsPerConnection ≤ c.streams then (false, t) else
    match c.peer with
    | none => (true, { t with conns := t.conns.insert id { c with streams := c.streams + 1 } })
    | some p =>
      let u := t.peerUse p
      if b.streamsPerPeer ≤ u.streams then (false, t)
      else (true, { (t.setPeerUse p { u with streams := u.streams + 1 }) with
                    conns := t.conns.insert id { c with streams := c.streams + 1 } })

/-- Return one stream of the connection. -/
def dropStream (id : Nat) (t : Table) : Table :=
  match t.conns.get? id with
  | none => t
  | some c =>
    let t := { t with conns := t.conns.insert id { c with streams := c.streams - 1 } }
    match c.peer with
    | none => t
    | some p => let u := t.peerUse p; t.setPeerUse p { u with streams := u.streams - 1 }

/-- Admit `n` buffered bytes on the connection. -/
def addMemory (b : Bounds) (id n : Nat) (t : Table) : Bool × Table :=
  match t.conns.get? id with
  | none => (false, t)
  | some c =>
    if b.memoryPerConnection < c.memory + n || b.memory < t.memory + n then (false, t) else
    let t := { t with memory := t.memory + n,
                      conns := t.conns.insert id { c with memory := c.memory + n } }
    match c.peer with
    | none => (true, t)
    | some p => let u := t.peerUse p; (true, t.setPeerUse p { u with memory := u.memory + n })

/-- Return `n` buffered bytes of the connection. -/
def dropMemory (id n : Nat) (t : Table) : Table :=
  match t.conns.get? id with
  | none => t
  | some c =>
    let t := { t with memory := t.memory - n,
                      conns := t.conns.insert id { c with memory := c.memory - n } }
    match c.peer with
    | none => t
    | some p => let u := t.peerUse p; t.setPeerUse p { u with memory := u.memory - n }

/-- Close the connection: return everything it still holds. -/
def closeConn (id : Nat) (t : Table) : Table :=
  match t.conns.get? id with
  | none => t
  | some c =>
    let t := { t with connections := t.connections - 1, memory := t.memory - c.memory,
                      conns := t.conns.erase id }
    match c.peer with
    | none => t
    | some p =>
      let u := t.peerUse p
      t.setPeerUse p { connections := u.connections - 1, streams := u.streams - c.streams,
                       memory := u.memory - c.memory }

end Table

/-- A share that releases once: the first call runs `act`. -/
private def once (act : BaseIO Unit) : BaseIO Reservation := do
  let done ← OnceRef.new false
  return { release := do
    if !(← done.updateGet fun d => (d, true)) then act }

/-- The limiting resource manager over `bounds`, and a read of its table
for a test or a metric. -/
def manager (bounds : Bounds := {}) : BaseIO (ResourceManager × BaseIO Table) := do
  let table ← OnceRef.new ({} : Table)
  let rm : ResourceManager := {
    openConnection := fun _ _ _ => do
      let some id ← table.updateGet (fun t => Table.openConn bounds t) | return none
      let closed ← once (table.update (Table.closeConn id))
      return some {
        setPeer := fun p => table.updateGet (Table.setPeer bounds id p)
        reserveStream := do
          if !(← table.updateGet (Table.addStream bounds id)) then return none
          some <$> once (table.update (Table.dropStream id))
        reserveMemory := fun n => do
          if !(← table.updateGet (Table.addMemory bounds id n)) then return none
          some <$> once (table.update (Table.dropMemory id n))
        release := closed.release } }
  return (rm, table.get)

end Libp2p.Host.Limits
