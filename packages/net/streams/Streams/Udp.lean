import Std.Async.UDP
import Conc
import Bytes
import StreamsShim

/-!
# UDP datagrams

A datagram socket for discv5 (spike P5). Root ARCHITECTURE §4.1 lets
only the transports import a `Std.Async` socket. `net/streams` already
holds the TCP binding, so this module puts the UDP one beside it, as
root §4.1 records.

The receive parks on `Std.Async.UDP.Socket.recv`, a promise, so a wait
holds no pool thread. `Std`'s receive *selector* would hold one (the
quic ARCHITECTURE, "Decisions"). `close` sets a flag, then sends an
empty datagram to the socket's own address. For a bind to `0.0.0.0`,
that address is the loopback. The datagram wakes a parked receive, and
the receive answers `none`, as QUIC's loop does at its stop.

An address is its bytes: 4 for IPv4, 16 for IPv6, as an ENR holds them.

`bind` goes through the shim's exclusive bind (`StreamsShim.udpBind`),
as QUIC's endpoint does. `Std`'s own bind sets SO_REUSEADDR. On Linux,
a port-0 bind may then take a port that another socket holds, and two
nodes would split each other's datagrams.
-/

set_option autoImplicit false

namespace Streams.Udp

open Conc

/-- The largest datagram a receive takes: discv5's 1280-byte packet
limit, with room to spare. -/
def maxDatagram : Nat := 2048

/-- A bound datagram socket. -/
structure Socket where
  private native : Std.Async.UDP.Socket
  private closed : OnceRef Bool
  /-- The address `close` sends its wake datagram to: the bound one, or
  the loopback for an unspecified bind. -/
  private wakeIp : List Nat
  /-- The port the socket is bound to, with the system's pick for 0. -/
  port : Nat

/-- The socket address of 4 IPv4 bytes or 16 IPv6 bytes, and a port. -/
private def sockAddr (ip : List Nat) (port : Nat) : Option Std.Net.SocketAddress :=
  match ip with
  | [a, b, c, d] =>
    some (.v4 ⟨Std.Net.IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8, port.toUInt16⟩)
  | bs =>
    if bs.length != 16 then none else
    -- Eight big-endian 16-bit segments.
    let seg (i : Nat) : UInt16 := (bs[2 * i]! * 256 + bs[2 * i + 1]!).toUInt16
    some (.v6 ⟨Std.Net.IPv6Addr.ofParts (seg 0) (seg 1) (seg 2) (seg 3) (seg 4) (seg 5) (seg 6)
      (seg 7), port.toUInt16⟩)

/-- The 16 bytes of an IPv6 address. -/
private def v6Bytes (a : Std.Net.IPv6Addr) : List Nat :=
  a.segments.toList.flatMap fun s => [s.toNat / 256, s.toNat % 256]

/-- Bind a socket to an IPv4 or IPv6 address (4 or 16 bytes) and a port
(0 for any). -/
def bind (ip : List Nat) (port : Nat) : IO Socket := do
  let some _ := sockAddr ip port
    | throw (IO.userError "udp: an IPv4 address of 4 bytes or an IPv6 address of 16")
  let s ← Std.Async.UDP.Socket.mk
  -- The shim's bind, with no address reuse (`StreamsShim.udpBind`).
  -- `Std`'s bind sets SO_REUSEADDR, and a port-0 bind could then share
  -- a port that another socket holds. The shim takes the family byte,
  -- the address, and the port, big-endian.
  let family : Nat := if ip.length == 4 then 4 else 6
  StreamsShim.udpBind s.native
    (Bytes.ofNatList (family :: ip ++ [port / 256 % 256, port % 256]))
  let bound ← s.getSockName
  -- A datagram to the loopback never reaches a socket bound to another
  -- address, so the wake goes to the bound address itself. An
  -- unspecified bind takes the loopback of its family.
  let wakeIp :=
    if ip == [0, 0, 0, 0] then [127, 0, 0, 1]
    else if ip == List.replicate 16 0 then List.replicate 15 0 ++ [1]
    else ip
  return { native := s, closed := ← OnceRef.new false, wakeIp, port := bound.port.toNat }

/-- Send one datagram. The send drops a datagram to an address of the
wrong shape, and a datagram that the system refuses: UDP promises no
delivery. -/
def send (s : Socket) (bytes : ByteArray) (ip : List Nat) (port : Nat) : Async Unit := do
  let some addr := sockAddr ip port | return ()
  try s.native.send bytes (some addr) catch _ => pure ()

/-- The next datagram and its source: the address bytes (4 or 16) and
the port, or `none` once the socket is closed. Park: a datagram wakes
it, and so does the datagram of `close`. -/
partial def recv (s : Socket) : Async (Option (ByteArray × List Nat × Nat)) := do
  if ← (s.closed.get : BaseIO Bool) then return none
  let (bytes, src) ← try s.native.recv maxDatagram.toUInt64
    catch _ => return none
  if ← (s.closed.get : BaseIO Bool) then return none
  match src with
  | some (.v4 a) =>
    let o := a.addr.octets
    return some (bytes, [o[0]!.toNat, o[1]!.toNat, o[2]!.toNat, o[3]!.toNat], a.port.toNat)
  | some (.v6 a) => return some (bytes, v6Bytes a.addr, a.port.toNat)
  | none => recv s

/-- Close: later receives answer `none`, and a parked one wakes. -/
def close (s : Socket) : Async Unit := do
  (s.closed.set true : BaseIO Unit)
  send s .empty s.wakeIp s.port

end Streams.Udp
