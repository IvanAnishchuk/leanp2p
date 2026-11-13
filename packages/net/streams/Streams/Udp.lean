import Std.Async.UDP
import Conc

/-!
# UDP datagrams

A datagram socket for discv5 (spike P5). Root ARCHITECTURE §4.1 lets
only the transports import a `Std.Async` socket; `net/streams` already
holds the TCP binding, so this module puts the UDP one beside it. The
placement is the spike's, and the root docs have not made it.

The receive parks on `Std.Async.UDP.Socket.recv`, a promise, so a wait
holds no pool thread (`Std`'s receive *selector* would; see the quic
ARCHITECTURE, "Decisions"). `close` sets a flag, then sends an empty
datagram to the socket's own address, which wakes a parked receive; the
receive then answers `none`, as QUIC's loop does at its stop.

IPv4 only in the spike.
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
  /-- The port the socket is bound to, with the system's pick for 0. -/
  port : Nat

private def v4 (ip : List Nat) (port : Nat) : Option Std.Net.SocketAddress :=
  match ip with
  | [a, b, c, d] =>
    some (.v4 ⟨Std.Net.IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8, port.toUInt16⟩)
  | _ => none

/-- Bind a socket to an IPv4 address and port (0 for any). -/
def bind (ip : List Nat) (port : Nat) : IO Socket := do
  let some addr := v4 ip port | throw (IO.userError "udp: an IPv4 address of 4 bytes")
  let s ← Std.Async.UDP.Socket.mk
  s.bind addr
  let bound ← s.getSockName
  return { native := s, closed := ← OnceRef.new false, port := bound.port.toNat }

/-- Send one datagram. A send to an address of the wrong shape, or one
the system refuses, is dropped: UDP promises no delivery. -/
def send (s : Socket) (bytes : ByteArray) (ip : List Nat) (port : Nat) : Async Unit := do
  let some addr := v4 ip port | return ()
  try s.native.send bytes (some addr) catch _ => pure ()

/-- The next datagram and its source: the IPv4 bytes and the port.
`none` once the socket is closed. Park: a datagram wakes it, and so does
`close`'s own datagram. -/
partial def recv (s : Socket) : Async (Option (ByteArray × List Nat × Nat)) := do
  if ← (s.closed.get : BaseIO Bool) then return none
  let (bytes, src) ← try s.native.recv maxDatagram.toUInt64
    catch _ => return none
  if ← (s.closed.get : BaseIO Bool) then return none
  match src with
  | some (.v4 a) =>
    let o := a.addr.octets
    return some (bytes, [o[0]!.toNat, o[1]!.toNat, o[2]!.toNat, o[3]!.toNat], a.port.toNat)
  | _ => recv s

/-- Close: later receives answer `none`, and a parked one wakes. -/
def close (s : Socket) : Async Unit := do
  (s.closed.set true : BaseIO Unit)
  send s .empty [127, 0, 0, 1] s.port

end Streams.Udp
