import Std.Async.TCP
import Std.Async.UDP

/-!
# The socket shim

Three C functions that the transports need and the v4.34 runtime does
not offer: two for `Streams.Tcp`, and the exclusive UDP bind for
`Streams.Udp` and `net/quic`.

Lean v4.34 binds libuv TCP with no close call: the runtime closes a
socket's handle only when the last reference to the socket goes, and
every pending connect, write, and shutdown request holds one. A write to
a peer that stops reading never completes, so without this shim its
socket and descriptor would live forever, and a hostile peer could
exhaust our descriptors.

`abort` makes the kernel fail every pending request of the socket
(`c/tcpabort.c` says how). Each request then drops its reference, and
the runtime closes the handle the normal way. `Streams.Tcp` calls it on
a teardown with writes in flight, and on a dial that outlived its
deadline. The package docs record why a shim is the only lever on this
toolchain (`docs/ARCHITECTURE.md`, "Decisions").

`econnreset` gives the platform's `ECONNRESET`. The runtime reports a
peer's reset as `IO.Error.resourceVanished` with that errno, and the
same constructor carries `EPIPE` and `ENETDOWN`, so `Streams.Tcp` tells
the reset apart by the code (`c/tcperrno.c`). The package docs say why
a peer's reset ends the read (`docs/ARCHITECTURE.md`, "Decisions").

`udpBind` binds a UDP socket with no address reuse. `Std.Async.UDP`'s
own bind always sets SO_REUSEADDR, and on Linux a port-0 bind may then
take a port another socket holds (`c/udpbind.c` says how the shim avoids
it).
-/

set_option autoImplicit false

namespace StreamsShim

/-- End every pending request of the socket: a connect aborts, and a
write or a shutdown fails. Established connections send RST. The socket
stays a valid object; the runtime closes its handle once the requests
release it. -/
@[extern "leanp2p_tcp_abort"]
opaque abort (sock : @& Std.Internal.UV.TCP.Socket) : BaseIO Unit

/-- The platform's `ECONNRESET`, the `osCode` of a read that met the
peer's reset. A constant of the platform, so the binding is pure (root
ARCHITECTURE §3.6). It takes `Unit`, as the runtime's own platform
constants do (`System.Platform.getTarget`). -/
@[extern "leanp2p_tcp_econnreset"]
opaque econnreset : Unit → UInt32

/-- Bind a fresh UDP socket to `addr` with no address reuse, so no other
socket shares its port. `addr` is the family byte (4 or 6), the address
in network order, then the port, big-endian: 7 or 19 bytes. Call it
once, before any receive or send on the socket. A port another socket
holds fails with EADDRINUSE. -/
@[extern "leanp2p_udp_bind"]
opaque udpBind (socket : @& Std.Internal.UV.UDP.Socket) (addr : @& ByteArray) : IO Unit

end StreamsShim
