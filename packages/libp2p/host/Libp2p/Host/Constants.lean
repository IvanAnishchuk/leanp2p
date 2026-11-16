/-!
# The constants of `libp2p/host`

Each fact has one home (ARCHITECTURE §3.8; PRINCIPLES 1.5). This module
holds the constants the host owns. The deadline of an unauthenticated
phase is not here: `net/streams` owns it (`Streams.unauthDeadlineMs`,
§5.4), and the upgrader applies it.
-/

set_option autoImplicit false

namespace Libp2p.Host

/-- The race window of the simultaneous-dial rule, in milliseconds
(§4.9; the package ARCHITECTURE, contract 2). Two connections to one
peer that run in opposite directions race when the standing session
was born less than this long before the new one. Inside the window,
the connection that the larger peer id dialed loses. Outside it, the
standing session keeps its place. Each side measures with its own
`Clock`. -/
def simulWindowMs : Nat := 30000

/-- The deadline of the protocol negotiation on one stream, in
milliseconds, both ways: go-libp2p's `DefaultNegotiationTimeout` of
10 s (`p2p/host/basic/basic_host.go`), which its stream handler sets on
each inbound stream, and `NewStream` sets when the caller gives none. A
peer that opens a stream and stays silent would hold its stream
reservation until the session ends. The expiry resets the stream. -/
def streamNegotiationMs : Nat := 10000

/-- The lifetime of a dial address in the peerstore, in milliseconds:
go-libp2p's `TempAddrTTL` of 2 minutes (`core/peerstore/peerstore.go`),
which its `Connect` gives the addresses it dials
(`p2p/host/basic/basic_host.go`). A discovered address with no lifetime
stays until the owner removes it, and the store refuses new peers once
it holds `Peerstore.Limits.peers`. -/
def dialAddrTtlMs : Nat := 120000

end Libp2p.Host
