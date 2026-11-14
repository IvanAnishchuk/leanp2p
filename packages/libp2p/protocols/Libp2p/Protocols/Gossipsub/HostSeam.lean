import Libp2p.Host
import Libp2p.Core

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub

/-- The host operations used by a gossipsub node. -/
structure HostSeam where
  /-- Open a stream to a peer. -/
  newStream : Libp2p.Identity.PeerId → List Libp2p.Core.ProtocolId →
    Conc.Async (Except Libp2p.Core.Error (Libp2p.Core.ProtocolId × Streams.Stream))
  /-- Register a stream handler. -/
  setHandler : Libp2p.Core.StreamHandler → BaseIO Unit
  /-- Register a connection notifiee (`Host.addNotifiee`). The node
  registers one at start, so the host's connects and disconnects reach
  the router as `peerJoined` and `peerLeft`. The default registers
  nothing, for a seam whose test drives the joins itself. -/
  addNotifiee : (Libp2p.Host.ConnEvent → BaseIO Unit) → BaseIO Unit := fun _ => pure ()
  /-- The peers connected now, when the seam knows them. The node joins
them at start, and before each heartbeat it reconciles the router with
  them: a join or leave lost to a full queue, or to the start's race,
  heals within one heartbeat. `none` for a seam whose test drives the
  joins itself. -/
  peers : Option (BaseIO (List Libp2p.Identity.PeerId)) := none
  /-- Dial a peer through the host's peerstore, for the explicit peers
  the router must keep connected. `true` once a session is live. -/
  dial : Libp2p.Identity.PeerId → Conc.Async Bool := fun _ => pure false
  /-- The signed peer record the host holds for a peer, as it arrived
  (`Host.recordOf`; identify fills the store). A prune's peer exchange
  carries it. -/
  recordOf : Libp2p.Identity.PeerId → BaseIO (Option ByteArray) := fun _ => pure none
  /-- Consume a signed peer record a peer exchange offered for `peer`:
  `true` when it verifies and names `peer` (`Host.consumeRecord`). Its
  addresses enter the peerstore with a short lifetime. -/
  consumeRecord : Libp2p.Identity.PeerId → ByteArray → BaseIO Bool := fun _ _ => pure false

/-- The lifetime of the addresses a peer exchange brings: go-libp2p's
`peerstore.TempAddrTTL`, two minutes. -/
def pxAddrTtlMs : Nat := 120000

/-- Adapt a host to the node operations. -/
def HostSeam.ofHost (host : Libp2p.Host.Host) : HostSeam where
  setHandler := host.setHandler
  newStream := fun peer ids => do
    match ← host.newStream peer ids with
    | .ok pair => return .ok pair
    | .error (.stream e) => return .error e
    | .error e => return .error (.protocol e.render)
  addNotifiee := host.addNotifiee
  peers := some host.peers
  dial := fun peer => do return (← host.dialPeer peer) matches .ok _
  recordOf := host.recordOf
  consumeRecord := fun peer bytes => do
    -- An older record than the stored one still verified: the peer is
    -- real, and the stored addresses serve the dial.
    return (← host.consumeRecord bytes (some peer) (some pxAddrTtlMs)) matches .ok _

end Libp2p.Protocols.Gossipsub
