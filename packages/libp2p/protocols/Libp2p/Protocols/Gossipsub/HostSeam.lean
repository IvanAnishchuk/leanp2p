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
  /-- The peers connected now. The node reads them after it registers
  its notifiee, so a peer connected before the start joins too. -/
  peers : BaseIO (List Libp2p.Identity.PeerId) := pure []

/-- Adapt a host to the node operations. -/
def HostSeam.ofHost (host : Libp2p.Host.Host) : HostSeam where
  setHandler := host.setHandler
  newStream := fun peer ids => do
    match ← host.newStream peer ids with
    | .ok pair => return .ok pair
    | .error (.stream e) => return .error e
    | .error e => return .error (.protocol e.render)
  addNotifiee := host.addNotifiee
  peers := host.peers

end Libp2p.Protocols.Gossipsub
