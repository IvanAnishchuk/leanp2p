import Tests.Support
import Tests.HostPair

/-!
# Leak scenarios (#102)

Small scenarios that the LeakSanitizer build of the suite runs one at a
time (`LEANP2P_SUITE=leak1` to `leak4`), so a leak report names the
smallest piece that keeps its objects alive. Each one builds, uses, and
closes its objects, and keeps no reference past its end. The normal
suite does not run them.
-/

set_option autoImplicit false

namespace Tests.Leak

open Conc
open Tests.HostPair (hostPair mkHost)

/-- A test clock, made and closed. -/
def clockOnly (r : Runner) : IO Unit := Async.run do
  r.section "leak: clock" "#102"
  let tc ← (TestClock.new : BaseIO TestClock)
  (tc.close : BaseIO Unit)
  r.check "leak: the clock closes" true

/-- Two hosts on one sim net, made and closed, with no dial. -/
def hostsOnly (r : Runner) : IO Unit := Async.run do
  r.section "leak: hosts" "#102"
  let net ← (Streams.Sim.Net.new false : BaseIO _)
  let tc ← (TestClock.new : BaseIO TestClock)
  let a ← mkHost net tc.clock 1 (← OnceRef.new [])
  let b ← mkHost net tc.clock 2 (← OnceRef.new [])
  a.close
  b.close
  (tc.close : BaseIO Unit)
  r.check "leak: the hosts close" true

/-- A host pair that dials, then closes. -/
def pairOnly (r : Runner) : IO Unit := Async.run do
  r.section "leak: pair" "#102"
  let p ← hostPair
  r.check "leak: the pair closes" (← p.close).isNone

/-- A host pair with one stream opened and closed. -/
def pairStream (r : Runner) : IO Unit := Async.run do
  r.section "leak: pair and stream" "#102"
  let p ← hostPair
  let echo : Libp2p.Core.StreamHandler :=
    { id := ⟨"/leak/1"⟩, handle := fun _ s => ExceptT.mk do s.close; return .ok () }
  p.server.setHandler echo
  match ← p.client.newStream p.serverPeer [⟨"/leak/1"⟩] with
  | .ok (_, s) => s.close
  | .error _ => r.check "leak: the stream opens" false
  r.check "leak: the pair closes" (← p.close).isNone

/-- A host pair whose server handler captures the server host, as
`Identify.pushHandler p.server` does: the host's handler table holds a
closure that holds the host. -/
def pairSelfHandler (r : Runner) : IO Unit := Async.run do
  r.section "leak: handler that holds its host" "#102"
  let p ← hostPair
  let server := p.server
  let selfRef : Libp2p.Core.StreamHandler :=
    { id := ⟨"/leak/2"⟩
      handle := fun _ s => ExceptT.mk do
        -- The read of the host keeps it in the closure.
        if ← (server.isClosing : BaseIO Bool) then s.reset else s.close
        return .ok () }
  server.setHandler selfRef
  r.check "leak: the pair closes" (← p.close).isNone

/-- A TCP pair on the loopback: the dialer's end and the listener's end. -/
private def tcpPair (clock : Clock := Clock.system) : Async (Streams.Connection × Streams.Connection) := do
  let tcp := Streams.Tcp.transport clock
  let some addr := (Multiformats.Multiaddr.parse? "/ip4/127.0.0.1/tcp/0").toOption
    | throw (IO.userError "leak: address")
  let l ← tcp.listen addr
  let accepted : Chan (Option Streams.Connection) ← Chan.new 1
  let ts ← TaskSet.new
  ts.spawn do discard <| accepted.send (← l.accept)
  let some client ← tcp.dial l.addr | throw (IO.userError "leak: dial refused")
  ts.joinAll
  let some (some server) ← accepted.recv | throw (IO.userError "leak: accept failed")
  l.close
  return (client, server)

/-- A TCP pair, both ends closed. -/
def tcpClosed (r : Runner) : IO Unit := Async.run do
  r.section "leak: tcp closed" "#102"
  let (c, s) ← tcpPair
  c.close
  s.close
  r.check "leak: both ends close" true

/-- A TCP pair whose client the unauthenticated deadline closes. -/
def tcpDeadline (r : Runner) : IO Unit := Async.run do
  r.section "leak: tcp deadline" "#102"
  let tc ← (TestClock.new : BaseIO TestClock)
  let (c, s) ← tcpPair
  let ts ← TaskSet.new
  ts.spawn do discard <| c.withinUnauthDeadline tc.clock c.read
  discard tc.nextTimer
  (tc.advance Streams.unauthDeadlineMs : BaseIO Unit)
  ts.joinAll
  s.close
  (tc.close : BaseIO Unit)
  r.check "leak: the deadline closes the client" true

/-- A TCP pair whose peer end the test drops with unread bytes, so the
client meets a reset. The test never closes the client. -/
def tcpReset (r : Runner) : IO Unit := Async.run do
  r.section "leak: tcp reset" "#102"
  let c ← do
    let (c, s) ← tcpPair
    c.write ⟨#[1, 2, 3]⟩
    let _ := s
    pure c
  for _ in [0:1000] do
    try c.write ⟨Array.replicate 65536 0⟩ catch _ => break
  r.check "leak: the write to a reset peer fails" true

/-- `Tests.Streams` line 892: a parked read that the close wakes, a
second close, and the peer reading the FIN. -/
def tcpParkedRead (r : Runner) : IO Unit := Async.run do
  r.section "leak: tcp parked read" "#102"
  let (client, server) ← tcpPair
  let got : OnceRef (Option (Option ByteArray)) ← OnceRef.new none
  let ts ← TaskSet.new
  ts.spawn do got.set (some (← client.read))
  client.close
  ts.joinAll
  client.close
  discard client.read
  discard server.read
  server.close
  r.check "leak: the parked read wakes" ((← got.get).isSome)

/-- `Tests.Streams` line 907: a write after the teardown. -/
def tcpWriteAfterClose (r : Runner) : IO Unit := Async.run do
  r.section "leak: tcp write after close" "#102"
  let (client, server) ← tcpPair
  client.close
  let thrown ← try client.write ⟨#[1]⟩; pure false catch _ => pure true
  discard client.read
  server.close
  r.check "leak: the late write throws" thrown

end Tests.Leak
