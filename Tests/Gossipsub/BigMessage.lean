import Tests.Support
import Tests.Gossipsub.Identity
import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Protocols.Gossipsub.Payload

/-!
# Gossipsub: one block-sized message through the core

A measurement, not a check suite (spike P7, F3). `LEANP2P_SUITE=bigmsg`
runs it: one RPC carrying a message of `MAX_PAYLOAD_SIZE` bytes goes
through `Core.step` (decode, validate, accept, cache, forward) on the
`List Nat` byte model, and the run prints the time of each stage.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.BigMessage

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Core

private def ta : TopicId := ⟨"t"⟩

private def prims : Sign.Prims :=
  { unmarshalKey := fun _ => none, inlineKey := fun _ => none, idOfKey := fun _ => [],
    verify := fun _ _ _ => false }

/-- The message id is the first 20 bytes of the data, so the id stays
small and the measurement is the payload's path. -/
private def params : Params :=
  { defaults with prims := prims, msgId := fun m => ⟨(m.data.getD []).take 20⟩ }

def run (r : Runner) : IO Unit := do
  r.section "gossipsub big message" "(spike P7, F3: a measurement)"
  let size := Constants.maxPayloadSize
  let t0 ← IO.monoMsNow
  let data := (List.range size).map (· % 251)
  let m : Message :=
    { «from» := none, data := some data, seqno := none, topic := ta
      signature := none, key := none }
  let rpc : Rpc.RPC := { subscriptions := [], publish := [m], control := none }
  let bytes := Pb.encodeMessage rpc
  let t1 ← IO.monoMsNow
  IO.println s!"bigmsg: built and encoded {bytes.length} bytes in {t1 - t0} ms"
  let pa := Tests.Gossipsub.Identity.peer 1
  let pb := Tests.Gossipsub.Identity.peer 2
  let s : State :=
    { peers := [(pa, { score := Score.PeerState.zero, proto := .meshsub, subs := [ta] }),
        (pb, { score := Score.PeerState.zero, proto := .meshsub, subs := [ta] })]
      mesh := [(ta, [pa, pb])], fanout := []
      mcache := Cache.MessageIndex.empty params.window
      seen := Cache.SeenIndex.empty params.seen
      backoff := [], iwant := [], topics := [ta], now := 0, lastHeartbeat := 0 }
  match step params s (.rpc pa bytes) with
  | .error e => r.check s!"bigmsg: the step decodes ({repr e})" false
  | .ok (_, acts) =>
    let t2 ← IO.monoMsNow
    IO.println s!"bigmsg: step (decode, validate, accept, forward) in {t2 - t1} ms, {acts.length} actions"
    let out := acts.foldl (fun n a => match a with
      | .sendRpc _ rpc => n + (Pb.encodeMessage rpc).length | _ => n) 0
    let t3 ← IO.monoMsNow
    IO.println s!"bigmsg: re-encoded the forwards, {out} bytes, in {t3 - t2} ms"
    r.check "bigmsg: the core forwards the message to the other mesh peer" (0 < out)

/-- The same 10 MiB message on the `ByteArray` payload path
(`LEANP2P_SUITE=bigmsgB`):
1. The raw RPC splits into a small RPC and the payload.
2. The core steps on the small RPC.
3. The forward joins the payload to the small RPC again.

Compare the peak with `run`'s. -/
def runB (r : Runner) : IO Unit := do
  r.section "gossipsub big message, ByteArray path" "(spike F3: a measurement)"
  let size := Constants.maxPayloadSize
  let payload : ByteArray := ⟨(Array.range size).map (·.toUInt8)⟩
  let idOf (_ : String) (d : ByteArray) : MessageId := ⟨(d.extract 0 20).toList.map (·.toNat)⟩
  -- The raw RPC, with its fields written directly around the payload, as
  -- a peer would send it.
  let header : Message :=
    { «from» := none, data := none, seqno := none, topic := ta, signature := none, key := none }
  let inner := Bytes.ofNatList (Pb.encodeMessage header)
  let raw := Payload.lenField Payload.rpcPublish (inner ++ Payload.lenField Payload.msgData payload)
  let t0 ← IO.monoMsNow
  let some (small, ps) := Payload.splitInbound raw idOf
    | r.check "bigmsgB: the RPC splits" false
  let t1 ← IO.monoMsNow
  IO.println s!"bigmsgB: split {raw.size} bytes into {small.size} and {ps.length} payload in {t1 - t0} ms"
  let pa := Tests.Gossipsub.Identity.peer 1
  let pb := Tests.Gossipsub.Identity.peer 2
  let hp : Params := { params with msgId := fun m => ⟨m.data.getD []⟩ }
  let s : State :=
    { peers := [(pa, { score := Score.PeerState.zero, proto := .meshsub, subs := [ta] }),
        (pb, { score := Score.PeerState.zero, proto := .meshsub, subs := [ta] })]
      mesh := [(ta, [pa, pb])], fanout := []
      mcache := Cache.MessageIndex.empty hp.window
      seen := Cache.SeenIndex.empty hp.seen
      backoff := [], iwant := [], topics := [ta], now := 0, lastHeartbeat := 0 }
  match step hp s (.rpc pa (Bytes.toNatList small)) with
  | .error e => r.check s!"bigmsgB: the step decodes ({repr e})" false
  | .ok (_, acts) =>
    let t2 ← IO.monoMsNow
    IO.println s!"bigmsgB: step in {t2 - t1} ms, {acts.length} actions"
    let lookup (h : MessageId) : Option ByteArray := (ps.find? (·.1 == h)).map (·.2)
    let out := acts.foldl (fun n a => match a with
      | .sendRpc _ rpc => n + (Payload.joinOutbound rpc lookup).size | _ => n) 0
    let t3 ← IO.monoMsNow
    IO.println s!"bigmsgB: joined the forwards, {out} bytes, in {t3 - t2} ms"
    r.check "bigmsgB: the forward carries the whole payload" (out ≥ size)

/-- A 20-byte id from a number, as the consensus id is 20 bytes. -/
private def idOf (n : Nat) : MessageId :=
  ⟨(List.range 20).map fun i => (n / 256 ^ (i % 4)) % 256⟩

/-- The seen cache at its capacity (spike P8, F4). `LEANP2P_SUITE=scale`
fills the cache with 65536 ids, then runs `steps` messages through the
per-message pair `contains` then `add`. Each op loops in `IO`, so the
compiler cannot lift it out of the timed span. -/
def scale (r : Runner) (steps : Nat := 500) : IO Unit := do
  r.section "gossipsub seen cache at capacity" "(spike P8, F4: a measurement)"
  for fill in [1024, 2048, 4096, 8192] do
    let p : Cache.SeenParams := { capacity := 65536, ttl := 768000, valid := by decide }
    let mut c := Cache.SeenCache.empty p
    let t0 ← IO.monoMsNow
    for i in [0:fill] do
      c := c.add (idOf i) 0
    let t1 ← IO.monoMsNow
    let mut hits := 0
    for i in [0:steps] do
      if c.contains (idOf (100000 + i)) 1 then hits := hits + 1
      c := c.add (idOf (100000 + i)) 1
    let t2 ← IO.monoMsNow
    IO.println s!"scale: {fill} ids filled in {t1 - t0} ms; then {steps} messages in {t2 - t1} ms, {(t2 - t1) * 1000 / steps} us each"
    r.check s!"scale {fill}: no false hit" (hits == 0)
  -- The production `SeenIndex` at the full capacity the model cannot reach.
  let p : Cache.SeenParams := { capacity := 65536, ttl := 768000, valid := by decide }
  let mut c := Cache.SeenIndex.empty p
  let t0 ← IO.monoMsNow
  for i in [0:65536] do
    c := c.add (idOf i) 0
  let t1 ← IO.monoMsNow
  let mut hits := 0
  let n := 20000
  for i in [0:n] do
    if c.contains (idOf (100000 + i)) 1 then hits := hits + 1
    c := c.add (idOf (100000 + i)) 1
  let t2 ← IO.monoMsNow
  IO.println s!"scale index: 65536 ids filled in {t1 - t0} ms; then {n} messages in {t2 - t1} ms, {(t2 - t1) * 1000 / n} us each, {c.index.size} held"
  r.check "scale index: no false hit, capacity held" (hits == 0 && c.index.size == 65536)

end Tests.Gossipsub.BigMessage
