import Tests.Support
import Tests.Gossipsub.Identity
import Libp2p.Protocols.Gossipsub.Core

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
      mcache := Cache.MessageCache.empty params.window
      seen := Cache.SeenCache.empty params.seen
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
    r.check "bigmsg: the message is forwarded to the other mesh peer" (0 < out)

end Tests.Gossipsub.BigMessage
