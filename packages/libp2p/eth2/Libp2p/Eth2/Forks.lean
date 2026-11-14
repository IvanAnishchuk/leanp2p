import Libp2p.Eth2.Constants
import Libp2p.Eth2.Fork

/-!
# The gossip across a fork

"With any fork, the fork version, and thus the `ForkDigestValue`,
change" (altair, "Transitioning the gossip"). Each topic then has a
pre-fork and a post-fork variant, and the spec asks for three steps:

1. "In advance of the fork, a node SHOULD subscribe to the post-fork
   variants of the topics." The spec names no lead. Lighthouse subscribes
   one epoch ahead (`SUBSCRIBE_DELAY_EPOCHS`), and so does this module.
2. At the fork, the post-fork digest becomes ours. "Peers who propagate
   messages on the pre-fork topics MUST NOT be scored negatively", so the
   service drops the score parameters of the pre-fork topics, as
   Lighthouse does (`remove_topic_weight_except`).
3. "Two epochs after the fork, pre-fork topics SHOULD be unsubscribed
   from" (`UNSUBSCRIBE_DELAY_EPOCHS`).

A Blob-Parameters-Only fork changes the digest with the same version
(EIP-7892), so it takes the same three steps.

"Messages SHOULD NOT be re-broadcast from one fork to the other." The
router forwards a message on its own topic only, so the rule holds with
no work here.

`step` is a pure transition over `ForkState`. The service's fork loop
calls it with the wall-clock epoch, and it performs the actions.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

/-- The lead of the post-fork subscription, in epochs. -/
def subscribeLeadEpochs : Nat := 1

/-- The epochs after the fork until the pre-fork topics go. -/
def unsubscribeDelayEpochs : Nat := 2

/-- What the service follows of the fork schedule. -/
structure ForkState where
  /-- Our digest. -/
  current : ByteArray
  /-- The post-fork digest whose topics we already joined, ahead of the
  fork. -/
  next : Option ByteArray := none
  /-- The pre-fork digest, and the epoch at which its topics go. -/
  retiring : Option (ByteArray × Nat) := none

/-- One duty of the fork loop. -/
inductive ForkAction where
  /-- Subscribe the client's kinds under this digest. -/
  | subscribe (digest : ByteArray)
  /-- The fork happened: `new` replaces `old` as our digest. -/
  | switch (old new : ByteArray)
  /-- Leave the topics of this digest. -/
  | unsubscribe (digest : ByteArray)

namespace ForkState

/-- The duties at `epoch`, in order, and the next state. A fork the loop
did not see ahead also subscribes to the new digest at the switch. -/
def step (c : Chain) (epoch : Nat) (st : ForkState) :
    Except Crypto.CryptoError (List ForkAction × ForkState) := do
  let digest ← c.forkDigest epoch
  let mut acts : List ForkAction := []
  let mut st := st
  -- The fork: the digest of the epoch is no longer ours.
  if digest != st.current then
    if st.next != some digest then acts := acts ++ [.subscribe digest]
    acts := acts ++ [.switch st.current digest]
    st := { current := digest, next := none,
            retiring := some (st.current, epoch + unsubscribeDelayEpochs) }
  -- The lead: the next fork is at most `subscribeLeadEpochs` away.
  let nextEpoch := c.nextForkEpoch epoch
  if nextEpoch != Constants.farFutureEpoch && nextEpoch ≤ epoch + subscribeLeadEpochs then
    let nextDigest ← c.forkDigest nextEpoch
    if st.next != some nextDigest && nextDigest != digest then
      acts := acts ++ [.subscribe nextDigest]
      st := { st with next := some nextDigest }
  -- The retirement of the pre-fork topics.
  if let some (old, at') := st.retiring then
    if at' ≤ epoch then
      acts := acts ++ [.unsubscribe old]
      st := { st with retiring := none }
  return (acts, st)

end ForkState

end Libp2p.Eth2
