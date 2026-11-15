import Crypto
import Snappy
import Libp2p.Protocols.Gossipsub.Types
import Libp2p.Eth2.Constants
import Libp2p.Eth2.Uint64

/-!
# The consensus message id

From Altair on, the `message-id` of a gossip message is the first 20
bytes of a SHA-256 over the topic and the data (altair, "Topics and
messages"):

* When `message.data` decompresses as a snappy block:
  `SHA256(MESSAGE_DOMAIN_VALID_SNAPPY ‖ uint64_le(len(topic)) ‖ topic ‖ snappy_decompress(data))[:20]`.
* Otherwise: `SHA256(MESSAGE_DOMAIN_INVALID_SNAPPY ‖ uint64_le(len(topic)) ‖ topic ‖ data)[:20]`.

The decompression takes the cap `MAX_PAYLOAD_SIZE`. A block that claims
more is invalid, so it takes the second form. This package starts at
Fulu, so it has no phase0 form.

The function is pure, as the node's `payloadId` seam asks. The
SHA-256 of the crypto facade answers `Except`, for a fault of the
OpenSSL shim. A fault gives `none`, and the node then drops the
message (`Config.payloadId`). A shim fault is not a peer input: it
means the process is broken.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Protocols.Gossipsub (MessageId)

/-- The bytes that the SHA-256 of the message id reads. -/
def messageIdInput (topic : String) (data : ByteArray) : ByteArray :=
  let t := topic.toUTF8
  match Snappy.decompress data Libp2p.Protocols.Constants.maxPayloadSize with
  | .ok raw => Constants.messageDomainValidSnappy ++ le64 t.size ++ t ++ raw
  | .error _ => Constants.messageDomainInvalidSnappy ++ le64 t.size ++ t ++ data

/-- The message id of `data` on `topic`, as bytes. `none` on a fault of
the SHA-256 shim. -/
def messageIdBytes (topic : String) (data : ByteArray) : Option ByteArray :=
  match Crypto.sha256 (messageIdInput topic data) with
  | .ok h => some (h.extract 0 Constants.messageIdLen)
  | .error _ => none

/-- The message id in the router's form. -/
def messageId (topic : String) (data : ByteArray) : Option MessageId :=
  (messageIdBytes topic data).map fun b => ⟨b.toList.map (·.toNat)⟩

end Libp2p.Eth2
