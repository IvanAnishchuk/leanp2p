import Bytes
import Crypto
import Libp2p.Identity

/-!
# discv5: the packet codec and the handshake crypto

The wire protocol of devp2p `discv5/discv5-wire.md` (protocol version
v5.1, `version = 0x0001`), which the consensus networking spec names for
peer discovery (phase0 `p2p-interface.md`, "The discovery domain:
discv5"). This module holds the pure codec and the crypto that the
handshake needs. The session table, the node table, the lookup, and the
UDP loop are in other modules.

A packet is `masking-iv ‖ masked-header ‖ message`:

* `masking-iv` is 16 random bytes.
* The header is `static-header ‖ authdata`, masked with AES-128-CTR
  under the first 16 bytes of the destination's node id and the IV.
* The static header is `"discv5" ‖ version ‖ flag ‖ nonce ‖
  authdata-size`, 23 bytes.
* The message is AES-128-GCM under the session key, with the packet's
  nonce, and with `masking-iv ‖ header` as the associated data.

CTR is a stream cipher, so the recipient unmasks the static header
first, reads `authdata-size`, and then unmasks the header in one run
from its start.
-/

set_option autoImplicit false

namespace Libp2p.Discv5

open Bytes

/-! ## Constants (discv5-wire.md, "Protocol Header") -/

/-- `"discv5"`. -/
def protocolId : ByteArray := "discv5".toUTF8

/-- The protocol version of v5.1. -/
def version : ByteArray := ⟨#[0x00, 0x01]⟩

/-- The static header: 6 + 2 + 1 + 12 + 2 bytes. -/
def staticHeaderLen : Nat := 23

/-- The masking IV. -/
def ivLen : Nat := 16

/-- "The minimum size of any Discovery v5 packet is 63 bytes." -/
def minPacket : Nat := 63

/-- "The maximum size of any packet is 1280 bytes." -/
def maxPacket : Nat := 1280

/-- The packet kinds, by `flag`. -/
inductive Flag where
  /-- An ordinary message packet: `authdata = src-id`. -/
  | message
  /-- WHOAREYOU: `authdata = id-nonce ‖ enr-seq`, no message. -/
  | whoareyou
  /-- A handshake message packet. -/
  | handshake
  deriving DecidableEq, Repr

def Flag.toByte : Flag → UInt8
  | .message => 0 | .whoareyou => 1 | .handshake => 2

def Flag.ofByte? : UInt8 → Option Flag
  | 0 => some .message | 1 => some .whoareyou | 2 => some .handshake | _ => none

/-- An unmasked header. -/
structure Header where
  flag : Flag
  /-- The 12-byte message nonce. -/
  nonce : ByteArray
  authdata : ByteArray

/-- The plain header bytes: `static-header ‖ authdata`. -/
def Header.encode (h : Header) : ByteArray :=
  let size := h.authdata.size
  protocolId ++ version ++ ⟨#[h.flag.toByte]⟩ ++ h.nonce ++
    ⟨#[(size / 256).toUInt8, (size % 256).toUInt8]⟩ ++ h.authdata

/-- What can go wrong reading a packet. -/
inductive Error where
  | size
  | protocol
  | flag
  | authdata
  | crypto (e : Crypto.CryptoError)
  | rlp
  deriving Repr

/-- The masking key: the first 16 bytes of the destination node id. -/
def maskingKey (destId : ByteArray) : Except Error Crypto.Key16 :=
  match Crypto.Key16.ofByteArray? (destId.extract 0 16) with
  | some k => .ok k
  | none => .error .size

private def ctr (destId iv data : ByteArray) : Except Error ByteArray := do
  let key ← maskingKey destId
  let some iv16 := Crypto.Key16.ofByteArray? iv | throw .size
  (Crypto.aes128Ctr key iv16 data).mapError .crypto

/-- An unmasked packet: the IV, the header, the header's plain bytes,
and the message ciphertext. -/
structure Unmasked where
  iv : ByteArray
  header : Header
  headerBytes : ByteArray
  message : ByteArray

/-- Unmask a packet sent to the node `localId`. The static header comes
first. Its `authdata-size` sets the length of the CTR run. -/
def unmask (localId packet : ByteArray) : Except Error Unmasked := do
  if packet.size < minPacket || maxPacket < packet.size then throw .size
  let iv := packet.extract 0 ivLen
  let static ← ctr localId iv (packet.extract ivLen (ivLen + staticHeaderLen))
  if static.extract 0 6 != protocolId || static.extract 6 8 != version then throw .protocol
  let some flag := Flag.ofByte? (static.get! 8) | throw .flag
  let size := (static.get! 21).toNat * 256 + (static.get! 22).toNat
  let headerEnd := ivLen + staticHeaderLen + size
  if packet.size < headerEnd then throw .authdata
  let plain ← ctr localId iv (packet.extract ivLen headerEnd)
  return { iv, headerBytes := plain
           header := { flag, nonce := plain.extract 9 21
                       authdata := plain.extract staticHeaderLen (staticHeaderLen + size) }
           message := packet.extract headerEnd packet.size }

/-- Mask a header for `destId` and append the sealed message. -/
def mask (destId iv : ByteArray) (h : Header) (message : ByteArray) : Except Error ByteArray := do
  let masked ← ctr destId iv h.encode
  return iv ++ masked ++ message

/-! ## The message (discv5-wire.md, "Protocol Header") -/

/-- Open the message of an unmasked packet with the session's read key:
AES-128-GCM, the packet's nonce, and `masking-iv ‖ header` as the
associated data. The answer is `message-type ‖ message-data`. -/
def openMessage (key : Crypto.Key16) (u : Unmasked) : Except Error ByteArray := do
  let some nonce := Crypto.Nonce12.ofByteArray? u.header.nonce | throw .size
  (Crypto.aes128GcmOpen key nonce (u.iv ++ u.headerBytes) u.message).mapError .crypto

/-- Seal a message for a header and IV. -/
def sealMessage (key : Crypto.Key16) (iv : ByteArray) (h : Header) (pt : ByteArray) :
    Except Error ByteArray := do
  let some nonce := Crypto.Nonce12.ofByteArray? h.nonce | throw .size
  (Crypto.aes128GcmSeal key nonce (iv ++ h.encode) pt).mapError .crypto

/-! ## The handshake crypto (discv5-theory.md, "Handshake Steps") -/

/-- The two session keys of a handshake. -/
structure SessionKeys where
  initiator : Crypto.Key16
  recipient : Crypto.Key16

/-- The session keys:
1. `secret = ecdh(dest-pubkey, ephemeral-key)`
2. `HKDF-Extract(challenge-data, secret)`
3. `HKDF-Expand` with `"discovery v5 key agreement" ‖ node-id-A ‖
   node-id-B`, to 32 bytes

ECDH is symmetric, so the recipient calls the same function with its
static key and the initiator's ephemeral public key. `idA` stays the
initiator's id on both sides. -/
def deriveKeys (ephemeralKey : Crypto.Key32) (destPubkey challengeData idA idB : ByteArray) :
    Except Error SessionKeys := do
  let secret ← (Crypto.secp256k1Ecdh ephemeralKey destPubkey).mapError .crypto
  let info := "discovery v5 key agreement".toUTF8 ++ idA ++ idB
  let kd ← (Crypto.hkdfSha256 challengeData secret info 32).mapError .crypto
  let some i := Crypto.Key16.ofByteArray? (kd.extract 0 16) | throw .size
  let some r := Crypto.Key16.ofByteArray? (kd.extract 16 32) | throw .size
  return { initiator := i, recipient := r }

/-- The input of the id signature, before its SHA-256. -/
def idSignatureInput (challengeData ephPubkey idB : ByteArray) : ByteArray :=
  "discovery v5 identity proof".toUTF8 ++ challengeData ++ ephPubkey ++ idB

/-- `id_sign(sha256(id-signature-input))`: 64 bytes, `r ‖ s`. -/
def idSign (staticKey : Crypto.Key32) (challengeData ephPubkey idB : ByteArray) :
    Except Error ByteArray := do
  let digest ← (Crypto.sha256 (idSignatureInput challengeData ephPubkey idB)).mapError .crypto
  let some d := Crypto.Digest32.ofByteArray? digest | throw .size
  (Crypto.secp256k1SignDigest staticKey d).mapError .crypto

/-- Verify an id signature against the signer's compressed public key,
through key recovery as the `v4` ENR check does (`Enr.verifyV4`), with
SHA-256 in place of keccak-256. A high S fails. -/
def idVerify (pubkey : ByteArray) (sig challengeData ephPubkey idB : ByteArray) : Bool :=
  match Crypto.sha256 (idSignatureInput challengeData ephPubkey idB) with
  | .error _ => false
  | .ok digest =>
    let r := sig.extract 0 32
    let s := sig.extract 32 64
    sig.size == 64 &&
    !(Libp2p.Identity.Enr.halfOrder < Libp2p.Identity.Rlp.beNat (toNatList s)) &&
    ([0, 1, 2, 3] : List UInt32).any fun recId =>
      let xy := Crypto.secp256k1Recover digest r s recId
      xy.size == 64 && ofNatList (Libp2p.Identity.Enr.compress xy) == pubkey

end Libp2p.Discv5
