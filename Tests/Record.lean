import Tests.Support
import Bytes
import Proto
import Libp2p.Identity
import Libp2p.Host

/-!
# Signed envelopes and peer records (RFC 0002, RFC 0003)

The checks of `Libp2p.Identity.Record` and of the host's record store:

* The domain and payload-type constants are the ASCII bytes of their
  strings.
* go-libp2p v0.51.0 vector: `scripts/pubsub-go record R 7 …` sealed the
  record of the Ed25519 key of 32 bytes of `R`, with seq 7 and two
  addresses. Ed25519 signs deterministically, so our signature of the
  same record must give the same bytes. The vector also opens, and names
  the peer, the seq, and the addresses.
* A secp256k1 record round-trips through sign and open; its signature
  draws a nonce, so only the open is checked.
* The rejections, one each: a flipped signature byte, an unknown payload
  type, a record that names another peer than its signer, and bytes that
  are not an envelope. The legacy pair of RFC 0003 opens.
* The host store: a newer `seq` replaces the record, an older or equal
  one does not, and a record for another peer than the expected one is
  refused. A taken record adds its addresses to the peerstore.
-/

set_option autoImplicit false

namespace Tests.Record

open Bytes Libp2p.Identity

/-- go-libp2p's bytes for the record of seed `R`, seq 7, and the
addresses `/ip4/127.0.0.1/tcp/4001` and `/ip4/10.0.0.1/udp/9000/quic-v1`. -/
def goVector : String :=
  "0a24080112202012cb90ca60e8e5d8daf66e2272d2233e0486d557e8c66141ed8920177d7eb712020301" ++
  "1a450a260024080112202012cb90ca60e8e5d8daf66e2272d2233e0486d557e8c66141ed8920177d7eb7" ++
  "10071a0a0a08047f000001060fa11a0d0a0b040a00000191022328cd032a4003e85d111a2ab3dd40ec72" ++
  "acf875a757573c9b2ada270cd2a09a2c751628fd42afab78f44abe5c22dfb86c3f770641f4201e51db36" ++
  "43865ce6e702c0e931bc0a"

/-- The addresses of the go vector. -/
def goAddrs : List String := ["/ip4/127.0.0.1/tcp/4001", "/ip4/10.0.0.1/udp/9000/quic-v1"]

/-- The value of an `Except`, or a failed run. -/
private def expectOk {ε α : Type} [Repr ε] (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{what}: {repr e}"

/-- The Ed25519 key of 32 bytes of one character. -/
private def edKey (c : Char) : IO PrivKey :=
  expectOk "key" (PrivKey.ofData? .ed25519 ⟨Array.replicate 32 c.toNat.toUInt8⟩)

/-- A secp256k1 key of 32 bytes of one value. -/
private def secpKey (v : UInt8) : IO PrivKey :=
  expectOk "key" (PrivKey.ofData? .secp256k1 ⟨Array.replicate 32 v⟩)

/-- The peer id of a key. -/
private def peerOf (k : PrivKey) : IO PeerId :=
  expectOk "peer id" (k.toPublic.bind PeerId.ofPubKey)

/-- The multiaddrs of their text forms. -/
private def addrsOf (l : List String) : IO (List Multiformats.Multiaddr) :=
  l.mapM fun s => expectOk "address" (Multiformats.Multiaddr.parse? s)

/-- Sign a record, or fail the run. -/
private def signed (k : PrivKey) (r : PeerRecord) : IO ByteArray := do
  match ← (PeerRecord.sign k r).run with
  | .ok e => pure e.marshal
  | .error e => throw <| IO.userError s!"sign: {repr e}"

/-- A host with no transport: enough for its stores. -/
private def bareHost (k : PrivKey) : IO Libp2p.Host.Host := do
  let config : Libp2p.Host.Config :=
    { identity := k, transports := [], security := [], muxers := [] }
  expectOk "host" (← (Libp2p.Host.Host.new config : BaseIO _))

def run (r : Runner) : IO Unit := do
  r.section "Signed peer records" "RFC/0002-signed-envelopes.md, RFC/0003-routing-records.md"

  -- The constants.
  r.check "record.domain.ascii" (peerRecordDomain == toNatList "libp2p-peer-record".toUTF8)
  r.check "record.legacy-domain.ascii"
    (legacyRecordDomain == toNatList "libp2p-routing-state".toUTF8)
  r.check "record.legacy-type.ascii"
    (legacyRecordPayloadType == toNatList "/libp2p/routing-state-record".toUTF8)

  -- The go vector: byte-identical sign, and the open.
  let rKey ← edKey 'R'
  let rPeer ← peerOf rKey
  let vector ← unhex "go vector" goVector
  let ours ← signed rKey { peerId := rPeer, seq := 7, addrs := ← addrsOf goAddrs }
  r.check "record.go.sign-bytes" (ours == vector)
  match PeerRecord.open? vector with
  | .ok (_, rec) =>
    r.check "record.go.open.peer" (rec.peerId.hash == rPeer.hash)
    r.check "record.go.open.seq" (rec.seq == 7)
    r.check "record.go.open.addrs" (rec.addrs.map toString == goAddrs)
  | .error e => r.check s!"record.go.open ({repr e})" false
  -- The production decoder reads the vector as the model does.
  r.check "record.go.envelope-model"
    ((Pb.decodeMessageB? (α := EnvelopeMsg) vector).toOption.map (·.1) ==
      (Pb.decodeMessage? (α := EnvelopeMsg) (toNatList vector)).toOption.map (·.1))

  -- secp256k1: sign, then open.
  let sKey ← secpKey 0x11
  let sPeer ← peerOf sKey
  let sBytes ← signed sKey { peerId := sPeer, seq := 1, addrs := ← addrsOf ["/ip4/1.2.3.4/tcp/1"] }
  r.check "record.secp256k1.open"
    (match PeerRecord.open? sBytes with
     | .ok (_, rec) => rec.peerId.hash == sPeer.hash && rec.seq == 1
     | .error _ => false)

  -- The rejections.
  let flipped := vector.set! (vector.size - 1) (vector.get! (vector.size - 1) ^^^ 1)
  r.check "record.reject.signature" (failsWith Error.badSignature (PeerRecord.open? flipped |>.map (·.2.seq)))
  let other ← peerOf (← edKey 'S')
  let lying ← signed rKey { peerId := other, seq := 1, addrs := [] }
  r.check "record.reject.peer" (failsWith Error.recordPeer (PeerRecord.open? lying |>.map (·.2.seq)))
  let typed ← match ← (Envelope.sign rKey peerRecordDomain [0x03, 0x02]
      (toNatList (PeerRecord.marshal { peerId := rPeer, seq := 1, addrs := [] }))).run with
    | .ok e => pure e.marshal
    | .error e => throw <| IO.userError s!"sign: {repr e}"
  r.check "record.reject.payload-type"
    (failsWith Error.payloadType (PeerRecord.open? typed |>.map (·.2.seq)))
  r.check "record.reject.garbage" ((PeerRecord.open? ⟨#[0xff, 0x01]⟩).toOption.isNone)
  -- A record signed for the peer-record domain does not open under
  -- another one (RFC 0002, "Domain Separation").
  r.check "record.domain-separation"
    (match Envelope.unmarshal? vector with
     | .ok e => !e.verify legacyRecordDomain && e.verify peerRecordDomain
     | .error _ => false)
  let legacy ← match ← (Envelope.sign rKey legacyRecordDomain legacyRecordPayloadType
      (toNatList (PeerRecord.marshal { peerId := rPeer, seq := 3, addrs := [] }))).run with
    | .ok e => pure e.marshal
    | .error e => throw <| IO.userError s!"sign: {repr e}"
  r.check "record.legacy.open"
    (match PeerRecord.open? legacy with
     | .ok (_, rec) => rec.seq == 3
     | .error _ => false)

  -- The host store.
  let h ← bareHost (← edKey 'H')
  let first ← h.consumeRecord vector (some rPeer)
  r.check "record.store.first" (match first with | .ok (_, took) => took | .error _ => false)
  r.check "record.store.addrs" ((← h.addrsOf rPeer).map toString == goAddrs)
  r.check "record.store.kept" ((← h.recordOf rPeer) == some vector)
  let same ← h.consumeRecord vector (some rPeer)
  r.check "record.store.equal-seq" (match same with | .ok (_, took) => !took | .error _ => false)
  let older ← signed rKey { peerId := rPeer, seq := 6, addrs := [] }
  let olderAns ← h.consumeRecord older (some rPeer)
  r.check "record.store.older" (match olderAns with | .ok (_, took) => !took | .error _ => false)
  r.check "record.store.older-kept" ((← h.recordOf rPeer) == some vector)
  let newer ← signed rKey { peerId := rPeer, seq := 8, addrs := [] }
  let newerAns ← h.consumeRecord newer (some rPeer)
  r.check "record.store.newer" (match newerAns with | .ok (_, took) => took | .error _ => false)
  r.check "record.store.newer-kept" ((← h.recordOf rPeer) == some newer)
  let wrong ← h.consumeRecord vector (some other)
  r.check "record.store.expected-peer" (failsWith Error.recordPeer (wrong.map (·.2)))
  -- Our own record, through the host.
  match ← h.signRecord (← addrsOf ["/ip4/127.0.0.1/tcp/9"]) 5 with
  | .ok b =>
    r.check "record.own.open"
      (match PeerRecord.open? b with
       | .ok (_, rec) => rec.peerId.hash == h.localPeer.hash && rec.seq == 5
       | .error _ => false)
  | .error e => r.check s!"record.own ({repr e})" false

end Tests.Record
