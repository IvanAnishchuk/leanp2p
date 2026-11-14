import Proto
import Bytes
import Multiformats
import Libp2p.Identity.Constants
import Libp2p.Identity.Error
import Libp2p.Identity.Keys
import Libp2p.Identity.Unmarshal
import Libp2p.Identity.PeerId

/-!
# Signed envelopes and peer records

RFC 0002 (`RFC/0002-signed-envelopes.md`) defines the signed envelope: a
payload, a payload type, the signer's public key, and a signature over
the three under a domain string. RFC 0003 (`RFC/0003-routing-records.md`)
defines the peer record that gossipsub's peer exchange and identify carry
inside one: a peer id, a sequence number, and the peer's addresses.

```
message Envelope {
  PublicKey public_key = 1;
  bytes payload_type = 2;
  bytes payload = 3;
  bytes signature = 5;
}
message PeerRecord {
  message AddressInfo { bytes multiaddr = 1; }
  bytes peer_id = 1;
  uint64 seq = 2;
  repeated AddressInfo addresses = 3;
}
```

Both messages are proto3, so an empty `bytes` field and a zero `seq` stay
off the wire. go-libp2p writes them so, and the encoder here matches its
bytes.

**The signed bytes.** The signature covers the domain, the payload type,
and the payload, each prefixed with its length as an unsigned varint
(RFC 0002, "Signature Production"; go-libp2p `makeUnsigned`). The domain
is in no field: the reader supplies it, so a signature made for one
purpose never verifies for another.

**Two layers.** `EnvelopeMsg` and `PeerRecordMsg` are the wire model over
the `List Nat` byte model, with the round trip proved (CLAUDE.md,
"Proofs and tests", rule 1). `Envelope` and `PeerRecord` are the typed
values above them: a checked key, a peer id, and multiaddrs. The
signature check calls the backend, so the vectors and the interop runs
pin it (rule 3).

**Domain and payload type.** RFC 0003 names `libp2p-routing-state` and
`"/libp2p/routing-state-record"`. go-libp2p signs with
`libp2p-peer-record` and the multicodec 0x0301 instead. rust-libp2p opens
that pair with `from_signed_envelope_interop`, and it keeps the RFC pair
as the legacy form. The seal writes go's pair. The open accepts either
pair, each with its own domain.
-/

set_option autoImplicit false

namespace Libp2p.Identity

open Bytes

/-! ## The wire model -/

/-- One length-delimited entry, or none for an empty payload: proto3
does not write an empty `bytes` field. -/
def optBytes (num : Nat) (bs : List Nat) : List Pb.Entry :=
  if bs = [] then [] else [(num, .bytes bs)]

/-- The checked field table of an entry list. Fail closed: a list whose
entries do not fit the wire model gives the empty table. -/
def fieldsOfEntries (es : List Pb.Entry) : Pb.Fields :=
  if h : ∀ e ∈ es, e.Valid then ⟨es, h⟩ else Pb.Fields.empty

/-- A signed envelope on the wire. `publicKey` holds the marshaled
`PublicKey` message. -/
structure EnvelopeMsg where
  /-- The marshaled public key. -/
  publicKey : List Nat
  /-- The payload type. -/
  payloadType : List Nat
  /-- The payload. -/
  payload : List Nat
  /-- The signature. -/
  signature : List Nat
  deriving DecidableEq, Repr

namespace EnvelopeMsg

/-- The entries in field order. -/
def entries (e : EnvelopeMsg) : List Pb.Entry :=
  optBytes envelopeKeyField e.publicKey ++ optBytes envelopeTypeField e.payloadType ++
    optBytes envelopePayloadField e.payload ++ optBytes envelopeSignatureField e.signature

/-- Every entry fits the wire model: each byte below 256 and each length
within the varint budget. -/
def Valid (e : EnvelopeMsg) : Prop := ∀ x ∈ e.entries, x.Valid

instance (e : EnvelopeMsg) : Decidable e.Valid := by
  unfold Valid
  infer_instance

/-- The field table. -/
def toFields (e : EnvelopeMsg) : Pb.Fields := fieldsOfEntries e.entries

/-- The message of a field table. A missing field is empty. A present
field of another wire type gives `badField`, as the go protobuf runtime
rejects it. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error EnvelopeMsg := do
  let publicKey ← Pb.bytesField? envelopeKeyField fs
  let payloadType ← Pb.bytesField? envelopeTypeField fs
  let payload ← Pb.bytesField? envelopePayloadField fs
  let signature ← Pb.bytesField? envelopeSignatureField fs
  .ok { publicKey := publicKey.getD [], payloadType := payloadType.getD [],
        payload := payload.getD [], signature := signature.getD [] }

instance : Pb.ProtoMessage EnvelopeMsg where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law: a valid message reads back from its own entries. -/
theorem ofFieldsToFields (e : EnvelopeMsg) (h : e.Valid) :
    ofFields? (toFields e) = .ok e := by
  -- `Valid` is a definition, so the `dite` condition only matches after
  -- `h` takes its unfolded type.
  have h' : ∀ x ∈ e.entries, x.Valid := h
  rw [toFields, fieldsOfEntries, dite_eq_left h']
  obtain ⟨k, t, p, s⟩ := e
  -- Each field is either absent (an empty payload) or one entry. The
  -- sixteen cases differ only in which lookups miss.
  by_cases hk : k = [] <;> by_cases ht : t = [] <;> by_cases hp : p = [] <;>
    by_cases hs : s = [] <;>
    simp [ofFields?, entries, optBytes, Pb.bytesField?, Pb.hasField, Pb.getBytes?,
      Pb.lookupLast, List.lookup_cons, envelopeKeyField, envelopeTypeField,
      envelopePayloadField, envelopeSignatureField, hk, ht, hp, hs, Bind.bind, Except.bind]

/-- An encoded message decodes back to itself, with no input left. -/
theorem decodeEncode (e : EnvelopeMsg) (h : e.Valid) :
    Pb.decodeMessage? (Pb.encodeMessage e) = .ok (e, []) := by
  show (do let (fs, rest) ← Pb.decodeFields? (Pb.encodeFields (toFields e))
           let value ← ofFields? fs
           .ok (value, rest)) = _
  rw [Pb.decodeEncode]
  simp [ofFieldsToFields e h, Bind.bind, Except.bind]

end EnvelopeMsg

/-- The `AddressInfo` entries of one multiaddr. -/
def addressEntries (a : List Nat) : List Pb.Entry := optBytes addressMultiaddrField a

/-- The encoded `AddressInfo` of one multiaddr. -/
def encodeAddress (a : List Nat) : List Nat := Pb.encodeFields (fieldsOfEntries (addressEntries a))

/-- The multiaddr bytes of an encoded `AddressInfo`. A missing field is
empty, and the typed layer drops an empty address. -/
def decodeAddress (bs : List Nat) : Except Pb.Error (List Nat) := do
  let (fs, _) ← Pb.decodeFields? bs
  let a ← Pb.bytesField? addressMultiaddrField fs
  .ok (a.getD [])

/-- A peer record on the wire. -/
structure PeerRecordMsg where
  /-- The peer id bytes, the multihash. -/
  peerId : List Nat
  /-- The sequence number. -/
  seq : Nat
  /-- The multiaddr bytes, in wire order. -/
  addrs : List (List Nat)
  deriving DecidableEq, Repr

namespace PeerRecordMsg

/-- The entries in field order. A zero `seq` stays off the wire. -/
def entries (r : PeerRecordMsg) : List Pb.Entry :=
  optBytes recordPeerIdField r.peerId ++
    (if r.seq = 0 then [] else [(recordSeqField, .varint r.seq)]) ++
    r.addrs.map (fun a => (recordAddrsField, .bytes (encodeAddress a)))

/-- Every entry fits the wire model, and so does every address entry. -/
def Valid (r : PeerRecordMsg) : Prop :=
  (∀ x ∈ r.entries, x.Valid) ∧ ∀ a ∈ r.addrs, ∀ x ∈ addressEntries a, x.Valid

instance (r : PeerRecordMsg) : Decidable r.Valid := by
  unfold Valid
  infer_instance

/-- The field table. -/
def toFields (r : PeerRecordMsg) : Pb.Fields := fieldsOfEntries r.entries

/-- The addresses of a list of encoded `AddressInfo` messages, in order. -/
def decodeAddresses : List (List Nat) → Except Pb.Error (List (List Nat))
  | [] => .ok []
  | bs :: rest => do
    let a ← decodeAddress bs
    let as ← decodeAddresses rest
    .ok (a :: as)

/-- The message of a field table. A missing `peer_id` is empty, and a
missing `seq` is zero. The typed layer rejects the empty peer id. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error PeerRecordMsg := do
  let peerId ← Pb.bytesField? recordPeerIdField fs
  let seq ← Pb.varintField? recordSeqField fs
  let addrs ← decodeAddresses (Pb.getAllBytes recordAddrsField fs)
  .ok { peerId := peerId.getD [], seq := seq.getD 0, addrs }

instance : Pb.ProtoMessage PeerRecordMsg where
  toFields := toFields
  ofFields? := ofFields?

/-- One address reads back from its encoding. -/
theorem decodeAddressEncode (a : List Nat) (h : ∀ x ∈ addressEntries a, x.Valid) :
    decodeAddress (encodeAddress a) = .ok a := by
  simp only [decodeAddress, encodeAddress, fieldsOfEntries, dite_eq_left h, Pb.decodeEncode]
  by_cases ha : a = [] <;>
    simp [addressEntries, optBytes, Pb.bytesField?, Pb.hasField, Pb.getBytes?, Pb.lookupLast,
      addressMultiaddrField, ha, Bind.bind, Except.bind]

/-- The addresses read back from their encodings, in order. -/
theorem decodeAddressesEncode (as : List (List Nat))
    (h : ∀ a ∈ as, ∀ x ∈ addressEntries a, x.Valid) :
    decodeAddresses (as.map encodeAddress) = .ok as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, decodeAddresses]
    rw [decodeAddressEncode a (h a (by simp)),
      ih (fun b hb => h b (by simp [hb]))]
    rfl

/-- The address payloads of the entries are the encoded addresses: the
peer id and `seq` entries carry other field numbers. -/
private theorem allAddrs (r : PeerRecordMsg) {hv : ∀ e ∈ r.entries, e.Valid} :
    Pb.getAllBytes recordAddrsField ⟨r.entries, hv⟩ = r.addrs.map encodeAddress := by
  simp only [Pb.getAllBytes, entries, List.filterMap_append, List.filterMap_map]
  by_cases hp : r.peerId = [] <;> by_cases hs : r.seq = 0 <;>
    simp [optBytes, hp, hs, recordPeerIdField, recordSeqField, recordAddrsField,
      Function.comp_def]

/-- A singular lookup of another field number misses every address
entry. -/
private theorem lookupAddrsMiss (k : Nat) (hk : k ≠ 3) (addrs : List (List Nat)) :
    ((addrs.map (fun a => ((3 : Nat), Pb.Value.bytes (encodeAddress a)))).reverse).lookup k =
      none := by
  rw [← List.map_reverse]
  generalize addrs.reverse = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hne : (k == 3) = false := by simp [hk]
    simp [List.lookup_cons, hne, ih]

/-- The table law: a valid record reads back from its own entries. -/
theorem ofFieldsToFields (r : PeerRecordMsg) (h : r.Valid) :
    ofFields? (toFields r) = .ok r := by
  obtain ⟨he, ha⟩ := h
  rw [toFields, fieldsOfEntries, dite_eq_left he]
  simp only [ofFields?]
  rw [allAddrs (hv := he), decodeAddressesEncode r.addrs ha]
  obtain ⟨pid, seq, addrs⟩ := r
  by_cases hp : pid = [] <;> by_cases hs : seq = 0 <;>
    simp [entries, optBytes, Pb.bytesField?, Pb.varintField?, Pb.hasField, Pb.getBytes?,
      Pb.getVarint?, Pb.lookupLast, recordPeerIdField, recordSeqField, recordAddrsField,
      List.lookup_append, List.lookup_cons, lookupAddrsMiss 1 (by decide),
      lookupAddrsMiss 2 (by decide), hp, hs, Bind.bind, Except.bind]

/-- An encoded record decodes back to itself, with no input left. -/
theorem decodeEncode (r : PeerRecordMsg) (h : r.Valid) :
    Pb.decodeMessage? (Pb.encodeMessage r) = .ok (r, []) := by
  show (do let (fs, rest) ← Pb.decodeFields? (Pb.encodeFields (toFields r))
           let value ← ofFields? fs
           .ok (value, rest)) = _
  rw [Pb.decodeEncode]
  simp [ofFieldsToFields r h, Bind.bind, Except.bind]

end PeerRecordMsg

/-! ## The signed bytes -/

/-- The bytes a signature covers: the domain, the payload type, and the
payload, each after its length as an unsigned varint (RFC 0002,
"Signature Production"). -/
def unsignedBytes (domain payloadType payload : List Nat) : List Nat :=
  Pb.encodeNat domain.length ++ domain ++ Pb.encodeNat payloadType.length ++ payloadType ++
    Pb.encodeNat payload.length ++ payload

/-! ## The typed envelope -/

/-- A signed envelope with a checked public key. The type does not check
the signature: `Envelope.open?` checks it against a domain. -/
structure Envelope where
  /-- The signer's public key. -/
  publicKey : PubKey
  /-- The payload type. -/
  payloadType : ByteArray
  /-- The payload. -/
  payload : ByteArray
  /-- The signature over `unsignedBytes`. -/
  signature : ByteArray

namespace Envelope

/-- The wire model of the envelope. -/
def toMsg (e : Envelope) : EnvelopeMsg where
  publicKey := toNatList e.publicKey.marshal
  payloadType := toNatList e.payloadType
  payload := toNatList e.payload
  signature := toNatList e.signature

/-- The wire bytes. -/
def marshal (e : Envelope) : ByteArray := Pb.encodeMessageB e.toMsg

/-- The signature verifies under the envelope's key for `domain`. -/
def verify (e : Envelope) (domain : List Nat) : Bool :=
  e.publicKey.verify
    (ofNatList (unsignedBytes domain (toNatList e.payloadType) (toNatList e.payload)))
    e.signature

/-- Sign a payload under a domain: RFC 0002, "Signature Production".
(`seal` is a Lean keyword, so the name is `sign`.) -/
def sign (key : PrivKey) (domain payloadType payload : List Nat) : ExceptT Error IO Envelope := do
  let pub ← ExceptT.mk (pure key.toPublic)
  let sig ← key.sign (ofNatList (unsignedBytes domain payloadType payload))
  return { publicKey := pub, payloadType := ofNatList payloadType,
           payload := ofNatList payload, signature := sig }

/-- The envelope of wire bytes, with its key checked and its signature
not yet checked. -/
def unmarshal? (b : ByteArray) : Except Error Envelope := do
  let (m, _) ← (Pb.decodeMessageB? (α := EnvelopeMsg) b).mapError .message
  let pub ← PubKey.unmarshal? (ofNatList m.publicKey)
  return { publicKey := pub, payloadType := ofNatList m.payloadType,
           payload := ofNatList m.payload, signature := ofNatList m.signature }

/-- The envelope of wire bytes whose signature verifies for `domain`
(RFC 0003: "a peer MUST validate the signature before deserializing"). -/
def open? (b : ByteArray) (domain : List Nat) : Except Error Envelope := do
  let e ← unmarshal? b
  if e.verify domain then return e else throw .badSignature

end Envelope

/-! ## The typed peer record -/

/-- A peer record: the peer id, the sequence number, and the addresses. -/
structure PeerRecord where
  /-- The peer the record describes. -/
  peerId : PeerId
  /-- The sequence number: a newer record has a higher one (RFC 0003). -/
  seq : Nat
  /-- The addresses. -/
  addrs : List Multiformats.Multiaddr

namespace PeerRecord

/-- The wire model of the record. -/
def toMsg (r : PeerRecord) : PeerRecordMsg where
  peerId := toNatList r.peerId.toBytes
  seq := r.seq
  addrs := (r.addrs.map Multiformats.Multiaddr.toBytes).filter (· ≠ [])

/-- The payload bytes. -/
def marshal (r : PeerRecord) : ByteArray := ofNatList (Pb.encodeMessage r.toMsg)

/-- The record of payload bytes. The decode drops an address that does
not decode, as go-libp2p's `addrsFromProtobuf` does. rust-libp2p
rejects the whole record. -/
def unmarshal? (b : ByteArray) : Except Error PeerRecord := do
  let (m, _) ← (Pb.decodeMessage? (α := PeerRecordMsg) (toNatList b)).mapError .message
  let peerId ← PeerId.ofBytes? (ofNatList m.peerId)
  let addrs := m.addrs.filterMap fun a =>
    if a = [] then none else (Multiformats.Multiaddr.ofBytes? a).toOption
  return { peerId, seq := m.seq, addrs }

/-- Sign the record with the peer's key, under go-libp2p's domain and
payload type. -/
def sign (key : PrivKey) (r : PeerRecord) : ExceptT Error IO Envelope :=
  Envelope.sign key peerRecordDomain peerRecordPayloadType (toNatList r.marshal)

/-- Which domain a payload type signs under: go's pair, or the legacy
pair of RFC 0003. -/
def domainOf? (payloadType : List Nat) : Option (List Nat) :=
  if payloadType = peerRecordPayloadType then some peerRecordDomain
  else if payloadType = legacyRecordPayloadType then some legacyRecordDomain
  else none

/-- The verified record of a signed envelope's bytes. The steps follow
RFC 0003, "Signed Envelopes": check the payload type, verify the
signature under the domain of that type, decode the payload, then check
that the envelope's key derives the record's peer id. -/
def open? (b : ByteArray) : Except Error (Envelope × PeerRecord) := do
  let e ← Envelope.unmarshal? b
  let some domain := domainOf? (toNatList e.payloadType) | throw .payloadType
  if !e.verify domain then throw .badSignature
  let r ← unmarshal? e.payload
  let signer ← PeerId.ofPubKey e.publicKey
  if signer.hash != r.peerId.hash then throw .recordPeer
  return (e, r)

end PeerRecord

end Libp2p.Identity
