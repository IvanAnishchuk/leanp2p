import Bytes
import Libp2p.Identity

/-!
# discv5: the protocol messages

The six messages a consensus node uses (devp2p `discv5-wire.md`,
"Protocol Messages"): PING, PONG, FINDNODE, NODES, TALKREQ, TALKRESP.
The topic messages (REGTOPIC to TOPICNODES) are left out: the consensus
spec finds subnet peers through the record's `attnets` and `syncnets`
(phase0 `p2p-interface.md`, "How are we going to discover peers in a
gossipsub topic?").

Each message is `message-type ‖ RLP(message-data)`, and every
`message-data` list starts with the request id, an RLP byte array of at
most 8 bytes, which a response mirrors.

## The model and the production path

The codec is stated over the `List Nat` byte model (`encodeModel`,
`decodeModel?`), on top of the proved RLP of `Libp2p.Identity.Rlp`. The
`ByteArray` functions the node runs (`encode`, `decode?`) are the model
behind one conversion each way, so the two views cannot drift
(CLAUDE.md, "Proofs and tests", rule 2).

The round trip is a theorem for each message a node builds itself:
`decodeModel? (encodeModel m) = some m` when `m` is well formed
(`WellFormed`: a request id of at most 8 bytes, every byte below 256,
each number within its field's width, and payloads that fit a packet).
NODES is the exception: its records decode through `Enr.decode?`, which
verifies a secp256k1 signature over the FFI, so its round trip is
checked by the wire vectors and the suite (rule 3).
-/

set_option autoImplicit false

namespace Libp2p.Discv5

open Bytes Libp2p.Identity

/-- The protocol messages. -/
inductive Message where
  /-- PING (0x01): the sender's record sequence number. -/
  | ping (requestId : List Nat) (enrSeq : Nat)
  /-- PONG (0x02): the sender's record sequence number, and the address
  and port the sender saw the PING come from. -/
  | pong (requestId : List Nat) (enrSeq : Nat) (ip : List Nat) (port : Nat)
  /-- FINDNODE (0x03): the log2 distances to collect. -/
  | findNode (requestId : List Nat) (distances : List Nat)
  /-- NODES (0x04): one of `total` answers, with encoded records. -/
  | nodes (requestId : List Nat) (total : Nat) (records : List Enr)
  /-- TALKREQ (0x05). -/
  | talkReq (requestId : List Nat) (protocol : List Nat) (request : List Nat)
  /-- TALKRESP (0x06). -/
  | talkResp (requestId : List Nat) (response : List Nat)

namespace Message

/-- The request id a message carries. -/
def requestId : Message → List Nat
  | .ping r _ | .pong r _ _ _ | .findNode r _ | .nodes r _ _ | .talkReq r _ _ | .talkResp r _ => r

/-- True for a request; a response answers one. -/
def isRequest : Message → Bool
  | .ping .. | .findNode .. | .talkReq .. => true
  | _ => false

/-- The RLP string of a scalar: its minimal big-endian bytes. -/
def scalar (n : Nat) : Rlp.Item := .bytes (Rlp.ofScalar n)

/-- The RLP list of a message's data, and its type byte. -/
def body : Message → Nat × Rlp.Item
  | .ping r seq => (0x01, .list [.bytes r, scalar seq])
  | .pong r seq ip port => (0x02, .list [.bytes r, scalar seq, .bytes ip, scalar port])
  | .findNode r ds => (0x03, .list [.bytes r, .list (ds.map scalar)])
  | .nodes r total rs =>
    -- A record is an RLP list on the wire; its encoding is that list.
    let items := rs.filterMap fun e =>
      match Rlp.decode? (toNatList (Enr.encode e)) with
      | .ok (v, []) => some v.item
      | _ => none
    (0x04, .list [.bytes r, scalar total, .list items])
  | .talkReq r proto req => (0x05, .list [.bytes r, .bytes proto, .bytes req])
  | .talkResp r resp => (0x06, .list [.bytes r, .bytes resp])

/-- The plaintext of a message in the byte model: its type byte, then
its RLP list. -/
def encodeModel (m : Message) : List Nat :=
  let (t, i) := m.body
  t :: Rlp.encode i

/-- The plaintext of a message, as the node sends it. -/
def encode (m : Message) : ByteArray := ofNatList m.encodeModel

/-- A scalar field, `none` past `maxBytes` bytes or with a leading zero. -/
def scalarOf? (maxBytes : Nat) : Rlp.Item → Option Nat
  | .bytes b => Rlp.scalar? maxBytes b
  | .list _ => none

/-- A request id: a byte array of at most 8 bytes. -/
def requestIdOf? : Rlp.Item → Option (List Nat)
  | .bytes b => if b.length ≤ 8 then some b else none
  | .list _ => none

/-- The message of a type byte and its RLP items. `none` for an unknown
type or a malformed body. -/
def ofItems? : Nat → List Rlp.Item → Option Message
  | 0x01, [r, seq] => return .ping (← requestIdOf? r) (← scalarOf? 8 seq)
  | 0x02, [r, seq, .bytes ip, port] =>
    if ip.length != 4 && ip.length != 16 then none
    else return .pong (← requestIdOf? r) (← scalarOf? 8 seq) ip (← scalarOf? 2 port)
  | 0x03, [r, .list ds] => return .findNode (← requestIdOf? r) (← ds.mapM (scalarOf? 2))
  | 0x04, [r, total, .list rs] => do
    let records ← rs.mapM fun i => (Enr.decode? (ofNatList (Rlp.encode i))).toOption
    return .nodes (← requestIdOf? r) (← scalarOf? 8 total) records
  | 0x05, [r, .bytes proto, .bytes req] => return .talkReq (← requestIdOf? r) proto req
  | 0x06, [r, .bytes resp] => return .talkResp (← requestIdOf? r) resp
  | _, _ => none

/-- Decode a plaintext in the byte model. `none` for an empty input, a
body that is not one RLP list with nothing after it, or what `ofItems?`
refuses. -/
def decodeModel? : List Nat → Option Message
  | [] => none
  | t :: rest => do
    let (v, tail) ← (Rlp.decode? rest).toOption
    if !tail.isEmpty then none
    match v.item with
    | .list items => ofItems? t items
    | .bytes _ => none

/-- Decode a plaintext, as the node receives it. -/
def decode? (pt : ByteArray) : Option Message := decodeModel? (toNatList pt)

/-! ## The round trip -/

/-- The messages whose round trip is a theorem, and the bounds each
field needs. Every byte list holds bytes. The request id has at most 8
bytes; `seq` and `total` fit 8 bytes and the ports and distances 2; an
IP address has 4 or 16 bytes; the TALK payloads and the distance list
fit a 1280-byte packet. -/
def WellFormed : Message → Prop
  | .ping r seq => r.length ≤ 8 ∧ (∀ b ∈ r, b < 256) ∧ seq < 256 ^ 8
  | .pong r seq ip port =>
    r.length ≤ 8 ∧ (∀ b ∈ r, b < 256) ∧ seq < 256 ^ 8 ∧ (ip.length = 4 ∨ ip.length = 16) ∧
      (∀ b ∈ ip, b < 256) ∧ port < 256 ^ 2
  | .findNode r ds => r.length ≤ 8 ∧ (∀ b ∈ r, b < 256) ∧ ds.length ≤ 1280 ∧ ∀ d ∈ ds, d < 256 ^ 2
  | .nodes .. => False
  | .talkReq r proto req =>
    r.length ≤ 8 ∧ (∀ b ∈ r, b < 256) ∧ proto.length ≤ 1280 ∧ (∀ b ∈ proto, b < 256) ∧
      req.length ≤ 1280 ∧ ∀ b ∈ req, b < 256
  | .talkResp r resp =>
    r.length ≤ 8 ∧ (∀ b ∈ r, b < 256) ∧ resp.length ≤ 1280 ∧ ∀ b ∈ resp, b < 256

/-- The header of a payload under the 8-byte length bound takes at most
9 bytes. -/
private theorem lengthHeaderLe (offset len : Nat) (h : len < Rlp.maxPayload) :
    (Rlp.header offset len).length ≤ 9 := by
  unfold Rlp.header
  split
  · simp
  · have := Rlp.lengthBeBytesLe 8 h
    simp only [List.length_cons]
    omega

/-- A short byte string encodes in at most its length plus 9 bytes. -/
private theorem lengthEncodeBytesLe (bs : List Nat) (h : bs.length < Rlp.maxPayload) :
    (Rlp.encodeBytes bs).length ≤ bs.length + 9 := by
  unfold Rlp.encodeBytes
  split
  · omega
  · have := lengthHeaderLe 0x80 bs.length h
    simp only [List.length_append]
    omega

/-- A byte string is valid when it holds bytes and fits the bound. -/
private theorem validBytes (bs : List Nat) (hb : ∀ b ∈ bs, b < 256)
    (hl : bs.length < Rlp.maxPayload) : (Rlp.Item.bytes bs).valid = true := by
  simp only [Rlp.Item.valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨hb, hl⟩

/-- The scalar of a number below `256 ^ 8` is a valid string of at most
8 bytes. -/
private theorem validScalar (n : Nat) (h : n < 256 ^ 8) :
    (scalar n).valid = true ∧ (Rlp.ofScalar n).length ≤ 8 := by
  have hl := Rlp.lengthBeBytesLe 8 h
  refine ⟨validBytes _ (fun b hb => Rlp.ltOfMemBeBytes hb) ?_, hl⟩
  simp only [Rlp.ofScalar, Rlp.maxPayload] at *
  omega

/-- A list item is valid when its items are, and its payload fits. -/
private theorem validOfList (is : List Rlp.Item) (hv : Rlp.Item.validList is = true)
    (hl : (Rlp.encodeList is).length < Rlp.maxPayload) : (Rlp.Item.list is).valid = true := by
  simp only [Rlp.Item.valid, hv, Bool.true_and, decide_eq_true_eq]
  exact hl

/-- The bound every proof below uses: a payload that fits a packet fits
the RLP length bound by far. -/
private theorem ltMaxPayload {n : Nat} (h : n ≤ 20000) : n < Rlp.maxPayload := by
  simp only [Rlp.maxPayload]
  omega

/-- A scalar reads back as the number it encodes. -/
private theorem scalarOfScalar' {n k : Nat} (h : n < 256 ^ k) : scalarOf? k (scalar n) = some n :=
  Rlp.scalarOfScalar h

/-- A request id of at most 8 bytes reads back. -/
private theorem requestIdOfBytes {r : List Nat} (h : r.length ≤ 8) :
    requestIdOf? (.bytes r) = some r := by
  simp [requestIdOf?, h]

/-- The list of the distance scalars: valid, at most 11 bytes each,
and each reads back. -/
private theorem distanceList (ds : List Nat) (h : ∀ d ∈ ds, d < 256 ^ 2) :
    Rlp.Item.validList (ds.map scalar) = true ∧
      (Rlp.encodeList (ds.map scalar)).length ≤ 11 * ds.length ∧
      (ds.map scalar).mapM (scalarOf? 2) = some ds := by
  induction ds with
  | nil => simp [Rlp.Item.validList, Rlp.encodeList]
  | cons d ds ih =>
    have hd : d < 256 ^ 2 := h d (by simp)
    have hds : ∀ x ∈ ds, x < 256 ^ 2 := fun x hx => h x (by simp [hx])
    obtain ⟨hv, hl, hm⟩ := ih hds
    have h8 : d < 256 ^ 8 := Nat.lt_of_lt_of_le hd (Nat.pow_le_pow_right (by decide) (by decide))
    obtain ⟨hvd, _⟩ := validScalar d h8
    -- A distance takes at most 2 bytes, so its string at most 11.
    have hld : (Rlp.ofScalar d).length ≤ 2 := Rlp.lengthBeBytesLe 2 hd
    have hle := lengthEncodeBytesLe (Rlp.ofScalar d) (ltMaxPayload (by omega))
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, Rlp.Item.validList, hvd, hv, Bool.and_self]
    · simp only [List.map_cons, Rlp.encodeList, List.length_append, List.length_cons]
      simp only [scalar, Rlp.encode] at hle ⊢
      omega
    · simp only [List.map_cons, List.mapM_cons, hm, scalarOfScalar' hd]
      rfl

/-- A valid list item decodes back through `decodeModel?` to the message
`ofItems?` makes of its items. -/
private theorem decodeModelList (t : Nat) (items : List Rlp.Item)
    (hv : (Rlp.Item.list items).valid = true) :
    decodeModel? (t :: Rlp.encode (.list items)) = ofItems? t items := by
  have h := Rlp.decodeEncodeValue ⟨.list items, hv⟩
  simp only [decodeModel?, h, Except.toOption]
  rfl

/-- A well-formed message decodes back from its encoding. -/
theorem decodeEncode (m : Message) (h : m.WellFormed) : decodeModel? m.encodeModel = some m := by
  cases m with
  | ping r seq =>
    obtain ⟨hr, hrb, hs⟩ := h
    obtain ⟨hvs, hls⟩ := validScalar seq hs
    have h1 := lengthEncodeBytesLe r (ltMaxPayload (by omega))
    have h2 := lengthEncodeBytesLe (Rlp.ofScalar seq) (ltMaxPayload (by omega))
    have hv : (Rlp.Item.list [.bytes r, scalar seq]).valid = true := by
      apply validOfList
      · simp only [Rlp.Item.validList, validBytes r hrb (ltMaxPayload (by omega)), hvs,
          Bool.and_self]
      · simp only [Rlp.encodeList, Rlp.encode, scalar, List.length_append, List.length_nil]
        exact ltMaxPayload (by omega)
    simp only [encodeModel, body, decodeModelList _ _ hv, ofItems?, requestIdOfBytes hr,
      scalarOfScalar' hs]
    rfl
  | pong r seq ip port =>
    obtain ⟨hr, hrb, hs, hip, hipb, hp⟩ := h
    obtain ⟨hvs, hls⟩ := validScalar seq hs
    have hp8 : port < 256 ^ 8 := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) (by decide))
    obtain ⟨hvp, hlp⟩ := validScalar port hp8
    have hipl : ip.length ≤ 16 := by omega
    have h1 := lengthEncodeBytesLe r (ltMaxPayload (by omega))
    have h2 := lengthEncodeBytesLe (Rlp.ofScalar seq) (ltMaxPayload (by omega))
    have h3 := lengthEncodeBytesLe ip (ltMaxPayload (by omega))
    have h4 := lengthEncodeBytesLe (Rlp.ofScalar port) (ltMaxPayload (by omega))
    have hv : (Rlp.Item.list [.bytes r, scalar seq, .bytes ip, scalar port]).valid = true := by
      apply validOfList
      · simp only [Rlp.Item.validList, validBytes r hrb (ltMaxPayload (by omega)),
          validBytes ip hipb (ltMaxPayload (by omega)), hvs, hvp, Bool.and_self]
      · simp only [Rlp.encodeList, Rlp.encode, scalar, List.length_append, List.length_nil]
        exact ltMaxPayload (by omega)
    have hipc : (ip.length != 4 && ip.length != 16) = false := by
      rcases hip with hl | hl <;> simp [hl]
    simp only [encodeModel, body, decodeModelList _ _ hv, ofItems?, hipc, requestIdOfBytes hr,
      scalarOfScalar' hs, scalarOfScalar' hp]
    rfl
  | findNode r ds =>
    obtain ⟨hr, hrb, hdl, hds⟩ := h
    obtain ⟨hvl, hll, hm⟩ := distanceList ds hds
    have h1 := lengthEncodeBytesLe r (ltMaxPayload (by omega))
    have hh := lengthHeaderLe 0xc0 (Rlp.encodeList (ds.map scalar)).length
      (ltMaxPayload (by omega))
    have hv : (Rlp.Item.list [.bytes r, .list (ds.map scalar)]).valid = true := by
      apply validOfList
      · simp only [Rlp.Item.validList, validBytes r hrb (ltMaxPayload (by omega)),
          validOfList _ hvl (ltMaxPayload (by omega)), Bool.and_self]
      · simp only [Rlp.encodeList, Rlp.encode, List.length_append, List.length_nil]
        exact ltMaxPayload (by omega)
    simp only [encodeModel, body, decodeModelList _ _ hv, ofItems?, requestIdOfBytes hr, hm]
    rfl
  | nodes => exact h.elim
  | talkReq r proto req =>
    obtain ⟨hr, hrb, hpl, hpb, hql, hqb⟩ := h
    have h1 := lengthEncodeBytesLe r (ltMaxPayload (by omega))
    have h2 := lengthEncodeBytesLe proto (ltMaxPayload (by omega))
    have h3 := lengthEncodeBytesLe req (ltMaxPayload (by omega))
    have hv : (Rlp.Item.list [.bytes r, .bytes proto, .bytes req]).valid = true := by
      apply validOfList
      · simp only [Rlp.Item.validList, validBytes r hrb (ltMaxPayload (by omega)),
          validBytes proto hpb (ltMaxPayload (by omega)),
          validBytes req hqb (ltMaxPayload (by omega)), Bool.and_self]
      · simp only [Rlp.encodeList, Rlp.encode, List.length_append, List.length_nil]
        exact ltMaxPayload (by omega)
    simp only [encodeModel, body, decodeModelList _ _ hv, ofItems?, requestIdOfBytes hr]
    rfl
  | talkResp r resp =>
    obtain ⟨hr, hrb, hql, hqb⟩ := h
    have h1 := lengthEncodeBytesLe r (ltMaxPayload (by omega))
    have h2 := lengthEncodeBytesLe resp (ltMaxPayload (by omega))
    have hv : (Rlp.Item.list [.bytes r, .bytes resp]).valid = true := by
      apply validOfList
      · simp only [Rlp.Item.validList, validBytes r hrb (ltMaxPayload (by omega)),
          validBytes resp hqb (ltMaxPayload (by omega)), Bool.and_self]
      · simp only [Rlp.encodeList, Rlp.encode, List.length_append, List.length_nil]
        exact ltMaxPayload (by omega)
    simp only [encodeModel, body, decodeModelList _ _ hv, ofItems?, requestIdOfBytes hr]
    rfl

/-- The production path is the model: `decode?` reads the bytes the
model reads, and `encode` writes the bytes the model writes. With
`decodeEncode`, a well-formed message the node sends reads back. -/
theorem decodeEncodeBytes (m : Message) (h : m.WellFormed)
    (hb : ∀ b ∈ m.encodeModel, b < 256) : decode? m.encode = some m := by
  simp only [decode?, encode, Bytes.toNatListOfNatListOfLt m.encodeModel hb, decodeEncode m h]

end Message

end Libp2p.Discv5
