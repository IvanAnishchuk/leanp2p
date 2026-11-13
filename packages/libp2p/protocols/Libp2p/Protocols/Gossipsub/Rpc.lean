import Proto
import Bytes
import Streams
import Libp2p.Protocols.Constants
import Libp2p.Protocols.Gossipsub.Types

/-!
# The gossipsub RPC

The wire messages of gossipsub v1.1 to v1.3, their `ProtoMessage`
instances, and the length-delimited frame step.

The field numbers come from the vendored specs: `vendor/specs/pubsub/README.md`
for `RPC`, `SubOpts`, and `Message`, `gossipsub-v1.0.md` for the control
envelope and its four messages, `gossipsub-v1.1.md` for the prune
peers and the backoff, `gossipsub-v1.2.md` for IDONTWANT, and
`extensions/extensions.proto` for the v1.3 Extensions message, the
`SubOpts` partial flags, and the partial-messages RPC.

Proto has no nested-message value. A nested message goes on the wire as a
`.bytes` entry that holds its encoding, and the decoder decodes that
encoding as the submessage.

The table is strict on singular fields: a present field with the wrong
wire type, a present string with invalid UTF-8, and a bool varint other
than 0 or 1 are `Pb.Error.badField`. The table is permissive on repeated
fields: an entry of another wire type is skipped. Unknown fields stay in
the wire view and drop out of the value on decode.

The validity premise of every table law is recursive. A child whose own
entries are invalid has an empty encoding, so a parent entry that holds
that empty encoding is valid. The parent law therefore states the
validity of its children as well.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub

/-! ## Shared readers

These readers are the house pattern of `Identify`, plus a strict bool
reader and an optional varint reader. Each one gates on `Pb.hasField`,
so a present field of another wire type is `badField` rather than a
miss. -/

/-- A present singular payload must be length-delimited. A miss means
absent. -/
private def bytesField? (num : Nat) (fs : Pb.Fields) : Except Pb.Error (Option (List Nat)) :=
  if Pb.hasField num fs then
    match Pb.getBytes? num fs with
    | some bs => .ok (some bs)
    | none => .error .badField
  else .ok none

/-- A present singular string must be length-delimited and valid UTF-8.
A miss means absent. -/
private def strField? (num : Nat) (fs : Pb.Fields) : Except Pb.Error (Option String) :=
  if Pb.hasField num fs then
    match (Pb.getBytes? num fs).bind (fun bs => Bytes.toString? (Bytes.ofNatList bs)) with
    | some s => .ok (some s)
    | none => .error .badField
  else .ok none

/-- A strict bool. A miss and varint 0 are `false`, varint 1 is `true`,
and every other present value is `badField`. -/
private def boolField? (num : Nat) (fs : Pb.Fields) : Except Pb.Error Bool :=
  if Pb.hasField num fs then
    match Pb.getVarint? num fs with
    | some 0 => .ok false
    | some 1 => .ok true
    | _ => .error .badField
  else .ok false

/-- An optional varint. A miss is `none`, and a present value of another
wire type is `badField`. -/
private def varintField? (num : Nat) (fs : Pb.Fields) : Except Pb.Error (Option Nat) :=
  if Pb.hasField num fs then
    match Pb.getVarint? num fs with
    | some n => .ok (some n)
    | none => .error .badField
  else .ok none

/-- A required string. A miss is `badField`. -/
private def requiredStr? (num : Nat) (fs : Pb.Fields) : Except Pb.Error String := do
  match ← strField? num fs with
  | some s => .ok s
  | none => .error .badField

/-- A singular nested field. A present field of another wire type is
`badField`, and a malformed nested payload keeps its wire error. -/
private def subField? {α : Type} (num : Nat) (fs : Pb.Fields)
    (ofFields? : Pb.Fields → Except Pb.Error α) :
    Except Pb.Error (Option α) :=
  if Pb.hasField num fs then
    match Pb.getSub? num fs with
    | .error e => .error e
    | .ok none => .error .badField
    | .ok (some nested) => do
        let a ← ofFields? nested
        .ok (some a)
  else .ok none

/-- Decode a list of encoded children in wire order. A child that fails
keeps its wire error. -/
private def decodeAll? {α : Type} [Pb.ProtoMessage α] :
    List (List Nat) → Except Pb.Error (List α)
  | [] => .ok []
  | bs :: rest => do
      let p ← Pb.decodeMessage? (α := α) bs
      let as ← decodeAll? rest
      .ok (p.1 :: as)

/-- The length-delimited payloads of one field number, in wire order. An
entry of another wire type is skipped. -/
private def allBytesOf (num : Nat) : List Pb.Entry → List (List Nat)
  | [] => []
  | (n, v) :: es =>
      (if n = num then
        match v with
        | .bytes bs => [bs]
        | _ => []
      else []) ++ allBytesOf num es

/-- The repeated nested reader. It takes every length-delimited payload
of the field number, in wire order, and decodes each one. -/
private def subAll? {α : Type} [Pb.ProtoMessage α] (num : Nat) (fs : Pb.Fields) :
    Except Pb.Error (List α) :=
  decodeAll? (allBytesOf num fs.entries)

/-- The wire view of a value, checked. Fail closed: a list whose entries
do not fit the wire model gives the empty field table. -/
private def fieldsOf? (es : List Pb.Entry) : Pb.Fields :=
  if h : ∀ e ∈ es, e.Valid then ⟨es, h⟩ else Pb.Fields.empty

/-! ## List lemmas -/

/-- A miss lookup through a segment that maps payloads to another field
number. -/
private theorem lookupMissMap {α : Type} (k n : Nat) (h : k ≠ n) (g : α → Pb.Value)
    (l : List α) :
    List.lookup k (l.map fun x => (n, g x)).reverse = none := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hb : (k == n) = false := by simpa using h
      simp [List.lookup_append, ih, List.lookup, hb]

/-- The payload reader splits over an append. -/
private theorem allBytesOfAppend (num : Nat) (a b : List Pb.Entry) :
    allBytesOf num (a ++ b) = allBytesOf num a ++ allBytesOf num b := by
  induction a with
  | nil => simp [allBytesOf]
  | cons e a ih =>
      obtain ⟨n, v⟩ := e
      simp [allBytesOf, ih, List.append_assoc]

/-- A segment of payload entries of one field number keeps exactly those
payloads, in order. -/
private theorem allBytesOfMapBytes {α : Type} (num k : Nat) (g : α → List Nat)
    (l : List α) :
    allBytesOf num (l.map fun x => (k, Pb.Value.bytes (g x))) =
      if k = num then l.map g else [] := by
  induction l with
  | nil => simp [allBytesOf]
  | cons x l ih =>
      simp only [List.map_cons, allBytesOf, ih]
      split <;> simp_all

/-- A segment of entries of another field number is empty. -/
private theorem allBytesOfMapOther {α : Type} (num k : Nat) (h : k ≠ num) (g : α → Pb.Value)
    (l : List α) :
    allBytesOf num (l.map fun x => (k, g x)) = [] := by
  induction l with
  | nil => simp [allBytesOf]
  | cons x l ih => simp [allBytesOf, h, ih]

/-- One entry of another field number is empty. -/
private theorem allBytesOfSingleOther {num k : Nat} (h : k ≠ num) (v : Pb.Value) :
    allBytesOf num [(k, v)] = [] := by
  simp [allBytesOf, h]

/-- The child round trips compose over a list of encoded children. -/
private theorem decodeAll?Encode {α : Type} [Pb.ProtoMessage α] (l : List α)
    (h : ∀ a ∈ l, Pb.decodeMessage? (α := α) (Pb.encodeMessage a) = .ok (a, [])) :
    decodeAll? (l.map (fun a => Pb.encodeMessage a)) = .ok l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha := h a (by simp)
      have hl : ∀ b ∈ l, Pb.decodeMessage? (α := α) (Pb.encodeMessage b) = .ok (b, []) :=
        fun b hb => h b (by simp [hb])
      simp [decodeAll?, ha, ih hl, Bind.bind, Except.bind]

/-- The singular reader finds a nested value encoded as the last entry.
`ofF` is the value's own table, and its law gives the value back. -/
private theorem subFieldLast {α : Type} [Pb.ProtoMessage α] (k : Nat) (es : List Pb.Entry)
    (x : α) (hv : ∀ e ∈ es ++ [(k, Pb.Value.bytes (Pb.encodeMessage x))], e.Valid)
    (ofF : Pb.Fields → Except Pb.Error α) (hof : ofF (Pb.ProtoMessage.toFields x) = .ok x) :
    subField? k ⟨es ++ [(k, Pb.Value.bytes (Pb.encodeMessage x))], hv⟩ ofF = .ok (some x) := by
  have hhas : Pb.hasField k ⟨es ++ [(k, Pb.Value.bytes (Pb.encodeMessage x))], hv⟩ = true := by
    simp [Pb.hasField]
  have hsub : Pb.getSub? k ⟨es ++ [(k, Pb.Value.bytes (Pb.encodeMessage x))], hv⟩ =
      .ok (some (Pb.ProtoMessage.toFields x)) := by
    simp only [Pb.getSub?, Pb.getBytes?, Pb.lookupLastAppend]
    simp [Pb.encodeMessage, Pb.decodeEncode, Bind.bind, Except.bind]
  simp [subField?, hhas, hsub, hof, Bind.bind, Except.bind]

/-- A last entry of another field number does not change the singular
reader's answer. -/
private theorem subFieldSkip {α : Type} (k n : Nat) (h : k ≠ n) (v : Pb.Value)
    (es : List Pb.Entry) (hv : ∀ e ∈ es ++ [(n, v)], e.Valid) (hv' : ∀ e ∈ es, e.Valid)
    (ofF : Pb.Fields → Except Pb.Error α) :
    subField? k ⟨es ++ [(n, v)], hv⟩ ofF = subField? k ⟨es, hv'⟩ ofF := by
  have hb : (k == n) = false := by simpa using h
  have hn : (n == k) = false := by simp [Ne.symm h]
  have hlast : Pb.lookupLast k (es ++ [(n, v)]) = Pb.lookupLast k es := by
    simp [Pb.lookupLast, List.reverse_append, List.lookup, hb]
  have hany : ((es ++ [(n, v)]).any fun e => e.fst == k) = (es.any fun e => e.fst == k) := by
    rw [List.any_append]
    simp [hn]
  simp only [subField?, Pb.hasField, Pb.getSub?, Pb.getBytes?, hlast, hany]
  rfl

/-- The singular reader answers `none` when no entry has the field number. -/
private theorem subFieldAbsent {α : Type} (k : Nat) (es : List Pb.Entry)
    (hv : ∀ e ∈ es, e.Valid) (h : ∀ e ∈ es, e.1 ≠ k) (ofF : Pb.Fields → Except Pb.Error α) :
    subField? k ⟨es, hv⟩ ofF = .ok none := by
  have hhas : Pb.hasField k ⟨es, hv⟩ = false := by
    simp only [Pb.hasField, List.any_eq_false, beq_iff_eq]
    exact h
  simp [subField?, hhas]

/-- A `MessageId` is its payload, so a list of ids survives the wrapper. -/
private theorem mapMessageIdMk (l : List MessageId) :
    (l.map (fun m => m.bytes)).map (fun bs => (⟨bs⟩ : MessageId)) = l := by
  induction l with
  | nil => rfl
  | cons m l ih => cases m; simp [ih]

/-- The same reading with the two maps composed. -/
private theorem mapMessageIdMkComp (l : List MessageId) :
    l.map (fun m => (⟨m.bytes⟩ : MessageId)) = l := by
  induction l with
  | nil => rfl
  | cons m l ih => cases m; simp [ih]

/-- The repeated payload reader for message ids. -/
private def messageIdsOf (num : Nat) (fs : Pb.Fields) : List MessageId :=
  (allBytesOf num fs.entries).map (fun bs => ⟨bs⟩)

/-! ## The `Message` codec

`Message` is the shared type of `Gossipsub.Types`. Its codec lives here,
in the parent namespace, so the type stays free of codec code. -/

namespace Message

/-- The wire view: one entry per present field, in the ascending order
1, 2, 3, 4, 5, 6. The topic is required and always present. -/
def entries (m : Message) : List Pb.Entry :=
  m.«from».toList.map (fun b => (1, Pb.Value.bytes b))
  ++ m.data.toList.map (fun b => (2, Pb.Value.bytes b))
  ++ m.seqno.toList.map (fun b => (3, Pb.Value.bytes b))
  ++ [(4, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString m.topic.name)))]
  ++ m.signature.toList.map (fun b => (5, Pb.Value.bytes b))
  ++ m.key.toList.map (fun b => (6, Pb.Value.bytes b))

/-- The wire validity of the entries. -/
def entriesValid (m : Message) : Prop := ∀ e ∈ m.entries, e.Valid

instance (m : Message) : Decidable (entriesValid m) := by
  unfold entriesValid
  infer_instance

/-- The validity of the message. It is the validity of its entries. -/
abbrev Valid (m : Message) : Prop := m.entriesValid

/-- Fail closed. A message whose entries do not fit the wire model emits
no entry; every theorem about the encode takes the validity as a
premise. -/
def toFields (m : Message) : Pb.Fields :=
  if h : m.entriesValid then ⟨m.entries, h⟩ else Pb.Fields.empty

/-- The field table: strict singular fields, permissive repeated fields.
The required topic reads first, so a missing topic fails before the
other fields run. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error Message := do
  let topic ← requiredStr? 4 fs
  let frm ← bytesField? 1 fs
  let data ← bytesField? 2 fs
  let seqno ← bytesField? 3 fs
  let signature ← bytesField? 5 fs
  let key ← bytesField? 6 fs
  .ok { «from» := frm, data, seqno, topic := ⟨topic⟩, signature, key }

instance : Pb.ProtoMessage Message where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law: a valid message round-trips through its own table. -/
theorem ofFieldsToFields (m : Message) (h : Valid m) :
    Pb.ProtoMessage.ofFields? (α := Message) (Pb.ProtoMessage.toFields m) = .ok m := by
  change ofFields? (toFields m) = .ok m
  have he : m.entriesValid := h
  rw [toFields, dite_eq_left he]
  obtain ⟨frm, data, seqno, topic, signature, key⟩ := m
  obtain ⟨name⟩ := topic
  cases frm <;> cases data <;> cases seqno <;> cases signature <;> cases key <;>
    simp [ofFields?, requiredStr?, bytesField?, strField?, entries, Pb.hasField, Pb.getBytes?,
      Pb.lookupLast, List.lookup_cons, Bind.bind, Except.bind, Bytes.ofNatListToNatList,
      Bytes.toString?OfString]

/-- An encode decodes back to the message. -/
theorem decodeEncode (m : Message) (h : Valid m) :
    Pb.decodeMessage? (Pb.encodeMessage m) = .ok (m, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields m h,
    Bind.bind, Except.bind]

/-- A `Message` without field 4 fails its table. -/
theorem ofFields?MissingTopic (fs : Pb.Fields) (h : ¬ Pb.hasField 4 fs) :
    ofFields? fs = .error .badField := by
  have hb : Pb.hasField 4 fs = false := by
    cases hm : Pb.hasField 4 fs <;> simp_all
  simp [ofFields?, requiredStr?, strField?, hb, Bind.bind, Except.bind]

end Message

/-! ## The control messages and the RPC envelope -/

namespace Rpc

/-- One subscription option. Field 1 is the bool, field 2 the topic.
Fields 3 and 4 are the partial-messages flags (`extensions.proto`,
`SubOpts`); a peer without the extension ignores them. -/
structure SubOpts where
  /-- True subscribes, false unsubscribes. -/
  subscribe : Bool            -- field 1, bool
  /-- The topic name. -/
  topicid : String            -- field 2, string
  /-- The sender wants partial messages on the topic. -/
  requestsPartial : Bool := false         -- field 3, bool
  /-- The sender can send partial messages on the topic. -/
  supportsSendingPartial : Bool := false  -- field 4, bool
  deriving DecidableEq, BEq, Repr

namespace SubOpts

/-- The wire view: field 1 as a varint, field 2 as the topic bytes, and
fields 3 and 4 only when true. A v1.1 subscription so keeps its bytes. -/
def entries (s : SubOpts) : List Pb.Entry :=
  [(1, .varint (if s.subscribe then 1 else 0)),
   (2, .bytes (Bytes.toNatList (Bytes.ofString s.topicid)))] ++
  (if s.requestsPartial then [(3, .varint 1)] else []) ++
  (if s.supportsSendingPartial then [(4, .varint 1)] else [])

def entriesValid (s : SubOpts) : Prop := ∀ e ∈ s.entries, e.Valid

instance (s : SubOpts) : Decidable (entriesValid s) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (s : SubOpts) : Prop := s.entriesValid

def toFields (s : SubOpts) : Pb.Fields :=
  fieldsOf? s.entries

/-- The field table. A miss reads as false or the empty string. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error SubOpts := do
  let subscribe ← boolField? 1 fs
  let topicid ← strField? 2 fs
  let requestsPartial ← boolField? 3 fs
  let supportsSendingPartial ← boolField? 4 fs
  .ok { subscribe, topicid := topicid.getD "", requestsPartial, supportsSendingPartial }

instance : Pb.ProtoMessage SubOpts where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (s : SubOpts) (h : Valid s) :
    Pb.ProtoMessage.ofFields? (α := SubOpts) (Pb.ProtoMessage.toFields s) = .ok s := by
  change ofFields? (toFields s) = .ok s
  have he : ∀ e ∈ s.entries, e.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨sub, tid, rp, ss⟩ := s
  cases sub <;> cases rp <;> cases ss <;>
    simp [ofFields?, boolField?, strField?, entries, Pb.hasField, Pb.getBytes?,
      Pb.getVarint?, Pb.lookupLast, List.lookup_cons, Bind.bind, Except.bind,
      Bytes.ofNatListToNatList, Bytes.toString?OfString]

/-- An encode decodes back to the value. -/
theorem decodeEncode (s : SubOpts) (h : Valid s) :
    Pb.decodeMessage? (Pb.encodeMessage s) = .ok (s, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields s h,
    Bind.bind, Except.bind]

end SubOpts

/-- A peer record of the v1.1 peer exchange. -/
structure PeerInfo where
  /-- The peer id bytes. -/
  peerId : Option (List Nat)            -- field 1, bytes
  /-- The signed peer record bytes. -/
  signedPeerRecord : Option (List Nat)  -- field 2, bytes
  deriving DecidableEq, BEq, Repr

namespace PeerInfo

def entries (p : PeerInfo) : List Pb.Entry :=
  p.peerId.toList.map (fun b => (1, Pb.Value.bytes b))
  ++ p.signedPeerRecord.toList.map (fun b => (2, Pb.Value.bytes b))

def entriesValid (p : PeerInfo) : Prop := ∀ e ∈ p.entries, e.Valid

instance (p : PeerInfo) : Decidable (entriesValid p) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (p : PeerInfo) : Prop := p.entriesValid

def toFields (p : PeerInfo) : Pb.Fields :=
  fieldsOf? p.entries

/-- The field table. A miss reads as an absent payload. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error PeerInfo := do
  let peerId ← bytesField? 1 fs
  let signedPeerRecord ← bytesField? 2 fs
  .ok { peerId, signedPeerRecord }

instance : Pb.ProtoMessage PeerInfo where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (p : PeerInfo) (h : Valid p) :
    Pb.ProtoMessage.ofFields? (α := PeerInfo) (Pb.ProtoMessage.toFields p) = .ok p := by
  change ofFields? (toFields p) = .ok p
  have he : ∀ e ∈ p.entries, e.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨pid, spr⟩ := p
  cases pid <;> cases spr <;>
    simp [ofFields?, bytesField?, entries, Pb.hasField, Pb.getBytes?, Pb.lookupLast,
      List.lookup_cons, Bind.bind, Except.bind]

/-- An encode decodes back to the value. -/
theorem decodeEncode (p : PeerInfo) (h : Valid p) :
    Pb.decodeMessage? (Pb.encodeMessage p) = .ok (p, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields p h,
    Bind.bind, Except.bind]

end PeerInfo

/-- An IHAVE control message. -/
structure ControlIHave where
  /-- The topic of the gossip. -/
  topicId : String            -- field 1, string
  /-- The ids of the messages on offer. -/
  messageIds : List MessageId -- field 2, repeated bytes
  deriving DecidableEq, BEq, Repr

namespace ControlIHave

def entries (i : ControlIHave) : List Pb.Entry :=
  [(1, .bytes (Bytes.toNatList (Bytes.ofString i.topicId)))]
  ++ i.messageIds.map (fun m => (2, Pb.Value.bytes m.bytes))

def entriesValid (i : ControlIHave) : Prop := ∀ e ∈ i.entries, e.Valid

instance (i : ControlIHave) : Decidable (entriesValid i) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (i : ControlIHave) : Prop := i.entriesValid

def toFields (i : ControlIHave) : Pb.Fields :=
  fieldsOf? i.entries

/-- The field table. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error ControlIHave := do
  let topicId ← strField? 1 fs
  .ok { topicId := topicId.getD "", messageIds := messageIdsOf 2 fs }

instance : Pb.ProtoMessage ControlIHave where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (i : ControlIHave) (h : Valid i) :
    Pb.ProtoMessage.ofFields? (α := ControlIHave) (Pb.ProtoMessage.toFields i) = .ok i := by
  change ofFields? (toFields i) = .ok i
  have he : ∀ e ∈ i.entries, e.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨tid, ids⟩ := i
  have hb : allBytesOf 2 ((1, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString tid))) ::
      ids.map (fun m => (2, Pb.Value.bytes m.bytes))) = ids.map (fun m => m.bytes) := by
    simp [allBytesOf, allBytesOfMapBytes]
  simp [ofFields?, strField?, entries, messageIdsOf, hb, mapMessageIdMkComp, Function.comp_def,
    Pb.hasField, Pb.getBytes?, Pb.lookupLast, List.lookup_append, Bind.bind, Except.bind,
    Bytes.ofNatListToNatList, Bytes.toString?OfString, lookupMissMap]

/-- An encode decodes back to the value. -/
theorem decodeEncode (i : ControlIHave) (h : Valid i) :
    Pb.decodeMessage? (Pb.encodeMessage i) = .ok (i, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields i h,
    Bind.bind, Except.bind]

end ControlIHave

/-- An IWANT control message. -/
structure ControlIWant where
  /-- The ids of the wanted messages. -/
  messageIds : List MessageId -- field 1, repeated bytes
  deriving DecidableEq, BEq, Repr

namespace ControlIWant

def entries (i : ControlIWant) : List Pb.Entry :=
  i.messageIds.map (fun m => (1, Pb.Value.bytes m.bytes))

def entriesValid (i : ControlIWant) : Prop := ∀ e ∈ i.entries, e.Valid

instance (i : ControlIWant) : Decidable (entriesValid i) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (i : ControlIWant) : Prop := i.entriesValid

def toFields (i : ControlIWant) : Pb.Fields :=
  fieldsOf? i.entries

/-- The field table. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error ControlIWant :=
  .ok { messageIds := messageIdsOf 1 fs }

instance : Pb.ProtoMessage ControlIWant where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (i : ControlIWant) (h : Valid i) :
    Pb.ProtoMessage.ofFields? (α := ControlIWant) (Pb.ProtoMessage.toFields i) = .ok i := by
  change ofFields? (toFields i) = .ok i
  have he : ∀ e ∈ i.entries, e.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨ids⟩ := i
  simp [ofFields?, entries, messageIdsOf, allBytesOfMapBytes, mapMessageIdMkComp, Function.comp_def]

/-- An encode decodes back to the value. -/
theorem decodeEncode (i : ControlIWant) (h : Valid i) :
    Pb.decodeMessage? (Pb.encodeMessage i) = .ok (i, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields i h,
    Bind.bind, Except.bind]

end ControlIWant

/-- A GRAFT control message. -/
structure ControlGraft where
  /-- The topic to graft. -/
  topicId : String            -- field 1, string
  deriving DecidableEq, BEq, Repr

namespace ControlGraft

def entries (g : ControlGraft) : List Pb.Entry :=
  [(1, .bytes (Bytes.toNatList (Bytes.ofString g.topicId)))]

def entriesValid (g : ControlGraft) : Prop := ∀ e ∈ g.entries, e.Valid

instance (g : ControlGraft) : Decidable (entriesValid g) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (g : ControlGraft) : Prop := g.entriesValid

def toFields (g : ControlGraft) : Pb.Fields :=
  fieldsOf? g.entries

/-- The field table. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error ControlGraft := do
  let topicId ← strField? 1 fs
  .ok { topicId := topicId.getD "" }

instance : Pb.ProtoMessage ControlGraft where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (g : ControlGraft) (h : Valid g) :
    Pb.ProtoMessage.ofFields? (α := ControlGraft) (Pb.ProtoMessage.toFields g) = .ok g := by
  change ofFields? (toFields g) = .ok g
  have he : ∀ e ∈ g.entries, e.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨tid⟩ := g
  simp [ofFields?, strField?, entries, Pb.hasField, Pb.getBytes?, Pb.lookupLast,
    Bind.bind, Except.bind, Bytes.ofNatListToNatList, Bytes.toString?OfString]

/-- An encode decodes back to the value. -/
theorem decodeEncode (g : ControlGraft) (h : Valid g) :
    Pb.decodeMessage? (Pb.encodeMessage g) = .ok (g, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields g h,
    Bind.bind, Except.bind]

end ControlGraft

/-- A PRUNE control message of gossipsub v1.1. -/
structure ControlPrune where
  /-- The topic to prune. -/
  topicId : String          -- field 1, string
  /-- The peers of the peer exchange. -/
  peers : List PeerInfo     -- field 2, repeated nested
  /-- The backoff in seconds. -/
  backoff : Option Nat      -- field 3, uint64 varint
  deriving DecidableEq, BEq, Repr

namespace ControlPrune

def entries (p : ControlPrune) : List Pb.Entry :=
  [(1, .bytes (Bytes.toNatList (Bytes.ofString p.topicId)))]
  ++ p.peers.map (fun q => (2, Pb.Value.bytes (Pb.encodeMessage q)))
  ++ p.backoff.toList.map (fun n => (3, Pb.Value.varint n))

def entriesValid (p : ControlPrune) : Prop := ∀ e ∈ p.entries, e.Valid

instance (p : ControlPrune) : Decidable (entriesValid p) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value: its entries, and every peer. -/
abbrev Valid (p : ControlPrune) : Prop :=
  p.entriesValid ∧ ∀ q ∈ p.peers, q.Valid

def toFields (p : ControlPrune) : Pb.Fields :=
  fieldsOf? p.entries

/-- The field table. The peers decode as nested messages. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error ControlPrune := do
  let topicId ← strField? 1 fs
  let peers ← subAll? (α := PeerInfo) 2 fs
  let backoff ← varintField? 3 fs
  .ok { topicId := topicId.getD "", peers, backoff }

instance : Pb.ProtoMessage ControlPrune where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (p : ControlPrune) (h : Valid p) :
    Pb.ProtoMessage.ofFields? (α := ControlPrune) (Pb.ProtoMessage.toFields p) = .ok p := by
  change ofFields? (toFields p) = .ok p
  obtain ⟨he, hp⟩ := h
  have he' : ∀ e ∈ p.entries, e.Valid := he
  rw [toFields, fieldsOf?, dite_eq_left he']
  obtain ⟨tid, peers, backoff⟩ := p
  have hdec := decodeAll?Encode peers (fun q hq => PeerInfo.decodeEncode q (hp q hq))
  cases backoff with
  | none =>
      have hb : allBytesOf 2 ((1, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString tid))) ::
          peers.map (fun q => (2, Pb.Value.bytes (Pb.encodeMessage q)))) =
          peers.map (fun q => Pb.encodeMessage q) := by
        simp [allBytesOf, allBytesOfMapBytes]
      simp [ofFields?, strField?, varintField?, subAll?, hdec, hb, entries, Pb.hasField,
        Pb.getBytes?, Pb.lookupLast, List.lookup_append, lookupMissMap, Bind.bind,
        Except.bind, Bytes.ofNatListToNatList, Bytes.toString?OfString]
  | some n =>
      have hb : allBytesOf 2 ((1, Pb.Value.bytes (Bytes.toNatList (Bytes.ofString tid))) ::
          (peers.map (fun q => (2, Pb.Value.bytes (Pb.encodeMessage q))) ++
            [(3, Pb.Value.varint n)])) =
          peers.map (fun q => Pb.encodeMessage q) := by
        simp [allBytesOf, allBytesOfAppend, allBytesOfMapBytes]
      simp [ofFields?, strField?, varintField?, subAll?, hdec, hb, entries, Pb.hasField,
        Pb.getBytes?, Pb.getVarint?, Pb.lookupLast, List.lookup_append, List.lookup_cons,
        List.reverse_append, lookupMissMap, Bind.bind, Except.bind,
        Bytes.ofNatListToNatList, Bytes.toString?OfString]

/-- An encode decodes back to the value. -/
theorem decodeEncode (p : ControlPrune) (h : Valid p) :
    Pb.decodeMessage? (Pb.encodeMessage p) = .ok (p, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields p h,
    Bind.bind, Except.bind]

end ControlPrune

/-- The v1.3 Extensions control message (`gossipsub-v1.3.md`, "The
Extensions Control Message"). A peer sends it once, in the first RPC on
its stream. Field 10 is the partial-messages extension; the decoder
drops unknown extensions, as the spec requires. -/
structure ControlExtensions where
  /-- The sender supports partial messages. -/
  partialMessages : Bool := false  -- field 10, bool
  deriving DecidableEq, BEq, Repr

namespace ControlExtensions

def entries (e : ControlExtensions) : List Pb.Entry :=
  if e.partialMessages then [(10, .varint 1)] else []

def entriesValid (e : ControlExtensions) : Prop := ∀ x ∈ e.entries, x.Valid

instance (e : ControlExtensions) : Decidable (entriesValid e) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (e : ControlExtensions) : Prop := e.entriesValid

def toFields (e : ControlExtensions) : Pb.Fields :=
  fieldsOf? e.entries

/-- The field table. A miss reads as false. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error ControlExtensions := do
  let partialMessages ← boolField? 10 fs
  .ok { partialMessages }

instance : Pb.ProtoMessage ControlExtensions where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (e : ControlExtensions) (h : Valid e) :
    Pb.ProtoMessage.ofFields? (α := ControlExtensions) (Pb.ProtoMessage.toFields e) = .ok e := by
  change ofFields? (toFields e) = .ok e
  have he : ∀ x ∈ e.entries, x.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨pm⟩ := e
  cases pm <;> simp [ofFields?, boolField?, entries, Pb.hasField, Pb.getVarint?, Pb.lookupLast,
    Bind.bind, Except.bind]

/-- An encode decodes back to the value. -/
theorem decodeEncode (e : ControlExtensions) (h : Valid e) :
    Pb.decodeMessage? (Pb.encodeMessage e) = .ok (e, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields e h,
    Bind.bind, Except.bind]

end ControlExtensions

/-- The partial-messages RPC (`extensions.proto`,
`PartialMessagesExtension`). The application defines `partialMessage`
and `partsMetadata`; the library forwards them (`partial-messages.md`,
"Application-Library Interface"). -/
structure PartialMessage where
  /-- The topic, as bytes. -/
  topicId : Option (List Nat) := none         -- field 1, bytes
  /-- The group: the full message the parts belong to. -/
  groupId : Option (List Nat) := none         -- field 2, bytes
  /-- One or more encoded parts. -/
  partialMessage : Option (List Nat) := none  -- field 3, bytes
  /-- The parts the sender has and wants. -/
  partsMetadata : Option (List Nat) := none   -- field 4, bytes
  deriving DecidableEq, BEq, Repr

namespace PartialMessage

def entries (p : PartialMessage) : List Pb.Entry :=
  p.topicId.toList.map (fun b => (1, Pb.Value.bytes b))
  ++ p.groupId.toList.map (fun b => (2, Pb.Value.bytes b))
  ++ p.partialMessage.toList.map (fun b => (3, Pb.Value.bytes b))
  ++ p.partsMetadata.toList.map (fun b => (4, Pb.Value.bytes b))

def entriesValid (p : PartialMessage) : Prop := ∀ e ∈ p.entries, e.Valid

instance (p : PartialMessage) : Decidable (entriesValid p) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value. -/
abbrev Valid (p : PartialMessage) : Prop := p.entriesValid

def toFields (p : PartialMessage) : Pb.Fields :=
  fieldsOf? p.entries

/-- The field table. A miss reads as an absent payload. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error PartialMessage := do
  let topicId ← bytesField? 1 fs
  let groupId ← bytesField? 2 fs
  let partialMessage ← bytesField? 3 fs
  let partsMetadata ← bytesField? 4 fs
  .ok { topicId, groupId, partialMessage, partsMetadata }

instance : Pb.ProtoMessage PartialMessage where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (p : PartialMessage) (h : Valid p) :
    Pb.ProtoMessage.ofFields? (α := PartialMessage) (Pb.ProtoMessage.toFields p) = .ok p := by
  change ofFields? (toFields p) = .ok p
  have he : ∀ e ∈ p.entries, e.Valid := h
  rw [toFields, fieldsOf?, dite_eq_left he]
  obtain ⟨t, g, m, md⟩ := p
  cases t <;> cases g <;> cases m <;> cases md <;>
    simp [ofFields?, bytesField?, entries, Pb.hasField, Pb.getBytes?, Pb.lookupLast,
      List.lookup_cons, Bind.bind, Except.bind]

/-- An encode decodes back to the value. -/
theorem decodeEncode (p : PartialMessage) (h : Valid p) :
    Pb.decodeMessage? (Pb.encodeMessage p) = .ok (p, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields p h,
    Bind.bind, Except.bind]

end PartialMessage

/-- The control envelope. Field 5 is gossipsub v1.2's `idontwant`
(`gossipsub-v1.2.md`, "Protobuf Extension"): `ControlIDontWant` is
`repeated bytes messageIDs = 1`, the wire shape of `ControlIWant`, so the
field reuses that type. -/
structure ControlMessage where
  /-- The IHAVE messages. -/
  ihave : List ControlIHave  -- field 1, repeated nested
  /-- The IWANT messages. -/
  iwant : List ControlIWant  -- field 2, repeated nested
  /-- The GRAFT messages. -/
  graft : List ControlGraft  -- field 3, repeated nested
  /-- The PRUNE messages. -/
  prune : List ControlPrune  -- field 4, repeated nested
  /-- The IDONTWANT messages (v1.2). -/
  idontwant : List ControlIWant := []  -- field 5, repeated nested
  /-- The Extensions message (v1.3). -/
  extensions : Option ControlExtensions := none  -- field 6, optional nested
  deriving DecidableEq, BEq, Repr

namespace ControlMessage

def entries (c : ControlMessage) : List Pb.Entry :=
  c.ihave.map (fun x => (1, Pb.Value.bytes (Pb.encodeMessage x)))
  ++ c.iwant.map (fun x => (2, Pb.Value.bytes (Pb.encodeMessage x)))
  ++ c.graft.map (fun x => (3, Pb.Value.bytes (Pb.encodeMessage x)))
  ++ c.prune.map (fun x => (4, Pb.Value.bytes (Pb.encodeMessage x)))
  ++ c.idontwant.map (fun x => (5, Pb.Value.bytes (Pb.encodeMessage x)))
  ++ c.extensions.toList.map (fun x => (6, Pb.Value.bytes (Pb.encodeMessage x)))

def entriesValid (c : ControlMessage) : Prop := ∀ e ∈ c.entries, e.Valid

instance (c : ControlMessage) : Decidable (entriesValid c) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value: its entries and every child. -/
abbrev Valid (c : ControlMessage) : Prop :=
  c.entriesValid ∧
  (∀ x ∈ c.ihave, x.Valid) ∧
  (∀ x ∈ c.iwant, x.Valid) ∧
  (∀ x ∈ c.graft, x.Valid) ∧
  (∀ x ∈ c.prune, x.Valid) ∧
  (∀ x ∈ c.idontwant, x.Valid) ∧
  (∀ x ∈ c.extensions.toList, x.Valid)

def toFields (c : ControlMessage) : Pb.Fields :=
  fieldsOf? c.entries

/-- The field table. Each of the five lists decodes as nested messages,
and the extensions as one singular nested message. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error ControlMessage := do
  let ihave ← subAll? (α := ControlIHave) 1 fs
  let iwant ← subAll? (α := ControlIWant) 2 fs
  let graft ← subAll? (α := ControlGraft) 3 fs
  let prune ← subAll? (α := ControlPrune) 4 fs
  let idontwant ← subAll? (α := ControlIWant) 5 fs
  let extensions ← subField? 6 fs ControlExtensions.ofFields?
  .ok { ihave, iwant, graft, prune, idontwant, extensions }

instance : Pb.ProtoMessage ControlMessage where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (c : ControlMessage) (h : Valid c) :
    Pb.ProtoMessage.ofFields? (α := ControlMessage) (Pb.ProtoMessage.toFields c) = .ok c := by
  change ofFields? (toFields c) = .ok c
  obtain ⟨he, hi, hw, hg, hr, hd, hx⟩ := h
  have he' : ∀ e ∈ c.entries, e.Valid := he
  rw [toFields, fieldsOf?, dite_eq_left he']
  obtain ⟨ih, iw, gr, pr, dw, ex⟩ := c
  have h1 := decodeAll?Encode ih (fun x hx => ControlIHave.decodeEncode x (hi x hx))
  have h2 := decodeAll?Encode iw (fun x hx => ControlIWant.decodeEncode x (hw x hx))
  have h3 := decodeAll?Encode gr (fun x hx => ControlGraft.decodeEncode x (hg x hx))
  have h4 := decodeAll?Encode pr (fun x hx => ControlPrune.decodeEncode x (hr x hx))
  have h5 := decodeAll?Encode dw (fun x hx => ControlIWant.decodeEncode x (hd x hx))
  cases ex with
  | none =>
      simp_all [ofFields?, subAll?, subField?, entries, allBytesOfAppend,
        allBytesOfMapBytes, Pb.hasField, Bind.bind, Except.bind]
  | some x =>
      have hof : ControlExtensions.ofFields? x.toFields = .ok x :=
        ControlExtensions.ofFieldsToFields x (hx x (by simp))
      -- The five lists, then the extensions as the last entry.
      have hent : entries ⟨ih, iw, gr, pr, dw, some x⟩ =
          (ih.map (fun y => (1, Pb.Value.bytes (Pb.encodeMessage y))) ++
            iw.map (fun y => (2, Pb.Value.bytes (Pb.encodeMessage y))) ++
            gr.map (fun y => (3, Pb.Value.bytes (Pb.encodeMessage y))) ++
            pr.map (fun y => (4, Pb.Value.bytes (Pb.encodeMessage y))) ++
            dw.map (fun y => (5, Pb.Value.bytes (Pb.encodeMessage y)))) ++
            [(6, Pb.Value.bytes (Pb.encodeMessage x))] := by
        simp [entries]
      have he₂ : ∀ e : Pb.Entry, e ∈ (ih.map (fun y => (1, Pb.Value.bytes (Pb.encodeMessage y))) ++
            iw.map (fun y => (2, Pb.Value.bytes (Pb.encodeMessage y))) ++
            gr.map (fun y => (3, Pb.Value.bytes (Pb.encodeMessage y))) ++
            pr.map (fun y => (4, Pb.Value.bytes (Pb.encodeMessage y))) ++
            dw.map (fun y => (5, Pb.Value.bytes (Pb.encodeMessage y)))) ++
            [(6, Pb.Value.bytes (Pb.encodeMessage x))] → e.Valid :=
        fun e hm => he' e (hent ▸ hm)
      simp only [hent]
      rw [show (⟨_, _⟩ : Pb.Fields) = ⟨_, he₂⟩ from rfl]
      simp only [ofFields?]
      rw [subFieldLast 6 _ x he₂ ControlExtensions.ofFields? hof]
      simp [subAll?, h1, h2, h3, h4, h5, allBytesOfAppend, allBytesOfMapBytes, allBytesOf,
        Bind.bind, Except.bind]

/-- An encode decodes back to the value. -/
theorem decodeEncode (c : ControlMessage) (h : Valid c) :
    Pb.decodeMessage? (Pb.encodeMessage c) = .ok (c, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields c h,
    Bind.bind, Except.bind]

end ControlMessage

/-- The control value of an optional control field. The `Option` shape
keeps the predicate decidable over a bounded value. -/
def controlValid : Option ControlMessage → Prop
  | none => True
  | some c => c.Valid

instance (o : Option ControlMessage) : Decidable (controlValid o) := by
  cases o with
  | none => exact isTrue trivial
  | some c =>
      rw [show controlValid (some c) = c.Valid from rfl]
      infer_instance

/-- The RPC envelope. -/
structure RPC where
  /-- The subscriptions. -/
  subscriptions : List SubOpts        -- field 1, repeated nested
  /-- The published messages. -/
  publish : List Message              -- field 2, repeated nested
  /-- The control envelope. -/
  control : Option ControlMessage     -- field 3, optional nested
  /-- The partial-messages extension (v1.3). -/
  partialRpc : Option PartialMessage := none  -- field 10, optional nested
  deriving DecidableEq, BEq, Repr

namespace RPC

/-- The wire view, in field-number order, as go and rust write it. -/
def entries (r : RPC) : List Pb.Entry :=
  r.subscriptions.map (fun s => (1, Pb.Value.bytes (Pb.encodeMessage s)))
  ++ r.publish.map (fun m => (2, Pb.Value.bytes (Pb.encodeMessage m)))
  ++ r.control.toList.map (fun c => (3, Pb.Value.bytes (Pb.encodeMessage c)))
  ++ r.partialRpc.toList.map (fun p => (10, Pb.Value.bytes (Pb.encodeMessage p)))

def entriesValid (r : RPC) : Prop := ∀ e ∈ r.entries, e.Valid

instance (r : RPC) : Decidable (entriesValid r) := by
  unfold entriesValid
  infer_instance

/-- The validity of the value: its entries, every child, and the control
value. -/
abbrev Valid (r : RPC) : Prop :=
  r.entriesValid ∧
  (∀ s ∈ r.subscriptions, s.Valid) ∧
  (∀ m ∈ r.publish, m.Valid) ∧
  controlValid r.control ∧
  (∀ p ∈ r.partialRpc.toList, p.Valid)

instance (r : RPC) : Decidable (Valid r) := by
  unfold Valid
  cases r.control with
  | none =>
      rw [show controlValid none = True from rfl]
      infer_instance
  | some c =>
      rw [show controlValid (some c) = c.Valid from rfl]
      infer_instance

def toFields (r : RPC) : Pb.Fields :=
  fieldsOf? r.entries

/-- The field table. The subscriptions and the messages decode as nested
messages, and the control and partial fields as singular nested
messages. -/
def ofFields? (fs : Pb.Fields) : Except Pb.Error RPC := do
  let subscriptions ← subAll? (α := SubOpts) 1 fs
  let publish ← subAll? (α := Message) 2 fs
  let control ← subField? 3 fs ControlMessage.ofFields?
  let partialRpc ← subField? 10 fs PartialMessage.ofFields?
  .ok { subscriptions, publish, control, partialRpc }

instance : Pb.ProtoMessage RPC where
  toFields := toFields
  ofFields? := ofFields?

/-- The table law. -/
theorem ofFieldsToFields (r : RPC) (h : Valid r) :
    Pb.ProtoMessage.ofFields? (α := RPC) (Pb.ProtoMessage.toFields r) = .ok r := by
  change ofFields? (toFields r) = .ok r
  obtain ⟨he, hsub, hpub, hctl, hpar⟩ := h
  have he' : ∀ e ∈ r.entries, e.Valid := he
  rw [toFields, fieldsOf?, dite_eq_left he']
  obtain ⟨subs, pubs, ctl, par⟩ := r
  have h1 := decodeAll?Encode subs (fun s hmem => SubOpts.decodeEncode s (hsub s hmem))
  have h2 := decodeAll?Encode pubs (fun m hmem => Message.decodeEncode m (hpub m hmem))
  -- The two list segments every case starts with.
  let pre : List Pb.Entry :=
    subs.map (fun s => (1, Pb.Value.bytes (Pb.encodeMessage s))) ++
      pubs.map (fun m => (2, Pb.Value.bytes (Pb.encodeMessage m)))
  have hofp : ∀ p, p ∈ par.toList → PartialMessage.ofFields? p.toFields = .ok p :=
    fun p hp => PartialMessage.ofFieldsToFields p (hpar p hp)
  cases ctl with
  | none =>
      cases par with
      | none =>
          simp_all [ofFields?, subAll?, subField?, entries, allBytesOfAppend,
            allBytesOfMapBytes, Pb.hasField, Bind.bind, Except.bind]
      | some p =>
          have hent : entries ⟨subs, pubs, none, some p⟩ =
              pre ++ [(10, Pb.Value.bytes (Pb.encodeMessage p))] := by
            simp [entries, pre]
          have he₂ : ∀ e ∈ pre ++ [(10, Pb.Value.bytes (Pb.encodeMessage p))], e.Valid :=
            fun e hm => he' e (hent ▸ hm)
          simp only [hent]
          rw [show (⟨_, _⟩ : Pb.Fields) = ⟨_, he₂⟩ from rfl]
          simp only [ofFields?]
          rw [subFieldLast 10 _ p he₂ PartialMessage.ofFields? (hofp p (by simp))]
          simp [pre, subAll?, subField?, h1, h2, Pb.hasField, allBytesOfAppend,
            allBytesOfMapBytes, allBytesOf, Bind.bind, Except.bind]
  | some c =>
      have h4 : ControlMessage.ofFields? c.toFields = .ok c :=
        ControlMessage.ofFieldsToFields c hctl
      cases par with
      | none =>
          have hent : entries ⟨subs, pubs, some c, none⟩ =
              pre ++ [(3, Pb.Value.bytes (Pb.encodeMessage c))] := by
            simp [entries, pre]
          have he₂ : ∀ e ∈ pre ++ [(3, Pb.Value.bytes (Pb.encodeMessage c))], e.Valid :=
            fun e hm => he' e (hent ▸ hm)
          simp only [hent]
          rw [show (⟨_, _⟩ : Pb.Fields) = ⟨_, he₂⟩ from rfl]
          simp only [ofFields?]
          rw [subFieldLast 3 _ c he₂ ControlMessage.ofFields? h4]
          simp [pre, subAll?, subField?, h1, h2, Pb.hasField, allBytesOfAppend,
            allBytesOfMapBytes, allBytesOf, Bind.bind, Except.bind]
      | some p =>
          -- Field 3, then field 10 last: the control reader skips the
          -- partial entry, and the partial reader finds it.
          have hent : entries ⟨subs, pubs, some c, some p⟩ =
              (pre ++ [(3, Pb.Value.bytes (Pb.encodeMessage c))]) ++
                [(10, Pb.Value.bytes (Pb.encodeMessage p))] := by
            simp [entries, pre]
          have he₂ : ∀ e ∈ (pre ++ [(3, Pb.Value.bytes (Pb.encodeMessage c))]) ++
              [(10, Pb.Value.bytes (Pb.encodeMessage p))], e.Valid :=
            fun e hm => he' e (hent ▸ hm)
          have hv' : ∀ e ∈ pre ++ [(3, Pb.Value.bytes (Pb.encodeMessage c))], e.Valid :=
            fun e hm => he₂ e (List.mem_append_left _ hm)
          simp only [hent]
          rw [show (⟨_, _⟩ : Pb.Fields) = ⟨_, he₂⟩ from rfl]
          simp only [ofFields?]
          rw [subFieldSkip 3 10 (by decide) _ _ he₂ hv' ControlMessage.ofFields?,
            subFieldLast 3 _ c hv' ControlMessage.ofFields? h4,
            subFieldLast 10 _ p he₂ PartialMessage.ofFields? (hofp p (by simp))]
          simp [pre, subAll?, h1, h2, allBytesOfAppend, allBytesOfMapBytes, allBytesOf,
            Bind.bind, Except.bind]

/-- An encode decodes back to the value. -/
theorem decodeEncode (r : RPC) (h : Valid r) :
    Pb.decodeMessage? (Pb.encodeMessage r) = .ok (r, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, ofFieldsToFields r h,
    Bind.bind, Except.bind]

/-- Equal encodings imply equal messages. Without the premise the
statement is false: two different invalid messages both encode to the
empty list. -/
theorem encodeInjective (a b : RPC) (ha : Valid a) (hb : Valid b)
    (h : Pb.encodeMessage a = Pb.encodeMessage b) : a = b := by
  have hf : toFields a = toFields b := Pb.encodeInjective h
  have h3 : Pb.ProtoMessage.ofFields? (α := RPC) (Pb.ProtoMessage.toFields a) =
      Pb.ProtoMessage.ofFields? (α := RPC) (Pb.ProtoMessage.toFields b) :=
    congrArg (fun fs => Pb.ProtoMessage.ofFields? (α := RPC) fs) hf
  rw [ofFieldsToFields a ha, ofFieldsToFields b hb] at h3
  exact Except.ok.inj h3

end RPC

/-- The repeated fields keep their order through the round trip. -/
theorem roundTripLists (r : RPC) (h : RPC.Valid r) :
    ∃ r' : RPC, Pb.decodeMessage? (Pb.encodeMessage r) = .ok (r', []) ∧
      r'.subscriptions = r.subscriptions ∧ r'.publish = r.publish :=
  ⟨r, RPC.decodeEncode r h, rfl, rfl⟩

/-- The four control lists keep their order through the round trip. -/
theorem roundTripControlLists (c : ControlMessage) (h : ControlMessage.Valid c) :
    ∃ c' : ControlMessage, Pb.decodeMessage? (Pb.encodeMessage c) = .ok (c', []) ∧
      c'.ihave = c.ihave ∧ c'.iwant = c.iwant ∧ c'.graft = c.graft ∧ c'.prune = c.prune :=
  ⟨c, ControlMessage.decodeEncode c h, rfl, rfl, rfl, rfl⟩

/-- The message ids of an IHAVE keep their order through the round
trip. -/
theorem roundTripMessageIdsIHave (i : ControlIHave) (h : ControlIHave.Valid i) :
    ∃ i' : ControlIHave, Pb.decodeMessage? (Pb.encodeMessage i) = .ok (i', []) ∧
      i'.messageIds = i.messageIds :=
  ⟨i, ControlIHave.decodeEncode i h, rfl⟩

/-- The message ids of an IWANT keep their order through the round
trip. -/
theorem roundTripMessageIdsIWant (i : ControlIWant) (h : ControlIWant.Valid i) :
    ∃ i' : ControlIWant, Pb.decodeMessage? (Pb.encodeMessage i) = .ok (i', []) ∧
      i'.messageIds = i.messageIds :=
  ⟨i, ControlIWant.decodeEncode i h, rfl⟩

/-- The peers of a PRUNE keep their order through the round trip. -/
theorem roundTripPeers (p : ControlPrune) (h : ControlPrune.Valid p) :
    ∃ p' : ControlPrune, Pb.decodeMessage? (Pb.encodeMessage p) = .ok (p', []) ∧
      p'.peers = p.peers :=
  ⟨p, ControlPrune.decodeEncode p h, rfl⟩

/-! ## The length-delimited frame step

One RPC frame is a uvarint length and the message bytes, under
`Constants.rpcCap`. The decoder checks the cap before it takes the body,
as `Streams.Framing.Frame.decode?` does. A zero-length frame is a legal
empty RPC; unlike `Identify`, this protocol has no empty-frame rule. -/

/-- One length-delimited RPC frame under the cap. `none` when the
payload is over the cap. A node passes its own cap
(`Node.Config.maxRpcSize`). -/
def encodeFrame? (r : RPC) (cap : Nat := Constants.rpcCap) : Option (List Nat) :=
  let payload := Pb.encodeMessage r
  if payload.length ≤ cap then
    some (Streams.Framing.encodeLength .uvarint payload.length ++ payload)
  else none

/-- One frame from the front of the buffer.

* `.ok (some (payload, rest))`: one whole frame, and the bytes after it.
* `.ok none`: the buffer ends inside the prefix or inside the payload.
* `.error (.framing .malformed)`: a bad prefix, or a length over the cap.

The cap check runs before the payload is taken. -/
def decodeFrame? (bytes : List Nat) :
    Except Pb.Error (Option (List Nat × List Nat)) :=
  match Streams.Framing.Frame.decode? .uvarint Constants.rpcCap bytes with
  | .error .malformed => .error (.framing .malformed)
  | .error .truncated => .ok none
  | .ok (frame, rest) => .ok (some (frame.payload, rest))

/-- The frame step reads a whole frame back from its encoding, with any
rest after it. -/
theorem decodeFrame?Encode (f : Streams.Framing.Frame .uvarint Constants.rpcCap)
    (rest : List Nat) :
    decodeFrame? (Streams.Framing.Frame.encode f ++ rest) =
      .ok (some (f.payload, rest)) := by
  unfold decodeFrame?
  rw [Streams.Framing.Frame.decode?EncodeAppend f rest]

/-- A prefix with a length over the cap is malformed before the body. -/
theorem decodeFrame?OverCap (len : Nat) (rest : List Nat)
    (hlen : len ≤ Streams.Framing.Prefix.maxLen .uvarint)
    (hcap : Constants.rpcCap < len) :
    decodeFrame? (Streams.Framing.encodeLength .uvarint len ++ rest) =
      .error (.framing .malformed) := by
  unfold decodeFrame?
  rw [Streams.Framing.Frame.decode?OverCap (p := .uvarint)
    (cap := Constants.rpcCap)
    (l := Streams.Framing.encodeLength .uvarint len ++ rest)
    (rest := rest) (len := len)
    (Streams.Framing.decodeLength?EncodeLength .uvarint len rest hlen) hcap]

/-- A prefix cut short needs more bytes. -/
theorem decodeFrame?Truncated (bytes : List Nat)
    (h : Streams.Framing.Frame.decode? .uvarint Constants.rpcCap bytes =
      .error .truncated) :
    decodeFrame? bytes = .ok none := by
  unfold decodeFrame?
  rw [h]

/-- The rpc cap fits the uvarint prefix. -/
theorem rpcCapLeMaxLen :
    Constants.rpcCap ≤ Streams.Framing.Prefix.maxLen .uvarint := by
  decide

/-- The frame steps are inverse for a valid RPC under the cap. -/
theorem decodeFrame?EncodeRpc (r : RPC) (rest : List Nat)
    (_h : ∀ e ∈ r.entries, e.Valid)
    (hcap : (Pb.encodeMessage r).length ≤ Constants.rpcCap) :
    decodeFrame? (Streams.Framing.encodeLength .uvarint (Pb.encodeMessage r).length
      ++ Pb.encodeMessage r ++ rest) = .ok (some (Pb.encodeMessage r, rest)) := by
  have hbytes : ∀ b ∈ Pb.encodeMessage r, b < 256 :=
    Pb.encodeFieldsBytes (Pb.ProtoMessage.toFields r)
  have hmax : (Pb.encodeMessage r).length ≤
      Streams.Framing.Prefix.maxLen .uvarint :=
    Nat.le_trans hcap rpcCapLeMaxLen
  let f : Streams.Framing.Frame .uvarint Constants.rpcCap :=
    ⟨Pb.encodeMessage r, hbytes, ⟨hcap, hmax⟩⟩
  simpa [Streams.Framing.Frame.encode] using decodeFrame?Encode f rest

end Rpc

end Libp2p.Protocols.Gossipsub
