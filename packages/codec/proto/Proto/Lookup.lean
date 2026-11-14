import Proto.Core

/-!
# Field lookups

The wire list retains all entries. Singular accessors inspect its last
occurrence of the requested number. Repeated accessors keep wire order.
Nested parsing reports malformed payloads through the wire error type.

The strict readers (`bytesField?`, `strField?`, `varintField?`) are the
one home of a rule that every message table of the stack follows:
- A present singular field of the wrong wire type gives `badField`.
- A string that is not UTF-8 gives `badField`.
- A missing field gives `none`. `hasField` tells a missing field from a
  present one.
-/

set_option autoImplicit false

namespace Pb

/-- Reversing turns the last wire occurrence into the first lookup hit. -/
def lookupLast (num : Nat) (entries : List Entry) : Option Value :=
  entries.reverse.lookup num

/-- A singular integer is available when the last occurrence has wire type zero. -/
def getVarint? (num : Nat) (fs : Fields) : Option Nat :=
  (lookupLast num fs.entries).bind fun
    | .varint n => some n
    | _ => none

/-- A singular payload is available when the last occurrence is length-delimited. -/
def getBytes? (num : Nat) (fs : Fields) : Option (List Nat) :=
  (lookupLast num fs.entries).bind fun
    | .bytes bs => some bs
    | _ => none

/-- A missing payload is a lookup miss; an invalid nested message is a wire error. -/
def getSub? (num : Nat) (fs : Fields) : Except Error (Option Fields) := do
  match getBytes? num fs with
  | none => .ok none
  | some bs =>
      let (nested, _) ← decodeFields? bs
      .ok (some nested)

/-- A valid UTF-8 reading of the last payload, when available. -/
def getStr? (num : Nat) (fs : Fields) : Option String := do
  let bs ← getBytes? num fs
  Bytes.toString? (Bytes.ofNatList bs)

/-- All integer occurrences keep their order and ignore other wire types. -/
def getAllVarints (num : Nat) (fs : Fields) : List Nat :=
  fs.entries.filterMap fun (n, v) =>
    if n = num then match v with | .varint x => some x | _ => none else none

/-- All length-delimited occurrences, including empty payloads. -/
def getAllBytes (num : Nat) (fs : Fields) : List (List Nat) :=
  fs.entries.filterMap fun (n, v) =>
    if n = num then match v with | .bytes bs => some bs | _ => none else none

/-- Repeated string readings retain the order of the valid UTF-8 payloads. -/
def getAllStrs (num : Nat) (fs : Fields) : List String :=
  (getAllBytes num fs).filterMap fun bs =>
    Bytes.toString? (Bytes.ofNatList bs)

/-- Presence does not depend on the entry's wire type or payload length. -/
def hasField (num : Nat) (fs : Fields) : Bool :=
  fs.entries.any fun e => e.1 == num

/-- A strict singular payload. A present field that is not
length-delimited gives `badField`, and a missing field gives `none`. -/
def bytesField? (num : Nat) (fs : Fields) : Except Error (Option (List Nat)) :=
  if hasField num fs then
    match getBytes? num fs with
    | some bs => .ok (some bs)
    | none => .error .badField
  else .ok none

/-- A strict singular string. A present field that is not
length-delimited, or not valid UTF-8, gives `badField`. A missing field
gives `none`. -/
def strField? (num : Nat) (fs : Fields) : Except Error (Option String) :=
  if hasField num fs then
    match (getBytes? num fs).bind (fun bs => Bytes.toString? (Bytes.ofNatList bs)) with
    | some s => .ok (some s)
    | none => .error .badField
  else .ok none

/-- A strict singular integer. A present field that is not a varint
gives `badField`, and a missing field gives `none`. -/
def varintField? (num : Nat) (fs : Fields) : Except Error (Option Nat) :=
  if hasField num fs then
    match getVarint? num fs with
    | some n => .ok (some n)
    | none => .error .badField
  else .ok none

/-- Appending an occurrence makes it the singular lookup result. -/
theorem lookupLastAppend (num : Nat) (v : Value) (entries : List Entry) :
    lookupLast num (entries ++ [(num, v)]) = some v := by
  simp [lookupLast, List.reverse_append]

end Pb
