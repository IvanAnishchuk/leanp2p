import Bytes
import Libp2p.Eth2.Fork

/-!
# The chain from a testnet directory

A consensus network ships its config as `config.yaml` and its genesis
state as `genesis.ssz` (the layout that Lighthouse's `--testnet-dir`
and the ethpandaops genesis generator use). This module reads the
values `Chain` needs, and nothing else.

`config.yaml` is flat `KEY: value` lines, with one list:
`BLOB_SCHEDULE`, whose entries are `- EPOCH: n` and
`MAX_BLOBS_PER_BLOCK: m` lines. The reader takes exactly that form. A
`#` starts a comment, and a value may sit in single quotes. Any other
YAML is outside the form, and the reader ignores lines it does not
know.

`genesis.ssz` is the SSZ of a `BeaconState`. Its first two fields are
the same in every fork: `genesis_time` (`Uint64`, bytes 0 to 8) and
`genesis_validators_root` (`Root`, bytes 8 to 40). The reader takes the
40 bytes and needs no state type.

`SLOTS_PER_EPOCH` is a preset value. `PRESET_BASE` names the preset:
`mainnet` has 32 slots per epoch, and `minimal` has 8 (consensus-specs
`presets/*/phase0.yaml`).
-/

set_option autoImplicit false

namespace Libp2p.Eth2.Config

/-- One `KEY: value` line: the key and the value, unquoted and with the
comment cut. `none` for a line of another form. -/
def keyValue? (line : String) : Option (String × String) := do
  let body := (line.splitOn "#").headD ""
  let parts := body.splitOn ":"
  let key := (parts.headD "").trimAscii.toString
  if key.isEmpty || parts.length < 2 then none
  let value := (":".intercalate parts.tail).trimAscii.toString
  let value := if value.startsWith "'" && value.endsWith "'" && 2 ≤ value.length then
      ((value.drop 1).dropEnd 1).toString
    else value
  return (key, value)

/-- The flat values and the blob schedule of a `config.yaml`. -/
structure Values where
  flat : List (String × String) := []
  blobSchedule : List BlobEntry := []

/-- Read a `config.yaml`. Inside `BLOB_SCHEDULE`, `- EPOCH: n` opens an
entry, and `MAX_BLOBS_PER_BLOCK: m` completes it. A line with no
indentation ends the list. -/
def parse (text : String) : Values := Id.run do
  let mut out : Values := {}
  let mut inSchedule := false
  let mut epoch : Option Nat := none
  for raw in text.splitOn "\n" do
    let indented := raw.startsWith " " || raw.startsWith "-"
    let line := raw.trimAscii.toString
    if inSchedule && !indented && !line.isEmpty then inSchedule := false
    if inSchedule then
      let item := if line.startsWith "- " then (line.drop 2).toString else line
      if let some (k, v) := keyValue? item then
        if k == "EPOCH" then epoch := v.toNat?
        else if k == "MAX_BLOBS_PER_BLOCK" then
          if let (some e, some m) := (epoch, v.toNat?) then
            out := { out with blobSchedule := out.blobSchedule ++ [⟨e, m⟩] }
          epoch := none
      continue
    if let some (k, v) := keyValue? line then
      if k == "BLOB_SCHEDULE" && v.isEmpty then inSchedule := true
      else out := { out with flat := out.flat ++ [(k, v)] }
  return out

/-- The value of `key`. -/
def Values.get? (v : Values) (key : String) : Option String :=
  (v.flat.find? (·.1 == key)).map (·.2)

/-- A `0x`-prefixed 4-byte version. -/
def version? (s : String) : Option ByteArray := do
  let hex ← s.dropPrefix? "0x" |>.map (·.toString)
  let b ← Bytes.ofHex? hex.toLower
  if b.size == 4 then some b else none

/-- The forks after genesis, in the order of the spec. -/
def forkNames : List String := ["ALTAIR", "BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS", "HEZE"]

/-- The slots per epoch of a preset. -/
def slotsPerEpochOf (preset : String) : Option Nat :=
  if preset == "mainnet" then some 32 else if preset == "minimal" then some 8 else none

/-- The 40 bytes at the start of a `genesis.ssz`: the genesis time and
the genesis validators root. -/
def genesisOf? (state : ByteArray) : Option (Nat × ByteArray) :=
  if state.size < 40 then none
  else
    let time := (List.range 8).foldl (fun n i => n + (state.get! i).toNat * 256 ^ i) 0
    some (time, state.extract 8 40)

/-- The `Chain` of a config text and the bytes of a genesis state. -/
def chainOf (config : String) (genesis : ByteArray) : Except String Chain := do
  let v := parse config
  let need (k : String) : Except String String :=
    match v.get? k with
    | some x => .ok x
    | none => .error s!"config.yaml: no {k}"
  let nat (k : String) : Except String Nat := do
    match (← need k).toNat? with
    | some n => return n
    | none => throw s!"config.yaml: {k} is no number"
  let genesisVersion ← match version? (← need "GENESIS_FORK_VERSION") with
    | some b => pure b
    | none => throw "config.yaml: GENESIS_FORK_VERSION is no 4-byte version"
  let mut forks : List Fork := []
  let mut fuluEpoch : Option Nat := none
  for name in forkNames do
    match v.get? s!"{name}_FORK_EPOCH", v.get? s!"{name}_FORK_VERSION" with
    | some e, some ver =>
      let some epoch := e.toNat? | throw s!"config.yaml: {name}_FORK_EPOCH is no number"
      let some version := version? ver | throw s!"config.yaml: {name}_FORK_VERSION is no version"
      if epoch < Constants.farFutureEpoch then
        forks := forks ++ [⟨epoch, version⟩]
        if name == "FULU" then fuluEpoch := some epoch
    | _, _ => pure ()
  let preset := (v.get? "PRESET_BASE").getD "mainnet"
  let some slotsPerEpoch := slotsPerEpochOf preset
    | throw s!"config.yaml: PRESET_BASE {preset} is no known preset"
  let some (genesisTime, gvr) := genesisOf? genesis | throw "genesis.ssz: shorter than 40 bytes"
  return {
    genesisVersion, forks
    electraEpoch := (← nat "ELECTRA_FORK_EPOCH")
    maxBlobsElectra := (← nat "MAX_BLOBS_PER_BLOCK_ELECTRA")
    fuluEpoch
    blobSchedule := v.blobSchedule
    slotDurationMs := (← nat "SLOT_DURATION_MS")
    slotsPerEpoch
    genesisValidatorsRoot := gvr
    genesisTime }

end Libp2p.Eth2.Config
