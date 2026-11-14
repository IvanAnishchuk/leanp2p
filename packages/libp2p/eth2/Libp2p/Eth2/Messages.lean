import Libp2p.Protocols.ReqResp.Payload
import Libp2p.Eth2.Fork

/-!
# The req/resp methods and their small messages

The methods a Fulu node speaks, as `ReqResp.Method` values, with their
protocol ids, their size bounds, their `ForkDigest`-context, and their
chunk counts. The framing package frames the bytes. This module says
how many.

The small messages have fixed SSZ forms, so this module encodes them:

| message | SSZ | bytes |
|---|---|---|
| `Status` v2 (fulu) | `fork_digest`, `finalized_root`, `finalized_epoch`, `head_root`, `head_slot`, `earliest_available_slot` | 4 + 32 + 8 + 32 + 8 + 8 = 92 |
| `MetaData` v3 (fulu) | `seq_number`, `attnets` (8), `syncnets` (1), `custody_group_count` | 8 + 8 + 1 + 8 = 25 |
| `MetaData` v2 (altair) | the first three fields | 17 |
| `Ping`, `Goodbye` | one `Uint64`, "encoded as a single SSZ-field" | 8 |

Blocks and columns stay opaque bytes: their SSZ types belong to the
client (`protocols/docs/ARCHITECTURE.md`, contract 7). Their bounds
are Lighthouse's (`rpc/protocol.rs`, `rpc_block_limits_by_fork` and
`rpc_data_column_limits`), cut at `MAX_PAYLOAD_SIZE`:

* the least `SignedBeaconBlock` is 404 bytes: the 100 fixed bytes of
  the signed block, the 84 of the block, and the 220 of a phase0 body;
* the least `DataColumnSidecar` is 356 bytes: an index, three list
  offsets, a 208-byte signed header, and a 128-byte inclusion proof.

The request bounds follow the request types:

* `BeaconBlocksByRange` v2: `start_slot`, `count`, `step`, 24 bytes.
* `BeaconBlocksByRoot` v2: a list of up to `MAX_REQUEST_BLOCKS_DENEB`
  roots.
* `DataColumnSidecarsByRange` v1: `start_slot`, `count`, and an offset,
  then up to `NUMBER_OF_COLUMNS` indices of 8 bytes.
* `DataColumnSidecarsByRoot` v1: up to `MAX_REQUEST_BLOCKS_DENEB`
  identifiers. Each one is an offset, a root, an offset, and up to
  `NUMBER_OF_COLUMNS` indices.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Protocols.ReqResp (Method Bounds)

/-- The little-endian `Uint64` at byte `i`. -/
def le64At (b : ByteArray) (i : Nat) : Nat :=
  (List.range 8).foldl (fun n k => n + (b.get! (i + k)).toNat * 256 ^ k) 0

/-! ## Status v2 -/

/-- `Status` v2 (fulu `p2p-interface.md`, "Status v2"). -/
structure Status where
  forkDigest : ByteArray
  finalizedRoot : ByteArray
  finalizedEpoch : Nat
  headRoot : ByteArray
  headSlot : Nat
  earliestAvailableSlot : Nat

/-- The SSZ width of `Status` v2. -/
def statusLen : Nat := 92

/-- The SSZ of a `Status`. The digest and the roots must have 4 and 32
bytes. -/
def Status.encode (s : Status) : ByteArray :=
  s.forkDigest ++ s.finalizedRoot ++ Chain.le64 s.finalizedEpoch ++ s.headRoot ++
    Chain.le64 s.headSlot ++ Chain.le64 s.earliestAvailableSlot

/-- A `Status` from its SSZ. -/
def Status.decode? (b : ByteArray) : Option Status :=
  if b.size != statusLen then none
  else some {
    forkDigest := b.extract 0 4
    finalizedRoot := b.extract 4 36
    finalizedEpoch := le64At b 36
    headRoot := b.extract 44 76
    headSlot := le64At b 76
    earliestAvailableSlot := le64At b 84 }

/-! ## MetaData v3 and v2 -/

/-- `MetaData` (fulu `p2p-interface.md`, "MetaData"). -/
structure MetaData where
  seqNumber : Nat
  attnets : ByteArray
  syncnets : ByteArray
  custodyGroupCount : Nat

/-- The SSZ of `MetaData` v3. -/
def MetaData.encodeV3 (m : MetaData) : ByteArray :=
  Chain.le64 m.seqNumber ++ m.attnets ++ m.syncnets ++ Chain.le64 m.custodyGroupCount

/-- The SSZ of `MetaData` v2: v3 without the custody group count. -/
def MetaData.encodeV2 (m : MetaData) : ByteArray :=
  Chain.le64 m.seqNumber ++ m.attnets ++ m.syncnets

/-- A `MetaData` from its v3 SSZ. -/
def MetaData.decodeV3? (b : ByteArray) : Option MetaData :=
  if b.size != 25 then none
  else some { seqNumber := le64At b 0, attnets := b.extract 8 16, syncnets := b.extract 16 17,
              custodyGroupCount := le64At b 17 }

/-! ## The methods -/

/-- A fixed size. -/
def exactly (n : Nat) : Bounds := ⟨n, n⟩

/-- `/eth2/beacon_chain/req/status/2/ssz_snappy`. -/
def statusMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "status" 2
    request := some (exactly statusLen), response := exactly statusLen
    contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/goodbye/1/ssz_snappy`. The responder sends
no chunk, as Lighthouse does ("Goodbye request has no response"), so
the requester reads at most one. -/
def goodbyeMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "goodbye" 1
    request := some (exactly 8), response := exactly 8, contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/ping/1/ssz_snappy`. -/
def pingMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "ping" 1
    request := some (exactly 8), response := exactly 8, contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/metadata/3/ssz_snappy`: "No Request
Content". -/
def metadataV3Method : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "metadata" 3
    request := none, response := exactly 25, contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/metadata/2/ssz_snappy`. -/
def metadataV2Method : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "metadata" 2
    request := none, response := exactly 17, contextLen := 0, maxChunks := 1 }

/-- The bounds of a block chunk. -/
def blockBounds : Bounds := ⟨404, Libp2p.Protocols.Constants.maxPayloadSize⟩

/-- The bounds of a column chunk. -/
def columnBounds : Bounds := ⟨356, Libp2p.Protocols.Constants.maxPayloadSize⟩

/-- `/eth2/beacon_chain/req/beacon_blocks_by_range/2/ssz_snappy`. -/
def blocksByRangeMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "beacon_blocks_by_range" 2
    request := some (exactly 24), response := blockBounds
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestBlocksDeneb }

/-- `/eth2/beacon_chain/req/beacon_blocks_by_root/2/ssz_snappy`. -/
def blocksByRootMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "beacon_blocks_by_root" 2
    request := some ⟨0, 32 * Constants.maxRequestBlocksDeneb⟩, response := blockBounds
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestBlocksDeneb }

/-- `/eth2/beacon_chain/req/data_column_sidecars_by_range/1/ssz_snappy`. -/
def columnsByRangeMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "data_column_sidecars_by_range" 1
    request := some ⟨20, 20 + 8 * Constants.numberOfColumns⟩, response := columnBounds
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestDataColumnSidecars }

/-- `/eth2/beacon_chain/req/data_column_sidecars_by_root/1/ssz_snappy`. -/
def columnsByRootMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "data_column_sidecars_by_root" 1
    request := some ⟨0, Constants.maxRequestBlocksDeneb * (4 + 32 + 4 + 8 * Constants.numberOfColumns)⟩
    response := columnBounds
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestDataColumnSidecars }

/-- The SSZ of a `BeaconBlocksByRange` request: `step` is 1. -/
def blocksByRangeRequest (startSlot count : Nat) : ByteArray :=
  Chain.le64 startSlot ++ Chain.le64 count ++ Chain.le64 1

/-- The SSZ of a `BeaconBlocksByRoot` request: the roots, back to back. -/
def blocksByRootRequest (roots : List ByteArray) : ByteArray :=
  roots.foldl (· ++ ·) ByteArray.empty

/-- The SSZ of a `DataColumnSidecarsByRange` request: the fixed part,
then the offset 20 of the list, then the indices. -/
def columnsByRangeRequest (startSlot count : Nat) (columns : List Nat) : ByteArray :=
  columns.foldl (fun b c => b ++ Chain.le64 c)
    (Chain.le64 startSlot ++ Chain.le64 count ++ (Chain.le64 20).extract 0 4)

/-- The SSZ of a `DataColumnSidecarsByRoot` request: one identifier per
root, each with the same columns. A list of variable-size elements
starts with an offset per element. -/
def columnsByRootRequest (roots : List ByteArray) (columns : List Nat) : ByteArray :=
  let item := fun (r : ByteArray) =>
    columns.foldl (fun b c => b ++ Chain.le64 c) (r ++ (Chain.le64 36).extract 0 4)
  let items := roots.map item
  let offsets := (items.foldl (fun (acc : List Nat × Nat) i => (acc.1 ++ [acc.2], acc.2 + i.size))
    ([], 4 * items.length)).1
  let header := offsets.foldl (fun b o => b ++ (Chain.le64 o).extract 0 4) ByteArray.empty
  items.foldl (· ++ ·) header

#guard (Status.decode? (Status.encode
  ⟨⟨#[1, 2, 3, 4]⟩, ⟨Array.replicate 32 7⟩, 5, ⟨Array.replicate 32 9⟩, 170, 3⟩)).map
    (fun s => (s.finalizedEpoch, s.headSlot, s.earliestAvailableSlot)) == some (5, 170, 3)
#guard (blocksByRangeRequest 64 32).size == 24
#guard (columnsByRangeRequest 0 1 [1, 2]).size == 20 + 16
#guard (columnsByRootRequest [⟨Array.replicate 32 0⟩] [0]).size == 4 + 36 + 8

end Libp2p.Eth2
