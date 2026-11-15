import Libp2p.Protocols.ReqResp.Payload
import Libp2p.Eth2.Constants
import Libp2p.Eth2.Uint64

/-!
# The req/resp methods

The methods a Fulu node speaks, as `ReqResp.Method` values, with their
protocol ids, their size bounds, their `ForkDigest`-context, and their
chunk counts. The framing package frames the bytes. This module says
how many.

The payloads are SSZ, and their types belong to the client. The service
reads three things in them, each at a place the spec fixes:

* the `fork_digest` of a `Status`, its first 4 bytes;
* the `Uint64` of `Ping` and of `Goodbye`, "encoded as a single
  SSZ-field", 8 little-endian bytes;
* the size of each payload, against the method's bounds.

A payload of fixed size has bounds of that size. Each other payload is
bounded by `MAX_PAYLOAD_SIZE`, and the client checks its SSZ. A client
that wants tighter bounds passes its own `Method` to `Service.request`.

| method | request | response |
|---|---|---|
| `Status` v2 | 92 | 92 |
| `Goodbye` v1, `Ping` v1 | 8 | 8 |
| `MetaData` v3 | none | 25 |
| `MetaData` v2 | none | 17 |
| `BeaconBlocksByRange` v2 | 24 | variable |
| `BeaconBlocksByHead` v1 | 40 | variable |
| `GetLightClientBootstrap` v1 | 32 | variable |
| `LightClientUpdatesByRange` v1 | 16 | variable |
| `GetLightClientFinalityUpdate` v1, `GetLightClientOptimisticUpdate` v1 | none | variable |
| `BeaconBlocksByRoot` v2, `DataColumnSidecarsByRange` v1, `DataColumnSidecarsByRoot` v1 | variable | variable |
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Protocols.ReqResp (Method Bounds)

/-- The width of `Status` v2 (fulu, "Status v2"). -/
def statusLen : Nat := 92

/-- The width of `MetaData` v3 (fulu, "MetaData"). -/
def metaDataV3Len : Nat := 25

/-- The width of `MetaData` v2 (altair, "MetaData"). -/
def metaDataV2Len : Nat := 17

/-- The `fork_digest` of a `Status`: its first field. -/
def statusDigest (status : ByteArray) : ByteArray := status.extract 0 4

/-- A `Status` with its `fork_digest` replaced. -/
def withDigest (status digest : ByteArray) : ByteArray :=
  digest ++ status.extract 4 status.size

/-- A fixed size. -/
def exactly (n : Nat) : Bounds := ⟨n, n⟩

/-- A payload of variable size. -/
def anySize : Bounds := ⟨0, Libp2p.Protocols.Constants.maxPayloadSize⟩

/-- `/eth2/beacon_chain/req/status/2/ssz_snappy`. -/
def statusMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "status" 2
    request := some (exactly statusLen), response := exactly statusLen
    contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/goodbye/1/ssz_snappy`. "The response MUST
consist of a single `response_chunk`", and the service answers one, as
Lodestar does. Lighthouse answers none ("Goodbye request has no
response"), so the requester reads at most one. -/
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
    request := none, response := exactly metaDataV3Len, contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/metadata/2/ssz_snappy`. -/
def metadataV2Method : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "metadata" 2
    request := none, response := exactly metaDataV2Len, contextLen := 0, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/beacon_blocks_by_range/2/ssz_snappy`:
`start_slot`, `count`, and `step`. -/
def blocksByRangeMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "beacon_blocks_by_range" 2
    request := some (exactly 24), response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestBlocksDeneb }

/-- `/eth2/beacon_chain/req/beacon_blocks_by_root/2/ssz_snappy`. -/
def blocksByRootMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "beacon_blocks_by_root" 2
    request := some anySize, response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestBlocksDeneb }

/-- `/eth2/beacon_chain/req/beacon_blocks_by_head/1/ssz_snappy` (fulu,
"BeaconBlocksByHead v1"): `beacon_root` and `count`, and the blocks of
the root's ancestry, newest first. "No more than
`MAX_REQUEST_BLOCKS_DENEB` may be requested at a time." -/
def blocksByHeadMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "beacon_blocks_by_head" 1
    request := some (exactly 40), response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestBlocksDeneb }

/-- `/eth2/beacon_chain/req/data_column_sidecars_by_range/1/ssz_snappy`. -/
def columnsByRangeMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "data_column_sidecars_by_range" 1
    request := some anySize, response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestDataColumnSidecars }

/-- `/eth2/beacon_chain/req/data_column_sidecars_by_root/1/ssz_snappy`. -/
def columnsByRootMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "data_column_sidecars_by_root" 1
    request := some anySize, response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestDataColumnSidecars }

/-! ## The light-client methods

altair `light-client/p2p-interface.md`, "The Req/Resp domain". Each
response carries the `ForkDigest` of its header's epoch. -/

/-- `/eth2/beacon_chain/req/light_client_bootstrap/1/ssz_snappy`: a block
root, and one `LightClientBootstrap`. -/
def lightClientBootstrapMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "light_client_bootstrap" 1
    request := some (exactly 32), response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/light_client_updates_by_range/1/ssz_snappy`:
`start_period` and `count`, and at most
`min(MAX_REQUEST_LIGHT_CLIENT_UPDATES, count)` updates. -/
def lightClientUpdatesByRangeMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "light_client_updates_by_range" 1
    request := some (exactly 16), response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen
    maxChunks := Constants.maxRequestLightClientUpdates }

/-- `/eth2/beacon_chain/req/light_client_finality_update/1/ssz_snappy`:
"No Request Content", and one `LightClientFinalityUpdate`. -/
def lightClientFinalityUpdateMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "light_client_finality_update" 1
    request := none, response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen, maxChunks := 1 }

/-- `/eth2/beacon_chain/req/light_client_optimistic_update/1/ssz_snappy`:
"No Request Content", and one `LightClientOptimisticUpdate`. -/
def lightClientOptimisticUpdateMethod : Method :=
  { id := Libp2p.Protocols.Constants.reqRespId "light_client_optimistic_update" 1
    request := none, response := anySize
    contextLen := Libp2p.Protocols.Constants.forkDigestLen, maxChunks := 1 }

/-- The methods whose answer is one chunk or an error. "When no
`LightClientFinalityUpdate` is available, peers SHOULD respond with
error code `3: ResourceUnavailable`", and the same holds for the
bootstrap and the optimistic update. -/
def oneOrErrorMethods : List Method :=
  [lightClientBootstrapMethod, lightClientFinalityUpdateMethod, lightClientOptimisticUpdateMethod]

/-- The methods the client answers (`Config.serve`). The service answers
the others itself. -/
def servedMethods : List Method :=
  [blocksByRangeMethod, blocksByRootMethod, blocksByHeadMethod, columnsByRangeMethod,
   columnsByRootMethod, lightClientBootstrapMethod, lightClientUpdatesByRangeMethod,
   lightClientFinalityUpdateMethod, lightClientOptimisticUpdateMethod]

#guard statusDigest (withDigest ⟨Array.replicate statusLen 7⟩ ⟨#[1, 2, 3, 4]⟩) == ⟨#[1, 2, 3, 4]⟩
#guard (withDigest ⟨Array.replicate statusLen 7⟩ ⟨#[1, 2, 3, 4]⟩).size == statusLen

end Libp2p.Eth2
