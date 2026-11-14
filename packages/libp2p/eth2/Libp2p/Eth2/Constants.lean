import Libp2p.Protocols.Constants

/-!
# The constants of `libp2p/eth2`

Every number and name of the consensus networking spec that this
package uses has its one home here (root ARCHITECTURE §3.8). The text is
consensus-specs `v1.7.0-beta.4`. Each value below is the same in
`v1.7.0-alpha.11`, the pin of etheorem and of the shadow node.

The numbers of the req/resp framing (`MAX_PAYLOAD_SIZE`,
`max_compressed_len`, the `ForkDigest` width, the result codes) and the
gossip size cap live in `Libp2p.Protocols.Constants`. This module uses
those.
-/

set_option autoImplicit false

namespace Libp2p.Eth2.Constants

/-! ## The gossip domain (phase0 and altair `p2p-interface.md`) -/

/-- `MESSAGE_DOMAIN_INVALID_SNAPPY`: the message-id domain of data that
does not decompress (phase0, "Configs"). -/
def messageDomainInvalidSnappy : ByteArray := ⟨#[0x00, 0x00, 0x00, 0x00]⟩

/-- `MESSAGE_DOMAIN_VALID_SNAPPY`: the message-id domain of data that
decompresses (phase0, "Configs"). -/
def messageDomainValidSnappy : ByteArray := ⟨#[0x01, 0x00, 0x00, 0x00]⟩

/-- The width of a message id: "the following 20 byte value" (altair,
"Topics and messages"). -/
def messageIdLen : Nat := 20

/-- The first segment of every topic: `/eth2/ForkDigestValue/Name/Encoding`
(phase0, "Topics and messages"). -/
def topicPrefix : String := "eth2"

/-- The one gossip encoding: "ssz_snappy" (phase0, "Encodings"). -/
def topicEncoding : String := "ssz_snappy"

/-- `ATTESTATION_SUBNET_COUNT` (phase0, "Configs"). -/
def attestationSubnetCount : Nat := 64

/-- `SYNC_COMMITTEE_SUBNET_COUNT` (altair `validator.md`, "Constants"). -/
def syncCommitteeSubnetCount : Nat := 4

/-- `DATA_COLUMN_SIDECAR_SUBNET_COUNT` (fulu, "Configs"). -/
def dataColumnSidecarSubnetCount : Nat := 128

/-- The gossipsub parameters of phase0 ("Gossipsub Parameters"): `D`,
`D_low`, `D_high`, and `D_lazy`. -/
def meshD : Nat := 8
def meshDLow : Nat := 6
def meshDHigh : Nat := 12
def meshDLazy : Nat := 6

/-- `heartbeat_interval`: 0.7 s. -/
def heartbeatMs : Nat := 700

/-- `fanout_ttl`: 60 s. -/
def fanoutTtlMs : Nat := 60000

/-- `mcache_len`: the heartbeats of full messages the cache keeps for
IWANT. -/
def mcacheLen : Nat := 6

/-- `mcache_gossip`: the heartbeats that gossip lists. -/
def mcacheGossip : Nat := 3

/-- `seen_ttl` in milliseconds: `SLOT_DURATION_MS * SLOTS_PER_EPOCH * 2`.
The slot length and the epoch length come from the chain's config. -/
def seenTtlMs (slotDurationMs slotsPerEpoch : Nat) : Nat := slotDurationMs * slotsPerEpoch * 2

/-! ## The req/resp domain -/

/-- `MAX_REQUEST_BLOCKS_DENEB` (deneb `p2p-interface.md`, "Configs"). -/
def maxRequestBlocksDeneb : Nat := 128

/-- `NUMBER_OF_COLUMNS` (fulu `das-core.md`, "Preset"). -/
def numberOfColumns : Nat := 128

/-- `compute_max_request_data_column_sidecars()` (fulu, "Helpers"). -/
def maxRequestDataColumnSidecars : Nat := maxRequestBlocksDeneb * numberOfColumns

/-- The Goodbye reasons of phase0 ("Goodbye v1"). -/
def goodbyeClientShutdown : Nat := 1
def goodbyeIrrelevantNetwork : Nat := 2
def goodbyeFault : Nat := 3

/-! ## Epochs and the ENR -/

/-- `FAR_FUTURE_EPOCH`: `2**64 - 1`. -/
def farFutureEpoch : Nat := 2 ^ 64 - 1

/-- The ENR key `eth2`: the SSZ of `ENRForkID` (phase0, "`eth2` field"). -/
def nameEth2 : List Nat := "eth2".toUTF8.toList.map (·.toNat)

/-- The ENR key `attnets`: the attestation subnet bitfield. -/
def nameAttnets : List Nat := "attnets".toUTF8.toList.map (·.toNat)

/-- The ENR key `syncnets`: the sync committee subnet bitfield (altair). -/
def nameSyncnets : List Nat := "syncnets".toUTF8.toList.map (·.toNat)

/-- The ENR key `cgc`: the custody group count (fulu). -/
def nameCgc : List Nat := "cgc".toUTF8.toList.map (·.toNat)

/-- The ENR key `nfd`: the next fork digest (fulu). -/
def nameNfd : List Nat := "nfd".toUTF8.toList.map (·.toNat)

/-- The width of `ENRForkID`: a 4-byte digest, a 4-byte version, and an
8-byte epoch. -/
def enrForkIdLen : Nat := 16

end Libp2p.Eth2.Constants
