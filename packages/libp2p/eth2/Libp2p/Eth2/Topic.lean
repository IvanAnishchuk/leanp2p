import Bytes
import Libp2p.Eth2.Constants

/-!
# The gossip topics

A consensus topic is `/eth2/ForkDigestValue/Name/Encoding` (phase0,
"Topics and messages"). `ForkDigestValue` is the lowercase hex of the
4-byte fork digest with no `0x`. `Name` is a global name or a subnet
name with its index. The encoding is always `ssz_snappy`. "Clients MUST
reject messages with an unknown topic", so the parse knows every name
of the forks up to Fulu and refuses the rest.

The names, by the fork that adds them:

| fork | names |
|---|---|
| phase0 | `beacon_block`, `beacon_aggregate_and_proof`, `voluntary_exit`, `proposer_slashing`, `attester_slashing`, `beacon_attestation_{i}` |
| altair | `sync_committee_contribution_and_proof`, `sync_committee_{i}` |
| altair, light client | `light_client_finality_update`, `light_client_optimistic_update` |
| capella | `bls_to_execution_change` |
| fulu | `data_column_sidecar_{i}` |

Deneb's `blob_sidecar_{i}` is deprecated in Fulu, and this package
leaves it out. The light-client topics come from altair
`light-client/p2p-interface.md`: "All full nodes SHOULD subscribe to
and provide stability on" both.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

/-- The kind of a topic: a global name, or a subnet name with its
index. -/
inductive Kind where
  | beaconBlock
  | beaconAggregateAndProof
  | voluntaryExit
  | proposerSlashing
  | attesterSlashing
  | syncCommitteeContributionAndProof
  | blsToExecutionChange
  | lightClientFinalityUpdate
  | lightClientOptimisticUpdate
  | beaconAttestation (subnet : Nat)
  | syncCommittee (subnet : Nat)
  | dataColumnSidecar (subnet : Nat)
  deriving DecidableEq, BEq, Repr

namespace Kind

/-- The global names, each with its kind. -/
def globals : List (String × Kind) :=
  [("beacon_block", .beaconBlock),
   ("beacon_aggregate_and_proof", .beaconAggregateAndProof),
   ("voluntary_exit", .voluntaryExit),
   ("proposer_slashing", .proposerSlashing),
   ("attester_slashing", .attesterSlashing),
   ("sync_committee_contribution_and_proof", .syncCommitteeContributionAndProof),
   ("bls_to_execution_change", .blsToExecutionChange),
   ("light_client_finality_update", .lightClientFinalityUpdate),
   ("light_client_optimistic_update", .lightClientOptimisticUpdate)]

/-- The subnet names: the prefix before the index, the count of
subnets, and the kind of an index. -/
def subnets : List (String × Nat × (Nat → Kind)) :=
  [("beacon_attestation_", Constants.attestationSubnetCount, .beaconAttestation),
   ("sync_committee_", Constants.syncCommitteeSubnetCount, .syncCommittee),
   ("data_column_sidecar_", Constants.dataColumnSidecarSubnetCount, .dataColumnSidecar)]

/-- The `Name` segment of a topic. -/
def name : Kind → String
  | .beaconBlock => "beacon_block"
  | .beaconAggregateAndProof => "beacon_aggregate_and_proof"
  | .voluntaryExit => "voluntary_exit"
  | .proposerSlashing => "proposer_slashing"
  | .attesterSlashing => "attester_slashing"
  | .syncCommitteeContributionAndProof => "sync_committee_contribution_and_proof"
  | .blsToExecutionChange => "bls_to_execution_change"
  | .lightClientFinalityUpdate => "light_client_finality_update"
  | .lightClientOptimisticUpdate => "light_client_optimistic_update"
  | .beaconAttestation i => s!"beacon_attestation_{i}"
  | .syncCommittee i => s!"sync_committee_{i}"
  | .dataColumnSidecar i => s!"data_column_sidecar_{i}"

/-- The kind of a `Name` segment. A subnet index must be a decimal under
the subnet count. The global names come first, so the prefix
`sync_committee_` never takes `sync_committee_contribution_and_proof`. -/
def ofName? (s : String) : Option Kind :=
  match globals.find? (·.1 == s) with
  | some (_, k) => some k
  | none =>
    subnets.findSome? fun (pre, count, mk) => do
      let rest ← (s.dropPrefix? pre).map (·.toString)
      -- A leading zero would make two names for one subnet.
      if rest.length > 1 && rest.startsWith "0" then none
      let i ← rest.toNat?
      if i < count then some (mk i) else none

end Kind

/-- The topic string of a kind under a fork digest. -/
def topicOf (digest : ByteArray) (k : Kind) : String :=
  s!"/{Constants.topicPrefix}/{Bytes.toHex digest}/{k.name}/{Constants.topicEncoding}"

/-- The fork digest and the kind of a topic string, or `none` for a
topic of another form. -/
def topicParse? (t : String) : Option (ByteArray × Kind) := do
  match t.splitOn "/" with
  | ["", pre, digest, name, enc] =>
    if pre != Constants.topicPrefix || enc != Constants.topicEncoding then none
    let d ← Bytes.ofHex? digest
    if d.size != Libp2p.Protocols.Constants.forkDigestLen then none
    return (d, ← Kind.ofName? name)
  | _ => none

-- The topic of the spec's example ("Encodings"), and the parses.
#guard topicOf ⟨#[0x44, 0x6a, 0x72, 0x32]⟩ .beaconAggregateAndProof ==
  "/eth2/446a7232/beacon_aggregate_and_proof/ssz_snappy"
#guard (topicParse? "/eth2/446a7232/beacon_attestation_63/ssz_snappy").map (·.2) ==
  some (.beaconAttestation 63)
#guard (topicParse? "/eth2/446a7232/beacon_attestation_64/ssz_snappy").isNone
#guard (topicParse? "/eth2/446a7232/beacon_attestation_07/ssz_snappy").isNone
#guard (topicParse? "/eth2/446a7232/sync_committee_contribution_and_proof/ssz_snappy").map (·.2) ==
  some .syncCommitteeContributionAndProof
#guard (topicParse? "/eth2/446a7232/blob_sidecar_0/ssz_snappy").isNone
#guard (topicParse? "/eth2/446a7232/light_client_finality_update/ssz_snappy").map (·.2) ==
  some .lightClientFinalityUpdate
#guard (topicParse? "/eth2/446a72/beacon_block/ssz_snappy").isNone

end Libp2p.Eth2
