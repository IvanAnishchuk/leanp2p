import Std.Data.HashMap
import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Eth2.Constants
import Libp2p.Eth2.Fork
import Libp2p.Eth2.Topic
import Libp2p.Eth2.Gossip

/-!
# The consensus score profile

The spec leaves the gossipsub score parameters open: they "are currently
under investigation" (phase0, "Gossipsub Parameters"). This module ports
Lighthouse's profile (`service/gossipsub_scoring_parameters.rs`), the
client whose other numbers the package takes.

The profile scores seven topic kinds: the block, the aggregate, each
attestation subnet, the voluntary exit, and the two slashings. The other
kinds, the columns among them, carry no parameters, as in Lighthouse.
Three topic kinds depend on the chain: the block, the aggregate, and
the attestation subnets. Their expected message rates come from the
active validator count, and their mesh delivery terms stay off for the
first slots of the chain. The client passes both numbers
(`dynamicParams`), and Lighthouse updates them every 60 s.

## From float64 to fixed point

Lighthouse computes in float64. This module computes the same formulas
in `Float`, then rounds each value once into the fixed point of
`Gossipsub.Score`:
- a weight, a threshold of the score, and the topic cap to `1/scoreScale`;
- a counter cap, a delivery threshold, and `decayToZero` to `1/counterUnit`;
- a decay factor to `1/scoreScale`;
- a time to milliseconds.

The rounding costs at most half a unit. Two cases cost more. The
attestation topic weight, 1/64, becomes 16/1000, so each subnet weighs
2.4% more. A decay factor keeps three digits, so a factor of 0.99641
becomes 0.996: after its 1280 steps, a counter keeps 0.6% of its value,
where Lighthouse's keeps 1%.

Lighthouse sets `slow_peer_weight` as well. That term is an extension of
rust-libp2p, and `Gossipsub.Score` does not carry it.
-/

set_option autoImplicit false

namespace Libp2p.Eth2.Scoring

open Libp2p.Protocols.Gossipsub

/-! ## Lighthouse's constants -/

/-- `MAX_IN_MESH_SCORE`. -/
def maxInMeshScore : Float := 10
/-- `MAX_FIRST_MESSAGE_DELIVERIES_SCORE`. -/
def maxFirstMessageDeliveriesScore : Float := 40
/-- `BEACON_BLOCK_WEIGHT`. -/
def beaconBlockWeight : Float := 0.5
/-- `BEACON_AGGREGATE_PROOF_WEIGHT`. -/
def beaconAggregateProofWeight : Float := 0.5
/-- `VOLUNTARY_EXIT_WEIGHT`. -/
def voluntaryExitWeight : Float := 0.05
/-- `PROPOSER_SLASHING_WEIGHT`. -/
def proposerSlashingWeight : Float := 0.05
/-- `ATTESTER_SLASHING_WEIGHT`. -/
def attesterSlashingWeight : Float := 0.05
/-- `MESH_MESSAGE_DELIVERIES_WINDOW`: 2 s. -/
def meshMessageDeliveriesWindowMs : Nat := 2000
/-- `decay_to_zero`. -/
def decayToZero : Float := 0.01

/-! ## Fixed point -/

/-- `x` rounded to the nearest integer, half away from zero. -/
private def roundInt (x : Float) : Int :=
  if x < 0 then -((Float.round (-x)).toUInt64.toNat : Int) else ((Float.round x).toUInt64.toNat : Int)

/-- A weight or a score in `1/scoreScale`. -/
def toWeight (x : Float) : Int := roundInt (x * scoreScale.toFloat)

/-- A counter value in `1/counterUnit`. -/
def toCounter (x : Float) : Nat := (roundInt (x * Score.counterUnit.toFloat)).toNat

/-- A decay factor in `1/scoreScale`. -/
def toFactor (x : Float) : Nat := (roundInt (x * scoreScale.toFloat)).toNat

/-- Seconds in milliseconds. -/
def toMs (seconds : Float) : Nat := (roundInt (seconds * 1000)).toNat

/-! ## The settings of a chain (`PeerScoreSettings::new`) -/

/-- The values every topic reads. Times are in seconds. -/
structure Settings where
  slot : Float
  slotsPerEpoch : Nat
  epoch : Float
  decayInterval : Float
  meshN : Nat
  maxPositiveScore : Float
  attestationSubnetWeight : Float

/-- The settings of a chain, with the mesh degree `D` of phase0. -/
def settings (c : Chain) : Settings :=
  let slot := c.slotDurationMs.toFloat / 1000
  let subnets := Constants.attestationSubnetCount.toFloat
  let attestationSubnetWeight := 1 / subnets
  { slot
    slotsPerEpoch := c.slotsPerEpoch
    epoch := slot * c.slotsPerEpoch.toFloat
    decayInterval := if slot < 1 then 1 else slot
    meshN := Constants.meshD
    maxPositiveScore := (maxInMeshScore + maxFirstMessageDeliveriesScore) *
      (beaconBlockWeight + beaconAggregateProofWeight + attestationSubnetWeight * subnets +
        voluntaryExitWeight + proposerSlashingWeight + attesterSlashingWeight)
    attestationSubnetWeight }

namespace Settings

/-- The factor that decays a counter to `decayToZero` in `decayTime`
seconds (`score_parameter_decay`). -/
def decayOver (st : Settings) (decayTime : Float) : Float :=
  Float.pow decayToZero (1 / (decayTime / st.decayInterval))

end Settings

/-- The limit of a counter that gains `rate` each interval and decays by
`decay` (`decay_convergence`). -/
def convergence (decay rate : Float) : Float := rate / (1 - decay)

/-- The counter value one interval below the limit (`threshold`). -/
def threshold (decay rate : Float) : Float := convergence decay rate * decay

/-! ## The topic parameters (`get_topic_params`) -/

/-- The mesh delivery terms of a topic: the decay time in slots, the cap
factor, the activation window in seconds, and the current slot. -/
structure MeshInfo where
  decaySlots : Nat
  capFactor : Float
  activation : Float
  currentSlot : Nat

/-- The parameters of one topic. `rate` is the expected message count per
slot. A topic with no `MeshInfo` has no mesh delivery terms. While the
chain is younger than the decay time, the mesh delivery weight and
threshold are 0, and the failure weight stays, as in Lighthouse. -/
def topicParams (st : Settings) (topicWeight rate firstDecayTime : Float)
    (mesh : Option MeshInfo) : Score.TopicParams :=
  let timeInMeshCap := 3600 / st.slot
  let firstDecay := st.decayOver firstDecayTime
  let firstCap := convergence firstDecay (2 * rate / st.meshN.toFloat)
  let base : Score.TopicParams :=
    { topicWeight := toWeight topicWeight
      timeInMeshWeight := toWeight (10 / timeInMeshCap)
      timeInMeshQuantum := toMs st.slot
      timeInMeshCap := (roundInt timeInMeshCap).toNat
      firstMessageDeliveriesWeight := toWeight (40 / firstCap)
      firstMessageDeliveriesDecay := toFactor firstDecay
      firstMessageDeliveriesCap := toCounter firstCap
      meshMessageDeliveriesWeight := 0
      meshMessageDeliveriesDecay := 0
      meshMessageDeliveriesThreshold := 0
      meshMessageDeliveriesCap := 0
      meshMessageDeliveriesActivation := 0
      meshMessageDeliveriesWindow := 0
      meshFailurePenaltyWeight := 0
      meshFailurePenaltyDecay := 0
      invalidMessageDeliveriesWeight := toWeight (-st.maxPositiveScore / topicWeight)
      invalidMessageDeliveriesDecay := toFactor (st.decayOver (st.epoch * 50)) }
  match mesh with
  | none => base
  | some m =>
    let decay := st.decayOver (st.slot * m.decaySlots.toFloat)
    let thr := threshold decay (rate / 50)
    let cap := if m.capFactor * thr < 2 then 2 else m.capFactor * thr
    let young := m.currentSlot ≤ m.decaySlots
    { base with
      meshMessageDeliveriesWeight := if young then 0 else toWeight (-topicWeight)
      meshMessageDeliveriesDecay := toFactor decay
      meshMessageDeliveriesThreshold := if young then 0 else toCounter thr
      meshMessageDeliveriesCap := toCounter cap
      meshMessageDeliveriesActivation := toMs m.activation
      meshMessageDeliveriesWindow := meshMessageDeliveriesWindowMs
      meshFailurePenaltyWeight := toWeight (-topicWeight)
      meshFailurePenaltyDecay := toFactor decay }

/-! ## The chain-dependent topics (`get_dynamic_topic_params`) -/

/-- `get_committee_count_per_slot` for `active` validators. -/
def committeesPerSlot (slotsPerEpoch active : Nat) : Nat :=
  max 1 (min Constants.maxCommitteesPerSlot (active / slotsPerEpoch / Constants.targetCommitteeSize))

/-- The expected aggregates per slot, and the committees per slot
(`expected_aggregator_count_per_slot`). -/
def aggregatorsPerSlot (slotsPerEpoch active : Nat) : Float × Nat :=
  let perSlot := committeesPerSlot slotsPerEpoch active
  let committees := perSlot * slotsPerEpoch
  let smaller := active / committees
  let larger := active - smaller * committees
  let moduloSmaller := max 1 (smaller / Constants.targetAggregatorsPerCommittee)
  let moduloLarger := max 1 ((smaller + 1) / Constants.targetAggregatorsPerCommittee)
  let total := ((committees - larger) * smaller).toFloat / moduloSmaller.toFloat +
    (larger * (smaller + 1)).toFloat / moduloLarger.toFloat
  (total / slotsPerEpoch.toFloat, perSlot)

/-- The parameters of the block, the aggregate, and every attestation
subnet, for `active` validators at `slot`. -/
def dynamicParams (st : Settings) (active slot : Nat) :
    Score.TopicParams × Score.TopicParams × Score.TopicParams :=
  let spe := st.slotsPerEpoch
  let (aggregators, perSlot) := aggregatorsPerSlot spe active
  let bursts := 2 * Constants.attestationSubnetCount / spe ≤ perSlot
  let block := topicParams st beaconBlockWeight 1 (st.epoch * 20)
    (some ⟨spe * 5, 3, st.epoch, slot⟩)
  let aggregate := topicParams st beaconAggregateProofWeight aggregators st.epoch
    (some ⟨spe * 2, 4, st.epoch, slot⟩)
  let attestation := topicParams st st.attestationSubnetWeight
    (active.toFloat / Constants.attestationSubnetCount.toFloat / spe.toFloat)
    (st.epoch * (if bursts then 1 else 4))
    (some ⟨spe * (if bursts then 4 else 16), 16,
      if bursts then st.slot * (spe / 2 + 1).toFloat else st.epoch * 3, slot⟩)
  (block, aggregate, attestation)

/-! ## The whole profile -/

/-- Lighthouse's thresholds (`lighthouse_gossip_thresholds`). -/
def thresholds : Thresholds :=
  { gossipThreshold := toWeight (-4000)
    publishThreshold := toWeight (-8000)
    graylistThreshold := toWeight (-16000)
    acceptPXThreshold := toWeight 100
    opportunisticGraftThreshold := toWeight 5 }

/-- The parameters of a topic kind, for `active` validators at `slot`.
`none` for a kind the profile does not score. The six values are
computed once, before the function: the router looks a topic up for
every score it reads, and the Float powers would run again each time. -/
def kindParams (st : Settings) (active slot : Nat) : Kind → Option Score.TopicParams :=
  let (block, aggregate, attestation) := dynamicParams st active slot
  let rare := 1 / 5 / st.slotsPerEpoch.toFloat
  let exit := topicParams st voluntaryExitWeight (4 / st.slotsPerEpoch.toFloat) (st.epoch * 100) none
  let attester := topicParams st attesterSlashingWeight rare (st.epoch * 100) none
  let proposer := topicParams st proposerSlashingWeight rare (st.epoch * 100) none
  fun
    | .beaconBlock => some block
    | .beaconAggregateAndProof => some aggregate
    | .beaconAttestation _ => some attestation
    | .voluntaryExit => some exit
    | .attesterSlashing => some attester
    | .proposerSlashing => some proposer
    | _ => none

/-- The global parameters (`get_peer_score_params`). -/
def globalParams (st : Settings) : Score.GlobalParams :=
  let behaviourDecay := st.decayOver (st.epoch * 10)
  let target := convergence behaviourDecay (10 / st.slotsPerEpoch.toFloat) - 6
  let cap := st.maxPositiveScore * 0.5
  { appSpecificWeight := toWeight 1
    ipColocationFactorWeight := toWeight (-cap)
    ipColocationFactorThreshold := 8
    behaviourPenaltyWeight := toWeight (-4000 / (target * target))
    behaviourPenaltyThreshold := toCounter 6
    behaviourPenaltyDecay := toFactor behaviourDecay
    decayInterval := toMs st.decayInterval
    decayToZero := toCounter decayToZero
    topicScoreCap := toWeight cap }

/-- The score parameters of the topics under `digest`, for `active`
validators at `slot`. A topic of another digest gets none. -/
def scoreParams (c : Chain) (digest : ByteArray) (active slot : Nat) : Score.Params :=
  let st := settings c
  let byKind := kindParams st active slot
  -- The router reads a topic's parameters for every counter of every
  -- score, so the lookup is one hash of the topic string, built once.
  let scored : List Kind := [.beaconBlock, .beaconAggregateAndProof, .voluntaryExit,
    .proposerSlashing, .attesterSlashing] ++
    (List.range Constants.attestationSubnetCount).map .beaconAttestation
  let table : Std.HashMap String Score.TopicParams := Std.HashMap.ofList
    (scored.filterMap fun k => (byKind k).map fun tp => (topicOf digest k, tp))
  { topics := fun t => table.get? t.name
    global := globalParams st }

/-- The router parameters of a consensus node with Lighthouse's scoring:
`gossipParams` with the score parameters, the thresholds, and a score
retention of 100 epochs (`retain_score`). -/
def scoredParams (c : Chain) (digest : ByteArray) (active slot : Nat) : Core.Params :=
  { gossipParams c with
    score := scoreParams c digest active slot
    thresholds
    retainScore := toMs ((settings c).epoch * 100) }

end Libp2p.Eth2.Scoring
