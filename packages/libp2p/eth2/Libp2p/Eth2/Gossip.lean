import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Eth2.MessageId

/-!
# The consensus gossipsub parameters

The router parameters of a consensus node: the phase0 values ("Gossipsub
Parameters"), the spec's size caps, and the two choices that Lighthouse
makes and the spec leaves open.

| parameter | value | source |
|---|---|---|
| `D`, `D_low`, `D_high`, `D_lazy` | 8, 6, 12, 6 | phase0 |
| `heartbeat_interval` | 700 ms | phase0 |
| `fanout_ttl` | 60 s | phase0 |
| `mcache_len`, `mcache_gossip` | 6, 3 | phase0 |
| `seen_ttl` | `SLOT_DURATION_MS * SLOTS_PER_EPOCH * 2` | phase0 |
| the `data` cap | `max_compressed_len(MAX_PAYLOAD_SIZE)` | phase0, "Gossipsub size limits" |
| the answer later | on | phase0 "Topics and messages" uses ACCEPT, REJECT, and IGNORE |
| IDONTWANT | at 1000 bytes and more | Lighthouse `config.rs`, `idontwant_message_size_threshold` |

The message id is `Libp2p.Eth2.messageId`. The node runs the
`ByteArray` payload path, so the id reads the payload bytes once.

Peer scoring stays off: the thresholds and the weights are the zeros of
`Core.defaults`. The spec says the score parameters "are currently under
investigation", and each client picks its own. Lighthouse derives its
values from the validator count at run time (`gossipsub_scoring_parameters.rs`).
The client sets them through `Node.setTopicParams`.

The seen cache holds 262144 ids. At the TTL of mainnet (768 s), that
covers 341 messages per second.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Protocols.Gossipsub

/-- The seen-cache capacity. -/
def seenCapacity : Nat := 262144

/-- The IDONTWANT threshold. -/
def idontwantThreshold : Nat := 1000

/-- The router parameters for a chain. -/
def gossipParams (c : Chain) : Core.Params :=
  let ttl := max 1 (Constants.seenTtlMs c.slotDurationMs c.slotsPerEpoch)
  { Core.defaults with
    mesh := { d := Constants.meshD, dLow := Constants.meshDLow, dHigh := Constants.meshDHigh,
              dScore := 4, dLazy := Constants.meshDLazy }
    heartbeatInterval := Constants.heartbeatMs
    fanoutTtl := Constants.fanoutTtlMs
    window := { historyLength := Constants.mcacheLen, historyGossip := Constants.mcacheGossip,
                valid := by decide }
    -- `ttl` is a `max 1 _`, so it is positive.
    seen := { capacity := seenCapacity, ttl,
              valid := ⟨by decide, Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left 1 _)⟩ }
    validateMessages := true
    maxDataSize := some (Libp2p.Protocols.Constants.maxCompressedLen
      Libp2p.Protocols.Constants.maxPayloadSize)
    idontwantThreshold := some idontwantThreshold }

/-- The consensus parameters pass the mesh rule of `Params.Valid`. The
mesh does not depend on the chain, so the goal reduces to `8 ≤ 12`. -/
example (c : Chain) : (gossipParams c).mesh.d ≤ (gossipParams c).mesh.dHigh :=
  show 8 ≤ 12 by decide

end Libp2p.Eth2
