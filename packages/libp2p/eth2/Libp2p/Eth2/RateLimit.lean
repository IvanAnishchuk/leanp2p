import Libp2p.Protocols.ReqResp.RateLimit
import Libp2p.Eth2.Messages

/-!
# The responder's quotas

The spec allows a responder to withhold chunks ("The responder MAY
rate-limit chunks by withholding each chunk until capacity is
available"), and it sets no numbers. The service takes Lighthouse's
inbound quotas (`rpc/config.rs`, `RateLimiterConfig` and
`InboundRateLimiterConfig::default`), per peer and per method, and it
charges one token per chunk, the finer choice of the spec's rationale.
Lighthouse charges a request its largest answer at once. Per chunk, the
same quota gives the same rate.

Goodbye has no quota. Lighthouse runs it at once, "so that the
disconnection is handled promptly". Lighthouse keys every inbound
bucket by peer and keeps no global level, and the service does the
same.
-/

set_option autoImplicit false

namespace Libp2p.Eth2

open Libp2p.Protocols.ReqResp (Quota Method)

/-- The quota of a method, `none` for Goodbye. -/
def quotaOf (m : Method) : Option Quota :=
  if m.id == goodbyeMethod.id then none
  else if m.id == pingMethod.id then some ⟨2, 10000⟩
  else if m.id == metadataV3Method.id || m.id == metadataV2Method.id then some ⟨2, 5000⟩
  else if m.id == statusMethod.id then some ⟨5, 15000⟩
  else if m.id == blocksByRangeMethod.id || m.id == blocksByRootMethod.id ||
      m.id == blocksByHeadMethod.id then some ⟨128, 10000⟩
  else if m.id == columnsByRangeMethod.id || m.id == columnsByRootMethod.id then
    some ⟨Constants.maxRequestDataColumnSidecars, 10000⟩
  -- `InboundRateLimiterConfig::default`: the largest valid request as
  -- the burst, at the former rate of one update per 10 s.
  else if m.id == lightClientUpdatesByRangeMethod.id then
    some ⟨Constants.maxRequestLightClientUpdates, 1280000⟩
  else some ⟨1, 10000⟩

#guard quotaOf goodbyeMethod == none
#guard quotaOf blocksByRangeMethod == some ⟨128, 10000⟩
#guard quotaOf columnsByRootMethod == some ⟨16384, 10000⟩
#guard quotaOf lightClientBootstrapMethod == some ⟨1, 10000⟩

end Libp2p.Eth2
