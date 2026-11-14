import Libp2p.Eth2.Constants
import Libp2p.Eth2.Fork
import Libp2p.Eth2.Config
import Libp2p.Eth2.Topic
import Libp2p.Eth2.MessageId
import Libp2p.Eth2.Enr
import Libp2p.Eth2.Messages
import Libp2p.Eth2.Gossip
import Libp2p.Eth2.Peers
import Libp2p.Eth2.Service

/-!
# libp2p/eth2

The consensus networking of an Ethereum client over the leanp2p stack:
the fork digest and the chain's config, the topics and the message id,
the ENR fields, the req/resp methods, the gossipsub parameters, and the
service that runs them. The package docs live under `docs/` beside this
file.
-/
