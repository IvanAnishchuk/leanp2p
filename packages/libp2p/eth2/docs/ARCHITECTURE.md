# leanp2p eth2: architecture

`libp2p/eth2` is the consensus networking of an Ethereum client over the
leanp2p stack. It turns the consensus networking spec into values of
the packages below it, and it runs them as one service. The client keeps
the chain. It answers the gossip validations and the block and column
requests, and it reads the events.

The spec text is the vendored consensus-specs (`vendor/consensus-specs`,
pinned at `0216d01` in `VECTORS.lock`): the `p2p-interface.md` of every
fork to fulu, fulu `beacon-chain.md` for the fork digest, and fulu
`das-core.md` for the column sidecar. Each of those files equals its
`v1.7.0-beta.4` copy. Every wire value the package uses is the same in
`v1.7.0-alpha.11`, the pin of etheorem and of the shadow node. The
differences between the two are the order of the validation rules,
the type names, and the partial-column format, and none of them reaches
this package.

The package sits at rank 7 of the libp2p group, above `protocols`. It
imports `host`, `protocols`, `discv5`, `identity`, `security`, `mux`,
and `quic`.

## Modules

| Module | Role |
|---|---|
| `Libp2p/Eth2/Constants.lean` | every number and name of the spec that the package uses, each in one home (root §3.8) |
| `Libp2p/Eth2/Fork.lean` | `Chain`: the fork schedule, `compute_fork_version`, the fork data root, Fulu's `compute_fork_digest` with the blob schedule, `ENRForkID`, and the next fork digest |
| `Libp2p/Eth2/Config.lean` | the `Chain` of a testnet directory: the flat keys and `BLOB_SCHEDULE` of `config.yaml`, and the first 40 bytes of `genesis.ssz` |
| `Libp2p/Eth2/Topic.lean` | the topic kinds up to Fulu, the topic string, and its strict parse |
| `Libp2p/Eth2/MessageId.lean` | the Altair message id, with the valid and the invalid snappy domain |
| `Libp2p/Eth2/Enr.lean` | the ENR fields `eth2`, `attnets`, `syncnets`, `cgc`, and `nfd`, and the fork predicates for discovery |
| `Libp2p/Eth2/Messages.lean` | the req/resp methods with their bounds, and the SSZ of `Status`, `MetaData`, Ping, Goodbye, and the requests |
| `Libp2p/Eth2/Gossip.lean` | the router parameters of a consensus node |
| `Libp2p/Eth2/Scoring.lean` | Lighthouse's score profile: the thresholds, the global parameters, and the parameters of each scored topic, from the active validator count and the slot |
| `Libp2p/Eth2/Peers.lean` | the peer table: the Ping intervals, the known MetaData seq numbers, and the bans, as pure transitions |
| `Libp2p/Eth2/Service.lean` | the service: the host, gossipsub, discv5, the req/resp handlers, and the peer duties |

## Public surface

- `Chain`, `Config.chainOf`, and the fork functions of `Chain`.
- `Kind`, `topicOf`, `topicParse?`.
- `messageId`, `messageIdBytes`: the id, as the router and as bytes.
- `Advert`, `advertPairs`, and the readers `enrForkId?`, `forkDigest?`,
  `cgc?`, `attnets?`, `bitSet`, `sameDigest`, `sameFork`.
- The methods `statusMethod`, `goodbyeMethod`, `pingMethod`,
  `metadataV3Method`, `metadataV2Method`, `blocksByRangeMethod`,
  `blocksByRootMethod`, `columnsByRangeMethod`, `columnsByRootMethod`,
  and the request encoders.
- `Status`, `MetaData`.
- `gossipParams`.
- `Scoring.scoredParams`, `Scoring.dynamicParams`, `Scoring.kindParams`,
  `Scoring.globalParams`, `Scoring.thresholds`.
- `Peers`.
- `Service.start`, `subscribe`, `publish`, `report`, `setStatus`,
  `request`, `peers`, `disconnect`, `ban`, `isBanned`, `updateScores`,
  `localEnr`, `stop`, and the client's seams:
  `Config.onEvent` (the `Event` stream) and `Config.serve` (the
  `Inbound` requests with their `Emit`).

## Owned contracts and how the package keeps them

1. **SSZ stays with the client, except the small fixed messages.**
   `protocols` contract 7 keeps the framing package free of SSZ. This
   package encodes only the messages of fixed size that a network
   layer must answer by itself: `Status`, `MetaData`, Ping, and
   Goodbye, and the request forms of the block and column methods.
   Blocks and columns stay opaque bytes, and the client's model owns
   their types and their roots.
2. **One key for libp2p and the ENR.** The service refuses a key that
   is not secp256k1. Peers derive our peer id from our record, so a
   second key would make our record name another peer.
3. **The dialer sends `Status`** on every outbound session, and the
   listener answers with ours. A peer of another fork digest gets
   Goodbye with reason 2 and loses its connection.
4. **Every gossip message waits for the client's answer**
   (`validateMessages`). Data that does not decompress is rejected at
   once. An unknown topic is rejected at once.
5. **Every task has an owner.** The service's task set owns the
   discovery loop, the liveness loop, the dials, the Pings, and the
   `Status` exchanges. `stop` closes the loops' channel, says Goodbye,
   stops gossipsub and discv5, closes
   the host, and joins the set. The host's close removes the notifiee,
   so nothing spawns after the join.
6. **Callbacks never park.** `Config.onEvent` runs on the gossipsub
   loop and on the host's notifiee, so the client must queue its work.

## Decisions

- **The fork digest from the config, with the blob schedule.** Fulu
  XORs the fork data root with the hash of the blob parameters in force
  (EIP-7892). A Blob-Parameters-Only fork changes the digest with the
  same version, and it is a "next fork" for `ENRForkID` and `nfd`. The
  devnet vector of the suite checks the digest, the whole `ENRForkID`,
  and `nfd` against the record of a Lighthouse node.
- **A narrow `config.yaml` reader.** The reader takes the flat
  `KEY: value` lines and the one list, `BLOB_SCHEDULE`. A full YAML
  parser has no use here, and the narrow form fails loudly on a missing
  key.
- **The genesis values from 40 bytes.** `genesis_time` and
  `genesis_validators_root` are the first two fields of every fork's
  `BeaconState`, so the reader needs no state type.
- **Lighthouse's bounds, cut at `MAX_PAYLOAD_SIZE`.** The least block is
  404 bytes, and the least column is 356 bytes. The largest of each is
  the spec's global cap. Lighthouse cuts the column at the blob count
  of the fork, which needs the client's numbers.
- **Goodbye answers nothing**, as in Lighthouse ("Goodbye request has no
  response"). The requester's read ends at the peer's close.
- **Lighthouse's score profile, on by default.** The spec has no score
  parameters yet, and each client picks its own. The package already
  takes Lighthouse's numbers for the other open choices, and the devnet
  peers are two Lighthouse nodes. The service starts the profile as
  Lighthouse does, at
  `SLOTS_PER_EPOCH` active validators and slot 0. The client calls
  `updateScores` with the chain's numbers, every 60 s in Lighthouse. The
  rounding to fixed point is in `Scoring.lean`. `Config.scoring := false`
  runs the router unscored.
- **The seen cache holds 262144 ids**, which covers 341 messages per
  second at mainnet's TTL of 768 s. The ids are `List Nat` in the
  router, about 480 bytes each, so a larger cache costs memory that the
  router's id type must shrink first.
- **`MessageId` can fail.** The node's `payloadId` seam is a pure
  function that answers `Option`. A fault of the OpenSSL SHA-256 gives
  `none`, and the node drops the message.
- **The service pings, and the client judges.** Ping, the MetaData
  refresh, and the ban are mechanism, with Lighthouse's numbers: 15 s
  and 20 s between Pings, a 12 h ban, and at most 1000 bans. The spec
  lets a client end a connection that does not answer a Ping, and it
  sets no penalties. Penalties are scoring, so the service reports
  (`Event.unresponsive`), and the client calls `disconnect` or `ban`.
- **A ban works at the gater.** The gater refuses a banned peer at the
  dial and after the handshake, the first point that proves an inbound
  peer's id. Discovery skips a banned peer's records.
- **The discovery predicate** asks for our fork digest, a TCP or QUIC
  address, and a peer that is not connected. Subnet predicates are the
  client's (`attnets?`, `cgc?`, `bitSet`).

## Conformance

- The devnet record of a Lighthouse node: our digest, `ENRForkID`,
  and `nfd` equal its fields (`Tests/Eth2.lean`).
- The message id: SHA-256 values that Python's `hashlib` computed from
  the spec's formula, for each snappy domain.
- The score profile: Lighthouse's formulas in Python's float64, at
  mainnet timing for 500000 validators, against every scored kind and
  the global parameters, plus the young-chain rule and the spec's
  parameter constraints.
- Two services over loopback: the boot dial, `Status` both ways, gossip
  with the held validation and the consensus id, a block range with its
  context bytes, MetaData, Ping, the MetaData refresh after a Ping,
  Goodbye at stop, and a ban that refuses the peer's redials, on two
  threads and on one.
- The live gate is the shadow node on the Kurtosis devnet, against
  Lighthouse and Grandine (the package PLAN, unit 3).

## What the package must not depend on

- The client's SSZ model. The package carries no block, column, or
  attestation type.
- `cli` and the test harness.
