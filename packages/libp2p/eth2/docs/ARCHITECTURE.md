# leanp2p eth2: architecture

`libp2p/eth2` is the consensus networking of an Ethereum client over the
leanp2p stack. It turns the consensus networking spec into values of
the packages below it, and it runs them as one service. The client keeps
the chain and every consensus type. It hands the service its fork
schedule, its `Status`, and its `MetaData` as bytes. It answers the
gossip validations and the requests, and it reads the events.

The spec text is the vendored consensus-specs (`vendor/consensus-specs`,
pinned at `0216d01` in `VECTORS.lock`): the `p2p-interface.md` of every
fork to fulu, and fulu `partial-columns/p2p-interface.md`. Each of those
files equals its `v1.7.0-beta.4` copy. Every wire value the package
uses is the same in `v1.7.0-alpha.11`, the pin of etheorem and of the
shadow node. The two differ in the order of the validation rules, in
the type names, and in the partial-column types. The package reads none
of those.

The package sits at rank 7 of the libp2p group, above `protocols`. It
imports `host`, `protocols`, `discv5`, `identity`, `security`, `mux`,
and `quic`.

## Modules

| Module | Role |
|---|---|
| `Libp2p/Eth2/Constants.lean` | every number and name of the spec that the package uses, each in one home (root §3.8) |
| `Libp2p/Eth2/Uint64.lean` | the little-endian `Uint64` of the message id, Ping, and Goodbye |
| `Libp2p/Eth2/Fork.lean` | `Chain`: the fork schedule of the client, its lookups by epoch, and the wall-clock epoch |
| `Libp2p/Eth2/Topic.lean` | the topic kinds up to Fulu, the topic string, and its strict parse |
| `Libp2p/Eth2/MessageId.lean` | the Altair message id, with the valid and the invalid snappy domain |
| `Libp2p/Eth2/Enr.lean` | the ENR fields `eth2`, `attnets`, `syncnets`, `cgc`, and `nfd`, and the fork predicates for discovery |
| `Libp2p/Eth2/Messages.lean` | the req/resp methods with their bounds and chunk counts, and the digest at offset 0 of a `Status` |
| `Libp2p/Eth2/Gossip.lean` | the router parameters of a consensus node |
| `Libp2p/Eth2/Scoring.lean` | Lighthouse's score profile: the thresholds, the global parameters, and the parameters of each scored topic, from the active validator count and the slot |
| `Libp2p/Eth2/Forks.lean` | the gossip across a fork: the pure schedule of the post-fork joins, the switch, and the retirement of the pre-fork topics |
| `Libp2p/Eth2/Peers.lean` | the peer table: the Ping intervals, the known MetaData seq numbers, and the bans, as pure transitions |
| `Libp2p/Eth2/PartialColumns.lean` | the group ID of a partial column, and the first-delivery reward once per peer, block, and column |
| `Libp2p/Eth2/Service.lean` | the service: the host, gossipsub, discv5, the req/resp handlers, and the peer duties |

## Public surface

- `ForkEntry`, `Chain`, `Chain.wellFormed`, and the lookups of `Chain`.
- `Kind`, `topicOf`, `topicParse?`.
- `messageId`, `messageIdBytes`: the id, as the router and as bytes.
- `Advert`, `advertPairs`, and the readers `enrForkId?`, `forkDigest?`,
  `cgc?`, `attnets?`, `bitSet`, `sameDigest`, `sameFork`.
- The methods `statusMethod`, `goodbyeMethod`, `pingMethod`,
  `metadataV3Method`, `metadataV2Method`, `blocksByRangeMethod`,
  `blocksByRootMethod`, `blocksByHeadMethod`, `columnsByRangeMethod`,
  `columnsByRootMethod`, the four `lightClient*Method`s, the lists
  `servedMethods` and `oneOrErrorMethods`, and `statusDigest`,
  `withDigest`, `le64`, `le64At`.
- `gossipParams`.
- `Scoring.scoredParams`, `Scoring.dynamicParams`, `Scoring.kindParams`,
  `Scoring.globalParams`, `Scoring.thresholds`.
- `Peers`, `ForkState`, `ForkAction`.
- `PartialColumns.groupIdOf`, `PartialColumns.rootOf?`,
  `PartialColumns.Rewards`.
- `Service.start`, `subscribe`, `unsubscribe`, `publish`, `report`,
  `setStatus`, `setMetaData`, `request`, `requestEach` (a check of each
  chunk before the next), `partialColumnPeers`, `sendPartialColumn`,
  `judgePartialColumn`, `peers`, `disconnect`, `ban`, `isBanned`,
  `updateScores`, `localEnr`, `stop`, and the client's seams:
  `Config.onEvent` (the `Event` stream) and `Config.serve` (the method
  and the request's bytes, with an `Emit`, answered by an `Ending`).

## Owned contracts and how the package keeps them

1. **The client owns every consensus type.** The package encodes and
   decodes no SSZ, and it computes no digest. It reads the spec's fixed
   places and nothing else:
   - the first 4 bytes of a `Status`, its `fork_digest`;
   - the `Uint64` of Ping and Goodbye, 8 little-endian bytes;
   - the size of each payload, against its method's bounds;
   - the ENR fields;
   - the version byte and the root of a partial-column group ID.

   The client hands in the schedule (`Chain`), each entry with its
   digest and the SSZ of its `ENRForkID`. It also hands in its `Status`
   and its `MetaData`. It writes each request it sends, and it reads
   each request it serves. `protocols` contract 7 keeps the framing
   package free of SSZ in the same way.
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
   discovery loop, the liveness loop, the fork loop, the dials, the
   Pings, and the `Status` exchanges. `stop` closes the loops' channel,
   says Goodbye, stops gossipsub and discv5, closes the host, and joins
   the set. The host's close removes the notifiee, so nothing spawns
   after the join.
6. **Callbacks never park.** `Config.onEvent` runs on the gossipsub
   loop and on the host's notifiee, so the client must queue its work.
7. **An answer stays inside the method's cap.** The service counts the
   chunks that the client emits, and it refuses each chunk past
   `Method.maxChunks`. A cap that the request sets, such as "no more
   than `count` blocks", is the client's, since it reads the request.
   The client ends an answer in error through `Ending`, and the error
   chunk goes last.
8. **Our digest has one owner.** The fork loop keeps it. The service
   writes it over the first 4 bytes of each `Status` the client hands
   in, and over the stored `Status` at the switch, each in one atomic
   update.

## Decisions

- **The schedule comes from the client.** A digest needs the chain's
  config, its genesis, and Fulu's blob schedule (EIP-7892). An
  `ENRForkID` is SSZ. The client has all of these. The service needs
  each digest only to compare it and to print it in a topic. So the
  schedule is a list of entries by epoch, and the service looks the
  digest, the next digest, and the next epoch up in it. A
  Blob-Parameters-Only fork is one more entry. `Chain.wellFormed` holds
  the shape the lookups need, and the service refuses a chain that
  fails it.
- **Bounds are sizes the spec fixes, or `MAX_PAYLOAD_SIZE`.** `Status`
  has 92 bytes, Ping and Goodbye 8, `MetaData` 25 and 17, and the fixed
  requests 24, 40, 32, and 16. Each other payload is bounded by the
  global cap, and the client's SSZ decoder checks the rest. A client
  that wants tighter bounds on a response passes its own `Method` to
  `request`.
- **Goodbye answers one chunk, and takes zero or one.** phase0 says "The
  response MUST consist of a single `response_chunk`". The service
  answers `Uint64 0`, as Lodestar does, whose requester expects exactly
  one chunk. Lighthouse answers none ("Goodbye request has no
  response"), against the spec, so our requester reads at most one and
  ends at the peer's close.
- **Lighthouse's score profile, on by default.** The spec has no score
  parameters yet, and each client picks its own. The package already
  takes Lighthouse's numbers for the other open choices, and the devnet
  peers are two Lighthouse nodes. The service starts the profile as
  Lighthouse does, at `SLOTS_PER_EPOCH` active validators and slot 0.
  The client calls `updateScores` with the chain's numbers, every 60 s
  in Lighthouse. The rounding to fixed point is in `Scoring.lean`.
  `Config.scoring := false` runs the router unscored.
- **Light clients at the network level.** altair
  `light-client/p2p-interface.md` asks full nodes to subscribe to the two
  light-client topics and to serve the four methods. The package carries
  the topic kinds and the methods, and the client gives the data
  (`Config.serve`). A bootstrap, finality, or optimistic request with no
  data gets `ResourceUnavailable`, as the spec asks
  (`oneOrErrorMethods`). Lighthouse does not score the two topics, and
  neither does the profile.
- **Partial columns at the network level.** Fulu sends a column in parts
  over gossipsub v1.3 partial messages. The column topics of every
  digest of the schedule take the client's `Config.partialColumns`, so
  a fork changes no router parameter. The service builds and reads the
  group ID, and it drops an unknown version ("Implementations MUST
  ignore unknown versions"). It hands the parts metadata and the message
  to the client as bytes (`Event.partialColumn`), and the heartbeat's
  gossip targets too (`Event.partialGossip`). The client decides what
  each peer gets and sends it (`sendPartialColumn`). The router skips
  the peers that requested partial messages when the full sidecar goes
  out. The service gives the first-delivery reward once per peer,
  block, and column ("Clients SHOULD limit the rate at which a peer
  gets the first message delivery reward"), over the latest 4 blocks,
  the bound of Lighthouse's header tracker.
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
- **The fork loop owns the digest.** altair "Transitioning the gossip"
  asks for the post-fork topics in advance, no negative score on the
  pre-fork topics after the fork, and the end of the pre-fork topics two
  epochs later. The lead is Lighthouse's, one epoch. The loop keeps our
  digest, and `topic`, `Status`, and the record read it, so the three
  never disagree. The client subscribes by kind once, and the loop
  carries the kind to each new digest with its score parameters.
- **A ban works at the gater.** The gater refuses a banned peer at the
  dial and after the handshake, the first point that proves an inbound
  peer's id. Discovery skips a banned peer's records.
- **The discovery predicate** asks for our fork digest, a TCP or QUIC
  address, and a peer that is not connected. Subnet predicates are the
  client's (`attnets?`, `cgc?`, `bitSet`). phase0 says a client SHOULD
  connect to peers whose whole `ENRForkID` matches ours, and it MAY
  connect on the digest alone. Lighthouse takes the digest alone
  (`discovery/mod.rs`, lines 833 to 840), so a peer that has not yet
  scheduled the next fork stays reachable. `sameFork` gives the whole
  match to a client that wants it.

## Conformance

- The devnet record of a Lighthouse node: its digest, `ENRForkID`, and
  `nfd` read back as the schedule's, and it passes `sameFork`
  (`Tests/Eth2.lean`).
- The message id: SHA-256 values that Python's `hashlib` computed from
  the spec's formula, for each snappy domain.
- The score profile: Lighthouse's formulas in Python's float64, at
  mainnet timing for 500000 validators, against every scored kind and
  the global parameters, plus the young-chain rule and the spec's
  parameter constraints.
- Two services over loopback: the boot dial, `Status` both ways with our
  digest over the client's bytes, gossip with the held validation and
  the consensus id, the served methods with their context bytes and
  their cap, MetaData, Ping, the MetaData refresh after a Ping, the
  client's updates, Goodbye at stop, and a ban that refuses the peer's
  redials, on two threads and on one.
- Partial columns over loopback: the client's metadata and message
  reach the peer with the block root, and a group ID of an unknown
  version does not.
- A live fork: a service on a chain of 2 s epochs with a new entry at
  epoch 2 joins the post-fork topic ahead, switches its `Status`, record,
  and topics at the fork, and leaves the pre-fork topic two epochs
  later.
- The live gate is the shadow node on the Kurtosis devnet, against
  Lighthouse and Grandine (the package PLAN, unit 3).

## What the package must not depend on

- The client's SSZ model, or any SSZ code. The package carries no
  consensus type.
- `cli` and the test harness.
