# leanp2p eth2: plan

The package's work units, in order. Each unit names its checks. The
package ARCHITECTURE holds the contracts, and the root documents bind
both.

## Units

1. **The pure layer.** The constants, `Chain` and its lookups, the
   topics, the message id, the ENR fields, the methods, and the gossip
   parameters.
2. **The service.** The host with TCP and QUIC, gossipsub on the payload
   path with the held validation, discv5 with our record and the
   discovery loop, the `Status` duty, the answers to Ping, MetaData, and
   Goodbye with the client's bytes, and the client's seams for gossip
   and for the served methods.
3. **The live gate.** The shadow node over this service, on the Kurtosis
   devnet of `etheorem-shadow-node` (`devnet/multi.yaml`: two
   Lighthouse nodes and one Grandine), against the same agreement as
   its Rust path.
4. **The peer duties.** The peer table (`Peers`), the liveness loop
   with the MetaData refresh, and the ban at the gater.
5. **The score profile.** Lighthouse's parameters (`Scoring`), on by
   default, with `updateScores` for the chain-dependent topics.
6. **Forks.** The fork schedule (`ForkState`) and the fork loop: the
   post-fork joins one epoch ahead, the switch, and the retirement two
   epochs after.
7. **Partial columns.** The partial options of the column topics, the
   group ID, the client's bytes both ways, and the first-delivery reward
   once per peer, block, and column.

## Consumers

- `etheorem-shadow-node`: its p2p adapter maps the frame commands and
  events of `P2p/Frames.lean` onto `Service`.

## Test milestones

Unit 1 (`Tests/Eth2.lean`):
- The record of a Lighthouse node of the devnet carries the devnet's
  digest `8049f250`. Its whole `ENRForkID` and its `nfd` equal the
  schedule's, and its `cgc` is a supernode's 128.
- A later entry is the next fork, changes the digest at its epoch, and
  gives `nfd`. The digests from an epoch on list ours, then each later
  one.
- `Chain.wellFormed` refuses an empty schedule, one that starts after
  epoch 0, one out of order, and a digest of 3 bytes.
- The wall-clock epoch starts at genesis, and epoch 0 holds before it.
- The message id of data that does not decompress, and of compressed
  data, equal the values of Python's `hashlib`. The topic enters the
  id.
- The digest of a `Status` is its first 4 bytes, and a new digest keeps
  the other 88. The methods have the spec's fixed sizes.
- The topic parse refuses an index past the subnet count, a leading
  zero, a deprecated name, and a short digest (`#guard` checks in
  `Topic.lean`).

Unit 2 (`Tests/Eth2.lean`, two services over loopback):
- The boot record's peer connects, and the listener sees it inbound.
- Each side gets the other's `Status`: our digest, then the client's
  bytes.
- The block topic meshes, and a published block reaches the other side
  as a held message with the consensus message id. The answer posts.
- A range request gets three chunks in order, each with our digest as
  its context. A client that emits past the method's cap stops at
  `MAX_REQUEST_BLOCKS_DENEB`.
- A light-client request with no data gets `ResourceUnavailable`.
- MetaData v3 and v2 answer the client's bytes, and Ping answers the
  seq number. A new `Status` keeps our digest, and bytes of another
  width change nothing.
- The start refuses a `Status`, a `MetaData`, or a schedule of the wrong
  shape.
- The stop says Goodbye with reason 1, and the listener sees the peer
  leave.
- The suite passes on two threads and on one.

Unit 3 has two legs:
- The network leg: `eth2-probe` (`packages/cli/Eth2Probe.lean`) joins
  the devnet with the service alone, and needs no chain model. It takes
  its fork from the `eth2` field of a boot record. On
  `devnet/multi.yaml`, two Lighthouse nodes and one Grandine accepted
  its dials and exchanged `Status`, with our digest. Each answered
  `BeaconBlocksByRange` with our digest as the context bytes, and Ping
  and MetaData v3. Gossip arrived on the block, aggregate, attestation,
  and column topics. A column range at slots 0 and 1 gave no chunks,
  since those blocks carry no blobs.
- The model leg: the shadow node over this service on the devnet, with
  `shadow-node check` against the host node. The adapter belongs to
  `etheorem-shadow-node`, so this leg runs there.

Unit 4 (`Tests/Eth2.lean`):
- The table: an outbound peer is due for a Ping at 15 s and an inbound
  one at 20 s. A peer taken as due is not due again at once, and an
  inbound Ping counts as our check.
- An unknown or higher seq number is news, and a known one is not.
- A ban holds until its end, a second ban keeps the later end, and the
  table stays at 1000 bans.
- Over loopback: the first Ping of a peer brings its MetaData once, and
  an answered Ping raises no `unresponsive` event.
- A ban says Goodbye with reason 251, and the peer leaves. The gater
  refuses our dial to it, and its redials.

Unit 5 (`Tests/Eth2.lean`):
- The block, aggregate, attestation, and voluntary exit topics, and the
  global parameters, equal Lighthouse's formulas in Python's float64,
  at mainnet timing for 500000 validators at slot 100000.
- On a young chain, the mesh delivery terms are off, and the failure
  term stays.
- Every scored kind and the global parameters pass the validity check,
  and the router parameters meet the spec's constraints.
- A topic of our digest is scored. A column topic and a topic of another
  digest are not.
- Over loopback, `updateScores` posts all 66 topics.

Unit 6 (`Tests/Eth2.lean`):
- The schedule, around a fork at epoch 10: nothing at 8, the join at 9
  once, the switch at 10 with no second join, nothing at 11, and the
  retirement at 12. A fork the loop did not see ahead joins and switches
  at once.
- A live service on a chain of 2 s epochs: both digests carry the topic
  ahead of the fork, then `Status`, the record, and `topic` name the new
  digest, then the pre-fork topic goes. The `Status` keeps the client's
  other bytes.

Unit 7 (`Tests/Eth2.lean`):
- The group ID is `0x00` then the root, gives back its root, and an
  unknown version is ignored.
- The reward goes once per peer, block, and column, and the state keeps
  four blocks.
- Over loopback: a peer that requests partial columns is listed, the
  client's metadata and message reach it with the block root and the
  source, and a group ID of an unknown version raises no event.

A run of 600 s on the devnet without the spammer and assertoor, with
Lighthouse at the debug level: three peers stayed connected for the
whole run, 50 blocks arrived on gossip (one per slot), 235 aggregates,
and 1650 attestations. No frame dropped, and Lighthouse sent `Status`
again every 300 s. Before the loop fix of the gossipsub node, the loop
used one core in full and fell minutes behind, which explains the
session drop of the 120 s run. From about 384 s on, the peers pruned the
probe from many meshes. Their mesh delivery term starts one epoch in,
and the probe answers IGNORE to every message, so it forwards nothing.
A client that accepts valid messages forwards them.
