# leanp2p eth2: plan

The package's work units, in order. Each unit names its checks. The
package ARCHITECTURE holds the contracts, and the root documents bind
both.

## Units

1. **The pure layer.** The constants, `Chain` and the fork digest, the
   config reader, the topics, the message id, the ENR fields, the
   methods and the small messages, and the gossip parameters.
2. **The service.** The host with TCP and QUIC, gossipsub on the payload
   path with the held validation, discv5 with our record and the
   discovery loop, the `Status` duty, the answers to Ping, MetaData, and
   Goodbye, and the client's seams for gossip and for block and column
   requests.
3. **The live gate.** The shadow node over this service, on the Kurtosis
   devnet of `etheorem-shadow-node` (`devnet/multi.yaml`: two
   Lighthouse nodes and one Grandine), against the same agreement as
   its Rust path.

## Consumers

- `etheorem-shadow-node`: its p2p adapter maps the frame commands and
  events of `P2p/Frames.lean` onto `Service`.

## Test milestones

Unit 1 (`Tests/Eth2.lean`):
- The devnet config gives six forks after genesis, Fulu at epoch 0,
  the one blob schedule entry, and the mainnet epoch.
- The digest is `8049f250`, the value Python computes, and the record
  of a Lighthouse node of the devnet carries it.
- That record's whole `ENRForkID` and its `nfd` equal ours, and its
  `cgc` is a supernode's 128.
- A Blob-Parameters-Only entry is the next fork, changes the digest,
  keeps the version, and gives `nfd`.
- Before Fulu, the digest is the plain fork data root.
- The message id of data that does not decompress, and of compressed
  data, equal the values of Python's `hashlib`. The topic enters the
  id.
- `Status` v2 has 92 bytes and reads back, and 84 bytes are refused.
  `MetaData` v3 has 25 bytes and v2 17.
- The topic parse refuses an index past the subnet count, a leading
  zero, a deprecated name, and a short digest (`#guard` checks in
  `Topic.lean`).

Unit 2 (`Tests/Eth2.lean`, two services over loopback):
- The boot record's peer connects, and the listener sees it inbound.
- Each side gets the other's `Status`.
- The block topic meshes, and a published block reaches the other side
  as a held message with the consensus message id. The answer posts.
- A range request gets three chunks in order, each with our digest as
  its context.
- MetaData v3 names the custody, and Ping answers the seq number.
- The stop says Goodbye with reason 1, and the listener sees the peer
  leave.
- The suite passes on two threads and on one.

Unit 3 has two legs:
- The network leg: `eth2-probe` (`packages/cli/Eth2Probe.lean`) joins
  the devnet with the service alone, and needs no chain model. On
  `devnet/multi.yaml`, two Lighthouse nodes and one Grandine accepted
  its dials and exchanged `Status`, with our digest. Each answered
  `BeaconBlocksByRange` with our digest as the context bytes, and Ping
  and MetaData v3. Gossip arrived on the block, aggregate, attestation,
  and column topics. A column range at slots 0 and 1 gave no chunks,
  since those blocks carry no blobs.
- The model leg: `shadow_node_lean` on the devnet, with `shadow-node
  check` against the host node.

Open from the network leg: in a run of 120 s, one Lighthouse node
ended our session once, and the discovery loop dialed it again. Its
log at the info level names no reason. A run with Lighthouse at the
debug level finds the cause.
