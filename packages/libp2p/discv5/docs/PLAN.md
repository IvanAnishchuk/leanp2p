# leanp2p discv5: plan

This plan refines the root `docs/PLAN.md` for `libp2p/discv5`. The root
plan has no unit for it yet: it calls discv5 out of scope (root PLAN
W6.1, ARCHITECTURE §8). The spike on `experiment/client` built it,
because a consensus node finds its peers through it, and the units
below record that work for the root plan to take in.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair | written, and consistent with the root docs |
| 1 | W6.1, W3.2 | the packet codec and the handshake crypto (`Packet.lean`) | the wire test vectors pass |
| 2 | unit 1 | the messages over the RLP, with the round-trip theorem (`Message.lean`) | the theorem holds with no `sorry`, and the vectors decode through it |
| 3 | unit 2 | the node table and the core (`Table.lean`, `Core.lean`) | two cores handshake and answer in memory |
| 4 | unit 3, W4.1 | the node over UDP (`Node.lean`): the lookup, revalidation, the rate limit, IPv6 | the conformance suites below pass |

All four units are done on `experiment/client`.

## Consumers

A consensus client calls `findPeers` with a predicate over records, a
fork-digest match on `eth2` and a subnet match on `attnets` or
`syncnets`, and dials what comes back through the host. The ENR side of
`libp2p/identity` maps each record to a peer id and a multiaddr.

## Test milestones

`Tests/Discv5.lean`, run alone with `LEANP2P_SUITE=discv5`:

- The wire vectors of `discv5-wire-test-vectors.md` (devp2p at
  `2c19a28`): the four packets unmask, open, and decode at node B, and
  the four crypto vectors (ECDH, key derivation, id signature,
  AES-GCM) match. Our encoder writes the vector PING's bytes.
- Two cores in memory: the handshake in both roles, PING and PONG,
  FINDNODE and NODES, TALKREQ and TALKRESP, the votes and their expiry.
- The geth scenarios, replayed in memory: the session bound to its
  endpoint, the resent challenge, the FINDNODE inside a handshake, the
  oversized request id, the empty-id TALKREQ, the unsolicited NODES and
  PONG, the distance filter, the live-only relay, the NODES packet cap,
  and the session cache bound.
- The policies: the /24 limits, the incoming limit, and the rate
  limiter.
- Real sockets: two nodes over UDP, over IPv6, the TALK handler, and
  the liveness checks, with a record pull on a higher `seq`.

The conformance runs are outside `lake test`, which stays free of Go
and Rust tooling:

- `scripts/discv5-geth-interop.sh`: geth's ten `v5test` scenarios
  against our node, then our client against a geth node.
- `scripts/discv5-rust-interop.sh`: the sigp crate 0.12.0 in both
  directions.

## Vector stance

The wire vectors are copied into `Tests/Discv5.lean` from the devp2p
clone at `2c19a28`; a pinned vendor copy and a `VECTORS.lock` entry come
with the root unit. The conformance harnesses pin their upstream code
by commit (geth) and by exact crate version with a lock file (sigp).
