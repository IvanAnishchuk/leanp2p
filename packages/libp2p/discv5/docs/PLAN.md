# leanp2p discv5: plan

This plan refines the root `docs/PLAN.md` for `libp2p/discv5`. The root
plan has no unit for it, and root W6.1 keeps discv5 out of scope. A
consensus node finds its peers through discv5, so the spike on
`experiment/client` holds the package. The units below are the input
for a root unit.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair | written, and consistent with the root docs |
| 1 | W6.1, W3.2 | the packet codec and the handshake crypto (`Packet.lean`) | the wire test vectors pass |
| 2 | unit 1 | the messages over the RLP, with the round-trip theorem (`Message.lean`) | the theorem holds with no `sorry`, and the vectors decode through it |
| 3 | unit 2 | the node table and the core (`Table.lean`, `Core.lean`) | two cores handshake and answer in memory |
| 4 | unit 3, W4.1 | the node over UDP (`Node.lean`): the lookup, revalidation, the rate limit, IPv6 | the conformance suites below pass |

All five units are done on `experiment/client`.

## Consumers

A consensus client calls `findPeers` with a predicate over records. The
predicate matches the fork digest in `eth2` and a subnet in `attnets` or
`syncnets`. The client dials the records that `findPeers` returns
through the host. The ENR side of `libp2p/identity` maps each record to
a peer id and a multiaddr.

## Test milestones

`Tests/Discv5.lean`, run alone with `LEANP2P_SUITE=discv5`:

- The wire vectors of `discv5-wire-test-vectors.md` (devp2p at
  `2c19a28`). The four packets unmask, open, and decode at node B. The
  four crypto vectors match: ECDH, key derivation, id signature, and
  AES-GCM. Our encoder writes the bytes of the vector PING.
- Two cores in memory: the handshake in both roles, PING and PONG,
  FINDNODE and NODES, TALKREQ and TALKRESP, the votes and their expiry.
- The geth scenarios, replayed in memory: the session bound to its
  endpoint, the resent challenge, the FINDNODE inside a handshake, the
  oversized request id, the empty-id TALKREQ, the unsolicited NODES and
  PONG, the distance filter, the live-only relay, the NODES packet cap,
  and the session cache bound.
- The policies: the /24 limits, the incoming limit, and the rate
  limiter, each with a theorem in `Table.lean` or `Node.lean` and a
  check in the suite.
- Real sockets: two nodes over UDP, over IPv6, the TALK handler, and
  the liveness checks, with a record pull on a higher `seq`.
- A lost datagram: a relay between two nodes drops the first PINGs.
  After one loss, the retry still gets the PONG. After two losses, the
  request ends. So the node sends a request at most twice
  (`Node.requestRetries`).

The conformance runs are outside `lake test`, which stays free of Go
and Rust tooling:

- `scripts/discv5-geth-interop.sh`: geth's ten `v5test` scenarios
  against our node, then our client against a geth node.
- `scripts/discv5-rust-interop.sh`: the sigp crate 0.12.0 in both
  directions.

## Vector stance

`VECTORS.lock` pins `vendor/devp2p` at `2c19a28`, with the test vector
file alone, since the repository has no license file.
`scripts/extract-vectors.py` extracts it to
`Tests/vectors/discv5-wire.json`, and the suite reads that file. The
conformance harnesses pin their upstream code by commit (geth), and by
exact crate version with a lock file (sigp).
