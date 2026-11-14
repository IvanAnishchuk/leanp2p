# leanp2p discv5: architecture

`libp2p/discv5` is Node Discovery v5, protocol version v5.1 (devp2p
`discv5/discv5-wire.md` and `discv5-theory.md`). The consensus
networking spec names it as the discovery domain (phase0
`p2p-interface.md`, "The discovery domain: discv5"), and every
consensus client runs it: Prysm through go-ethereum's `p2p/discover`,
Lighthouse through the sigp `discv5` crate. A consensus node finds its
peers here, then dials them over libp2p. discv5 itself speaks no
libp2p.

The package is in the libp2p group, at the rank of `core`. It imports
`libp2p/identity` for the ENR and the RLP, and nothing else of the
group. The spike on `experiment/client` holds it. The root ARCHITECTURE
§8 has its row, and the root PLAN has no unit for it.

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Discv5.lean` | the root module, with one import line per public submodule |
| `Libp2p/Discv5/Packet.lean` | the packet codec: masking with AES-128-CTR, the static header, the message seal and open with AES-128-GCM, and the handshake crypto (ECDH, the HKDF key derivation, the id signature) |
| `Libp2p/Discv5/Message.lean` | the six messages a consensus node uses, over the package-owned RLP, with the round-trip theorem |
| `Libp2p/Discv5/Table.lean` | the Kademlia node table: 256 buckets of 16, the replacement caches, the liveness marks, and the eclipse limits |
| `Libp2p/Discv5/Core.lean` | the pure protocol core: sessions, the WHOAREYOU handshake in both roles, the answers, the request bookkeeping, and the endpoint votes |
| `Libp2p/Discv5/Node.lean` | the IO shell: the UDP socket, the randomness, the waits, the rate limit, the lookup, and the maintenance tasks |

All declarations live in the `Libp2p.Discv5` namespace.

## Public surface

- `Message` holds PING, PONG, FINDNODE, NODES, TALKREQ, and TALKRESP.
  The package leaves out the topic messages: consensus finds subnet
  peers through the record's `attnets` and `syncnets`. `encode` and
  `decode?` are the production path. Each one converts the bytes once
  and calls the model codec.
- `Packet` holds `unmask`, `mask`, `openMessage`, `sealMessage`,
  `deriveKeys`, `idSign`, and `idVerify`.
- `Core.step` is one total transition, `State → Event → State × List
  Action`. The events are a datagram, a request to send, a request to
  forget, the application's TALKRESP, and the clock. The actions are a
  datagram to send, a response for a waiter, and a TALKREQ for the
  application. Every event carries the random bytes it may use, so the
  core makes no choice of its own and a test replays it.
- `Node.start` binds the socket (IPv4 or IPv6), signs the local record,
  and starts the reader and the revalidation task. A running node
  offers these calls:
  - `ping`, `findNode`, and `talk`, one request each
  - `lookup`, with α = 3 concurrent queries
  - `findPeers`, the consensus interface: a lookup toward a random
    target, with the client's predicate over the records it finds
  - `addEnr`, `known`, `localEnr`, `updateEnr`, and `votes`, for the
    table and the local record
  - `stop`

## Owned contracts and how the package keeps them

1. **A session belongs to one endpoint.** A packet from another
   endpoint, or one that does not open, gets a WHOAREYOU
   (`discv5-theory.md`, "Sessions"). The core sends a challenge that is
   still pending for that endpoint again, unchanged, so the peer can
   finish the first handshake (geth `v5test`, `HandshakeResend`).
2. **No nonce repeats under one key.** Each session counts the messages
   sent under its write key, and the count is the first 32 bits of the
   nonce (`discv5-theory.md`, "Session Cache").
3. **Only solicited answers count.** The core keeps each request by id
   until its answer ends or the shell posts `forget`. The geth `v5test`
   scenarios `UnsolicitedNodes` and `FindnodeResults` check three rules:
   - An unsolicited PONG or NODES changes nothing.
   - A NODES answer counts only at the distances that the request asked.
   - At most `maxNodesPackets` packets answer one request.
4. **The table holds live nodes.** FINDNODE answers relay only entries
   that passed a liveness check. The revalidation task pings one entry
   per round, removes a node that fails, and promotes its replacement. A
   PONG with a higher `enr-seq` pulls the newer record
   (`discv5-theory.md`, "Table Maintenance In Practice").
5. **The record follows the votes.** The `recipient-ip` and
   `recipient-port` of each PONG are one vote for our external endpoint.
   Each voter has one vote, and it stays valid for `voteTtl` (120 s) on
   the shell's clock. When `voteQuorum`
   (10) voters name an endpoint the record does not hold, the core
   re-signs the record with that endpoint and the next `seq`.
6. **Bounded state.** The limits:
   - The session cache and the pending challenges each hold at most
     1000 entries, and drop the least recently used.
   - A /24 of global IPv4 addresses holds at most 2 places in a bucket,
     and 10 in the table.
   - Nodes that contacted us take at most 8 places of a bucket.
   - Unsolicited packets pass at 10 per second in all, and at 9 per
     second from one IP. Loopback is exempt.

   Theorems state each limit:
   - `Table.insertOverSubnet`, with `overSubnetBucket` and
     `overSubnetTable`: a new node past a /24 limit leaves the table
     unchanged.
   - `insertNoRoom`, with `overIncomingFull`: a full bucket, or one at
     the incoming limit, takes no new node into its entries.
   - `limitStepTotal`, `limitStepPerIp`, and `limitStepRefused`: the
     counts of the rate limiter.
7. **The codec round-trips.** `Message.decodeEncode` proves
   `decodeModel? (encodeModel m) = some m` for every well-formed message
   a node builds itself, and `decodeEncodeBytes` carries it to the
   `ByteArray` path. NODES is the exception. Its records decode through
   `Enr.decode?`, which verifies a secp256k1 signature over the FFI. So
   the wire vectors and the conformance suites check NODES (CLAUDE.md,
   "Proofs and tests", rule 3).

## Decisions

- **The policies follow Lighthouse.** The spec leaves the eclipse
  limits, the rate limits, the retry count, and the vote window to the
  implementation. The package takes the sigp crate's numbers as
  Lighthouse configures them:
  - the /24 limits: 2 per bucket and 10 per table
  - the incoming bucket limit: 8
  - the unsolicited rate: 10 per second, and 9 per IP
  - one request retry
  - the vote window: 120 s
  - the vote quorum: `enr_peer_update_min`, 10
- **The lookup is the spec's.** α = 3 queries run at once toward the
  target, each asking for the log distances around it, until the `k`
  closest known nodes have all answered. A refresh lookup toward a
  random target runs every `refreshEvery` revalidation rounds.
- **TALKREQ goes to the application.** The node's `onTalk` handler
  answers each request. For an unknown protocol, it answers the empty
  TALKRESP that `discv5-wire.md` requires. The handler runs on the reader task,
  so it must not park.
- **Time and randomness stay in the shell.** The core reads neither.
  The shell posts `clock` events and hands every event its random bytes,
  so the theorems and the replay tests see a pure function.

## Conformance

- go-ethereum's `devp2p discv5 test` (`v5test`), the suite of the
  `p2p/discover` code that Prysm runs. All ten scenarios pass against
  our node (`scripts/discv5-geth-interop.sh`, geth at `0d06140`). The same script
  queries a geth node (`devp2p discv5 listen`) from ours.
- The sigp `discv5` crate 0.12.0, Lighthouse's discovery: a PING, a
  FINDNODE at distance 0, and a TALKREQ pass in both directions
  (`scripts/discv5-rust-interop.sh`).

## What the package must not depend on

- Nothing of the libp2p group beside `libp2p/identity`: no seam type,
  no host, no `ProtocolId`. discv5 runs beside the host, and the client
  joins the two.
- From net, `net/streams` for its UDP socket only.
- From crypto, the `Crypto` facade only (§3.6): AES-128-CTR,
  AES-128-GCM, HKDF-SHA256, secp256k1 ECDH, the digest signer, and key
  recovery.
- No Go or Rust code: the conformance harnesses are test-only and stay
  under `scripts/`.
