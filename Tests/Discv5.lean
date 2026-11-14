import Tests.Support
import Libp2p.Discv5

/-!
# discv5 suite: the wire test vectors

Mirrors devp2p `discv5/discv5-wire-test-vectors.md` (devp2p at
`2c19a28`, the clone at `../p2p/devp2p`): the four packet encodings,
which node B unmasks, opens, and decodes, and the four crypto vectors
(ECDH, key derivation, id signature, AES-GCM). The vectors are copied
here by hand for the spike; a pinned vendor copy and `VECTORS.lock`
entry come with the real unit.
-/

set_option autoImplicit false

namespace Tests.Discv5

open Libp2p.Discv5

private def hex (s : String) : ByteArray := (Bytes.ofHex? s).getD .empty

private def key32 (s : String) : Option Crypto.Key32 := Crypto.Key32.ofByteArray? (hex s)
private def key16 (s : String) : Option Crypto.Key16 := Crypto.Key16.ofByteArray? (hex s)

private def nodeBKey := "66fb62bfbd66b9177a138c1e5cddbe4f7c30c343e94e68df8769459cb1cde628"
private def srcId := hex "aaaa8419e9f49d0083561b48287df592939a8d19947d8c0ef88f2a4856a69fbb"
private def destId := hex "bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9"

private def pingPacket := hex ("00000000000000000000000000000000088b3d4342774649325f313964a39e55" ++
  "ea96c005ad52be8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3" ++
  "4c4f53245d08dab84102ed931f66d1492acb308fa1c6715b9d139b81acbdcc")

private def whoareyouPacket := hex ("00000000000000000000000000000000088b3d434277464933a1ccc59f5967ad" ++
  "1d6035f15e528627dde75cd68292f9e6c27d6b66c8100a873fcbaed4e16b8d")

private def handshakePacket := hex ("00000000000000000000000000000000088b3d4342774649305f313964a39e55" ++
  "ea96c005ad521d8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3" ++
  "4c4f53245d08da4bb252012b2cba3f4f374a90a75cff91f142fa9be3e0a5f3ef" ++
  "268ccb9065aeecfd67a999e7fdc137e062b2ec4a0eb92947f0d9a74bfbf44dfb" ++
  "a776b21301f8b65efd5796706adff216ab862a9186875f9494150c4ae06fa4d1" ++
  "f0396c93f215fa4ef524f1eadf5f0f4126b79336671cbcf7a885b1f8bd2a5d83" ++
  "9cf8")

private def challengeData (enrSeq : String) := hex
  ("000000000000000000000000000000006469736376350001010102030405060708090a0b0c" ++
   "00180102030405060708090a0b0c0d0e0f10" ++ enrSeq)

/-- The decoded PING of a packet, through the node's own decoder:
`(type, request-id, enr-seq)`. -/
private def pingOf (pt : ByteArray) : Option (UInt8 × List Nat × Nat) :=
  match Message.decode? pt with
  | some (.ping rid seq) => some (1, rid, seq)
  | _ => none

/-! ## Two cores, in memory -/

/-- Deterministic "random" bytes for event `n`: a counter pattern, long
enough for `randLen`. The ephemeral key slice (bytes 44 to 75) is a
valid secp256k1 scalar for every `n` used here. -/
private def randFor (n : Nat) : ByteArray :=
  ⟨(Array.range randLen).map fun i => ((i * 7 + n * 13 + 1) % 251 + 1).toUInt8⟩

/-- Deliver every send among the two cores until none is left, and
collect the responses each one reports. `fuel` bounds the rounds. -/
private def settle (a b : State) (epA epB : Endpoint) (acts : List (Bool × Action)) (fuel : Nat)
    (n : Nat) : State × State × List (Bool × Message) := Id.run do
  let mut a := a
  let mut b := b
  let mut queue := acts
  let mut got : List (Bool × Message) := []
  let mut k := n
  for _ in [0:fuel] do
    match queue with
    | [] => break
    | (fromA, act) :: rest =>
      queue := rest
      match act with
      | .response _ m => got := got ++ [(fromA, m)]
      -- The shell's default for a TALKREQ: an empty TALKRESP, from the
      -- core that took the request.
      | .talk src rid _ _ =>
        k := k + 1
        if fromA then
          let (a', out) := Core.step a (.respond src (.talkResp rid []) (randFor k))
          a := a'
          queue := queue ++ out.map (true, ·)
        else
          let (b', out) := Core.step b (.respond src (.talkResp rid []) (randFor k))
          b := b'
          queue := queue ++ out.map (false, ·)
      | .send _ bytes =>
        k := k + 1
        if fromA then
          let (b', out) := Core.step b (.packet epA bytes (randFor k))
          b := b'
          queue := queue ++ out.map (false, ·)
        else
          let (a', out) := Core.step a (.packet epB bytes (randFor k))
          a := a'
          queue := queue ++ out.map (true, ·)
  return (a, b, got)

/-- The datagrams an action list sends. -/
private def sendsOf (acts : List Action) : List (Endpoint × ByteArray) :=
  acts.filterMap fun a => match a with
    | .send d b => some (d, b)
    | _ => none

/-- The packet kind of a datagram sent to the node `localId`. -/
private def flagFor (localId : ByteArray) (b : ByteArray) : Option Flag :=
  (unmask localId b).toOption.map (·.header.flag)

/-- The header nonce of a datagram sent to the node `localId`. -/
private def nonceFor (localId : ByteArray) (b : ByteArray) : Option (List UInt8) :=
  (unmask localId b).toOption.map (·.header.nonce.toList)

/-- The one datagram of an action list. -/
private def onlySend (acts : List Action) : Option ByteArray :=
  match sendsOf acts with
  | [(_, b)] => some b
  | _ => none

private def memoryChecks (r : Runner) : IO Unit := do
  let some ka := key32 "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f"
    | r.check "discv5 memory: key A" false
  let some kb := key32 nodeBKey | r.check "discv5 memory: key B" false
  let epA : Endpoint := { ip := [127, 0, 0, 1], port := 9001 }
  let epB : Endpoint := { ip := [127, 0, 0, 1], port := 9002 }
  let pairs (ep : Endpoint) : List Libp2p.Identity.Enr.Pair :=
    [⟨.ip, .bytes ep.ip⟩, ⟨.udp, .bytes (Libp2p.Identity.Rlp.ofScalar ep.port)⟩]
  match Libp2p.Identity.Enr.sign ka 1 (pairs epA), Libp2p.Identity.Enr.sign kb 1 (pairs epB) with
  | .ok ea, .ok eb =>
    let a0 := Core.init ka ea
    let b0 := Core.init kb eb
    -- The first PING has no session: B answers WHOAREYOU, A sends the
    -- handshake, and B's PONG comes back in the new session.
    let (a1, out) := Core.step a0 (.request eb epB (.ping [1] 1) (randFor 0))
    let (a2, b2, got) := settle a1 b0 epA epB (out.map (true, ·)) 20 0
    r.check "discv5 memory: the first PING runs the handshake and gets its PONG"
      (got.any fun (toA, m) => toA && match m with
        | .pong [1] 1 ip port => ip == [127, 0, 0, 1] && port == 9001
        | _ => false)
    r.check "discv5 memory: both sides hold a session"
      ((a2.sessions.get? (idNat eb.nodeId)).isSome && (b2.sessions.get? (idNat ea.nodeId)).isSome)
    r.check "discv5 memory: B learned A's record from the handshake"
      (b2.table.entries.any (·.id == ea.nodeId))
    r.check "discv5 memory: A recorded B's view of its endpoint" (a2.votes.any (·.endpoint == epA))
    -- A second request goes straight through the session: one packet
    -- each way.
    let (a3, out) := Core.step a2 (.request eb epB (.findNode [2] [0]) (randFor 100))
    r.check "discv5 memory: a session request is one packet" (out.length == 1)
    let (a4, _, got) := settle a3 b2 epA epB (out.map (true, ·)) 20 100
    r.check "discv5 memory: FINDNODE at distance 0 returns B's record"
      (got.any fun (toA, m) => toA && match m with
        | .nodes [2] 1 [e] => e.nodeId == eb.nodeId
        | _ => false)
    r.check "discv5 memory: A's table holds B after NODES" (a4.table.entries.any (·.id == eb.nodeId))
    -- Endpoint votes: below the quorum the record stays; at the quorum
    -- it names the voted endpoint under the next seq.
    let outside : Endpoint := { ip := [203, 0, 113, 7], port := 30303 }
    let vote (k : Nat) : Vote := { voter := k, endpoint := outside, at_ := 0 }
    let few := Core.refreshRecord { a0 with votes := (List.range (Core.voteQuorum - 1)).map vote }
    r.check "discv5 votes: fewer than the quorum leave the record" (few.localEnr.seq == 1)
    let many := Core.refreshRecord { a0 with votes := (List.range Core.voteQuorum).map vote }
    r.check "discv5 votes: the quorum re-signs the record under seq 2" (many.localEnr.seq == 2)
    r.check "discv5 votes: the new record names the voted endpoint"
      (endpointOf? many.localEnr == some outside)
    r.check "discv5 votes: the node id stays" (many.localEnr.nodeId == ea.nodeId)
    let again := Core.refreshRecord many
    r.check "discv5 votes: a record that holds the endpoint stays" (again.localEnr.seq == 2)
    -- Votes expire after `voteTtl`: a quorum cast at time 0 counts at
    -- `voteTtl` and not one millisecond later.
    let quorum := (List.range Core.voteQuorum).map vote
    r.check "discv5 votes: a quorum still in time counts"
      ((Core.refreshRecord { a0 with votes := quorum, now := Core.voteTtl }).localEnr.seq == 2)
    r.check "discv5 votes: an expired quorum does not count"
      ((Core.refreshRecord { a0 with votes := quorum, now := Core.voteTtl + 1 }).localEnr.seq == 1)
    let (cleared, _) := Core.step { a0 with votes := quorum } (.clock (Core.voteTtl + 1))
    r.check "discv5 votes: the clock drops expired votes" cleared.votes.isEmpty
    -- TALKREQ goes up to the application; its answer comes back through
    -- `Event.respond` and leaves in the session.
    let (a5, out) := Core.step a4 (.request eb epB (.talkReq [12] [0x65] [1, 2]) (randFor 120))
    match onlySend out with
    | some p =>
      let (b5, bOut) := Core.step b2 (.packet epA p (randFor 121))
      r.check "TALKREQ goes up to the application, and nothing answers by itself"
        (bOut.any (fun a => match a with
          | .talk src [12] [0x65] [1, 2] => src.toList == ea.nodeId.toList
          | _ => false) && (sendsOf bOut).isEmpty)
      let (_, rOut) := Core.step b5 (.respond ea.nodeId (.talkResp [12] [7, 7]) (randFor 122))
      match onlySend rOut with
      | some q =>
        let (_, aOut) := Core.step a5 (.packet epB q (randFor 123))
        r.check "the application's TALKRESP reaches the asker"
          (aOut.any fun a => match a with
            | .response _ (.talkResp [12] [7, 7]) => true
            | _ => false)
      | none => r.check "the TALKRESP is one packet" false
    | none => r.check "TALKREQ: A sends one packet" false
  | _, _ => r.check "discv5 memory: the records sign" false

/-! ## geth's conformance scenarios

The behaviours geth's discv5 test suite checks against a node
(`cmd/devp2p/internal/v5test/discv5tests.go`, go-ethereum `0d06140`),
played here with our own core as the tester. -/

private def gethChecks (r : Runner) : IO Unit := do
  let some ka := key32 "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f"
    | r.check "geth: key A" false
  let some kb := key32 nodeBKey | r.check "geth: key B" false
  let some kc := key32 "fb757dc581730490a1d7a00deea65e9b1936924caaea8f44d476014856b68736"
    | r.check "geth: key C" false
  let epA : Endpoint := { ip := [127, 0, 0, 1], port := 9001 }
  let epA2 : Endpoint := { ip := [127, 0, 0, 3], port := 9001 }
  let epB : Endpoint := { ip := [127, 0, 0, 1], port := 9002 }
  let epC : Endpoint := { ip := [127, 0, 0, 1], port := 9003 }
  let pairs (ep : Endpoint) : List Libp2p.Identity.Enr.Pair :=
    [⟨.ip, .bytes ep.ip⟩, ⟨.udp, .bytes (Libp2p.Identity.Rlp.ofScalar ep.port)⟩]
  let sign (k : Crypto.Key32) (ep : Endpoint) := Libp2p.Identity.Enr.sign k 1 (pairs ep)
  match sign ka epA, sign kb epB, sign kc epC with
  | .ok ea, .ok eb, .ok ec =>
    let a0 := Core.init ka ea
    let b0 := Core.init kb eb
    -- A session between A at epA and B.
    let (a1, out) := Core.step a0 (.request eb epB (.ping [1] 1) (randFor 0))
    let (a2, b2, _) := settle a1 b0 epA epB (out.map (true, ·)) 20 0

    -- PingMultiIP: the session's packet from another IP draws WHOAREYOU.
    let (a3, out) := Core.step a2 (.request eb epB (.ping [2] 1) (randFor 300))
    match onlySend out with
    | some p =>
      -- The handshake packet was message 0 of A's write key, so this
      -- one carries count 1 in its first 32 bits.
      r.check "session nonces carry the message count"
        ((nonceFor eb.nodeId p).map (·.take 4) == some [0, 0, 0, 1])
      let (_, bOut) := Core.step b2 (.packet epA2 p (randFor 301))
      r.check "geth PingMultiIP: a session packet from another IP draws WHOAREYOU, not PONG"
        (match sendsOf bOut with
         | [(d, q)] => d == epA2 && flagFor ea.nodeId q == some .whoareyou
         | _ => false)
      let (_, bOut') := Core.step b2 (.packet epA p (randFor 302))
      r.check "geth PingMultiIP: the same packet from the session's IP opens"
        (match sendsOf bOut' with
         | [(_, q)] => flagFor ea.nodeId q == some .message
         | _ => false)
    | none => r.check "geth PingMultiIP: A sends one packet" false

    -- FindnodeWrongIP: FINDNODE from another IP gets a challenge.
    let (_, out) := Core.step a3 (.request eb epB (.findNode [3] [0]) (randFor 310))
    match onlySend out with
    | some p =>
      let (_, bOut) := Core.step b2 (.packet epA2 p (randFor 311))
      r.check "geth FindnodeWrongIP: FINDNODE from another IP draws WHOAREYOU, not NODES"
        (match sendsOf bOut with
         | [(_, q)] => flagFor ea.nodeId q == some .whoareyou
         | _ => false)
    | none => r.check "geth FindnodeWrongIP: A sends one packet" false

    -- HandshakeResend: a second packet before the handshake gets the
    -- first WHOAREYOU again, byte for byte.
    let (a4, out1) := Core.step a0 (.request eb epB (.ping [4] 1) (randFor 320))
    let (_, out2) := Core.step a4 (.request eb epB (.ping [5] 1) (randFor 321))
    match onlySend out1, onlySend out2 with
    | some p1, some p2 =>
      let (b5, w1) := Core.step b0 (.packet epA p1 (randFor 322))
      let (_, w2) := Core.step b5 (.packet epA p2 (randFor 323))
      r.check "geth HandshakeResend: the second packet gets the first challenge again"
        (match onlySend w1, onlySend w2 with
         | some x, some y => x.toList == y.toList && flagFor ea.nodeId x == some .whoareyou
         | _, _ => false)
    | _, _ => r.check "geth HandshakeResend: A sends two packets" false

    -- FindnodeHandshake: a FINDNODE as the first packet draws WHOAREYOU
    -- with that packet's nonce, and NODES after the handshake.
    let (a6, out) := Core.step a0 (.request eb epB (.findNode [6] [0]) (randFor 330))
    match onlySend out with
    | some p =>
      let (_, w) := Core.step b0 (.packet epA p (randFor 331))
      r.check "geth FindnodeHandshake: the WHOAREYOU carries the FINDNODE's nonce"
        (match onlySend w with
         | some q => (nonceFor eb.nodeId p).isSome && nonceFor ea.nodeId q == nonceFor eb.nodeId p
         | none => false)
      let (_, _, got) := settle a6 b0 epA epB (out.map (true, ·)) 20 330
      r.check "geth FindnodeHandshake: NODES with the request id follows the handshake"
        (got.any fun (toA, m) => toA && match m with
          | .nodes [6] _ _ => true
          | _ => false)
    | none => r.check "geth FindnodeHandshake: A sends one packet" false

    -- PingLargeRequestID: a 9-byte request id draws no answer.
    let (_, out) := Core.step a2 (.request eb epB (.ping [1, 2, 3, 4, 5, 6, 7, 8, 9] 1) (randFor 340))
    match onlySend out with
    | some p =>
      let (_, bOut) := Core.step b2 (.packet epA p (randFor 341))
      r.check "geth PingLargeRequestID: a 9-byte request id draws no answer" bOut.isEmpty
    | none => r.check "geth PingLargeRequestID: A sends one packet" false

    -- TalkRequest: an empty TALKRESP, also for an empty request id.
    let (a7, out) := Core.step a2 (.request eb epB (.talkReq [] [0x74] []) (randFor 350))
    let (_, _, got) := settle a7 b2 epA epB (out.map (true, ·)) 20 350
    r.check "geth TalkRequest: an empty request id gets an empty TALKRESP"
      (got.any fun (toA, m) => toA && match m with
        | .talkResp [] [] => true
        | _ => false)

    -- UnsolicitedNodes: a NODES nobody asked for plants nothing and draws
    -- no contact.
    let (_, out) := Core.step a2 (.request eb epB (.nodes [7] 1 [ec]) (randFor 360))
    match onlySend out with
    | some p =>
      let (b8, bOut) := Core.step b2 (.packet epA p (randFor 361))
      r.check "geth UnsolicitedNodes: an unasked NODES draws nothing"
        (bOut.isEmpty)
      r.check "geth UnsolicitedNodes: the injected record stays out of the table"
        (!(b8.table.entries.any (·.id == ec.nodeId)))
    | none => r.check "geth UnsolicitedNodes: A sends one packet" false

    -- An unasked PONG casts no endpoint vote.
    let (_, out) := Core.step b2 (.request ea epA (.pong [8] 1 [9, 9, 9, 9] 1) (randFor 370))
    match onlySend out with
    | some p =>
      let (a9, _) := Core.step a2 (.packet epB p (randFor 371))
      r.check "an unasked PONG casts no endpoint vote"
        (a9.votes.length == a2.votes.length)
    | none => r.check "an unasked PONG: B sends one packet" false

    -- NODES keep only the records at the distances asked. A asks B for
    -- distance 1, and B answers with C, which sits at another distance.
    let dC := logDistance ec.nodeId eb.nodeId
    let wrong := if dC = 1 then 2 else 1
    let (a10, _) := Core.step a2 (.request eb epB (.findNode [9] [wrong]) (randFor 380))
    let (_, out) := Core.step b2 (.request ea epA (.nodes [9] 1 [ec]) (randFor 381))
    match onlySend out with
    | some p =>
      let (a11, aOut) := Core.step a10 (.packet epB p (randFor 382))
      r.check "NODES drop a record at a distance not asked"
        (!(a11.table.entries.any (·.id == ec.nodeId)) &&
          aOut.any fun act => match act with
            | .response _ (.nodes [9] _ []) => true
            | _ => false)
    | none => r.check "NODES at a wrong distance: B sends one packet" false
    -- FINDNODE relays only live nodes: C, known to B but never pinged,
    -- stays out of the answer until it is marked live.
    let dC := logDistance ec.nodeId eb.nodeId
    let bKnows : State := { b2 with table := b2.table.insert { id := ec.nodeId, record := ec } }
    let askC (b : State) (rid : List Nat) (n : Nat) : Bool := Id.run do
      let (a', out) := Core.step a2 (.request eb epB (.findNode rid [dC]) (randFor n))
      let (_, _, got) := settle a' b epA epB (out.map (true, ·)) 20 n
      return got.any fun (toA, m) => toA && match m with
        | .nodes _ _ rs => rs.any (·.nodeId == ec.nodeId)
        | _ => false
    r.check "FINDNODE does not relay a node not yet live" (!askC bKnows [10] 390)
    r.check "FINDNODE relays a live node"
      (askC { bKnows with table := bKnows.table.markLive ec.nodeId } [11] 395)

    -- The NODES packet cap: an answer that claims 255 packets ends after
    -- `maxNodesPackets`, so a peer cannot hold the request open.
    let (a12, _) := Core.step a2 (.request eb epB (.findNode [12] [1]) (randFor 397))
    let (_, _, responses) := (List.range (Core.maxNodesPackets + 1)).foldl
      (fun (acc : State × State × Nat) i =>
        let (a, b, count) := acc
        let (b', out) := Core.step b (.request ea epA (.nodes [12] 255 []) (randFor (400 + 2 * i)))
        match onlySend out with
        | some p =>
          let (a', aOut) := Core.step a (.packet epB p (randFor (401 + 2 * i)))
          let answered := aOut.any fun act => match act with
            | .response _ (.nodes [12] _ _) => true
            | _ => false
          (a', b', if answered then count + 1 else count)
        | none => (a, b', count))
      (a12, b2, 0)
    r.check "NODES: an answer ends after maxNodesPackets packets"
      (responses == Core.maxNodesPackets)

    -- The session cache is bounded: past `maxSessions`, the least
    -- recently used session goes.
    match Crypto.Key16.ofByteArray? (ByteArray.mk (Array.replicate 16 0)) with
    | some k =>
      let idOf (i : Nat) : ByteArray :=
        ByteArray.mk ((List.range 32).map fun j => if j = 31 then (i % 256).toUInt8 else if j = 30 then (i / 256).toUInt8 else 1).toArray
      let ses : Session := { readKey := k, writeKey := k, endpoint := epA }
      let full := (List.range (Core.maxSessions + 1)).foldl
        (fun (s : State) i => Core.putSession { s with tick := i } (idOf i) ses) b0
      r.check "the session cache stays at maxSessions"
        (full.sessions.size == Core.maxSessions)
      r.check "the least recently used session went first"
        (!(full.sessions.contains (idNat (idOf 0))) && full.sessions.contains (idNat (idOf Core.maxSessions)))
    | none => r.check "a 16-byte key" false
  | _, _, _ => r.check "geth: the records sign" false

/-! ## Three nodes over UDP on the loopback -/

/-- The `eth2` key: a pair a consensus client adds to its record. -/
private def eth2Key : Libp2p.Identity.Enr.Key := .ofName [0x65, 0x74, 0x68, 0x32]

private def udpChecks (r : Runner) : IO Unit := Conc.Async.run do
  let some ka := key32 "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f"
    | r.check "discv5 udp: key A" false
  let some kb := key32 nodeBKey | r.check "discv5 udp: key B" false
  let some kc := key32 "fb757dc581730490a1d7a00deea65e9b1936924caaea8f44d476014856b68736"
    | r.check "discv5 udp: key C" false
  let lo := [127, 0, 0, 1]
  -- The consensus client's own pair: the predicate below looks for it.
  let tagged : List Libp2p.Identity.Enr.Pair :=
    [⟨eth2Key, .bytes [1, 2, 3, 4]⟩]
  let a ← Node.start ka lo 0
  let b ← Node.start kb lo 0
  let c ← Node.start kc lo 0 tagged
  let ea ← (a.localEnr : BaseIO _)
  let eb ← (b.localEnr : BaseIO _)
  let ec ← (c.localEnr : BaseIO _)
  -- B knows C; A boots from B alone.
  (b.addEnr ec : BaseIO Unit)
  (a.addEnr eb : BaseIO Unit)
  match ← a.ping eb with
  | some (.pong _ _ ip port) =>
    r.check "discv5 udp: A's PING to B gets a PONG naming A's endpoint" (ip == lo && port == a.port)
  | _ => r.check "discv5 udp: A's PING to B gets a PONG" false
  -- B relays only nodes it has seen answer: before B pings C, a FINDNODE
  -- at C's distance returns nothing; after, it returns C.
  let d := logDistance eb.nodeId ec.nodeId
  let before ← a.findNode eb [d]
  r.check "discv5 udp: B does not relay C before C answers a PING"
    (!before.any (·.nodeId == ec.nodeId))
  discard <| b.ping ec
  let found ← a.findNode eb [d]
  r.check "discv5 udp: FINDNODE through B returns C once C is live" (found.any (·.nodeId == ec.nodeId))
  -- The client's interface: a lookup that keeps the records with the
  -- `eth2` pair finds C, which A never booted from.
  let peers ← a.findPeers (fun e => (e.get? eth2Key).isSome) 4
  r.check "discv5 udp: findPeers finds C by its record's eth2 pair"
    (peers.any (·.nodeId == ec.nodeId))
  r.check "discv5 udp: B learned A from the handshake"
    ((← (b.known : BaseIO (List Libp2p.Identity.Enr))).any (·.nodeId == ea.nodeId))
  a.stop
  b.stop
  c.stop
  r.check "discv5 udp: the nodes stop" true

/-! ## The UDP socket's close -/

/-- `close` wakes a parked receive with `none`, within one second of
real time, for a socket bound to `ip`. -/
private def closeWakes (ip : List Nat) : Conc.Async Bool := do
  let s ← (Streams.Udp.bind ip 0 : IO Streams.Udp.Socket)
  let woke : Conc.Chan Bool ← Conc.Chan.new 1
  let ts ← Conc.TaskSet.new
  ts.spawn do discard <| woke.send (← Streams.Udp.recv s).isNone
  -- Give the receive time to park, then close.
  Conc.select #[← (Conc.Park.sleep 50 () : BaseIO (Conc.Park Unit))]
  Streams.Udp.close s
  let timer ← (Conc.Park.sleep 1000 none : BaseIO (Conc.Park (Option Bool)))
  let answer ← Conc.select #[Conc.Park.recv woke id, timer]
  if answer.isNone then
    -- The close did not wake it: a datagram from another socket to the
    -- bound address does, so the join below returns and the check fails.
    let other ← (Streams.Udp.bind [127, 0, 0, 1] 0 : IO Streams.Udp.Socket)
    let target := if ip == [0, 0, 0, 0] then [127, 0, 0, 1] else ip
    Streams.Udp.send other .empty target s.port
    Streams.Udp.close other
  ts.joinAll
  return answer == some true

private def socketChecks (r : Runner) : IO Unit := Conc.Async.run do
  -- 127.0.0.2 is a loopback address on Linux, and a datagram to
  -- 127.0.0.1 never reaches a socket bound to it.
  r.check "udp: close wakes a receive on a socket bound to 127.0.0.2"
    (← closeWakes [127, 0, 0, 2])
  r.check "udp: close wakes a receive on a socket bound to 0.0.0.0"
    (← closeWakes [0, 0, 0, 0])
  -- The bind takes no address reuse: a second socket on a held port
  -- fails, where `Std`'s own bind would share the port.
  let first ← (Streams.Udp.bind [127, 0, 0, 1] 0 : IO Streams.Udp.Socket)
  let second ← (try
      discard (Streams.Udp.bind [127, 0, 0, 1] first.port : IO Streams.Udp.Socket)
      pure true
    catch _ => pure false : IO Bool)
  r.check "udp: a second bind to a held port fails" (!second)
  Streams.Udp.close first

/-! ## Eclipse limits -/

/-- A signed record for key number `i` at `ip`, port 30303. Keys are the
scalars `i + 1`, all valid. -/
private def recordAt (i : Nat) (ip : List Nat) : Option Libp2p.Identity.Enr := do
  let k ← Crypto.Key32.ofByteArray? (ByteArray.mk ((List.range 32).map fun j =>
    if j = 31 then ((i + 1) % 256).toUInt8 else if j = 30 then ((i + 1) / 256).toUInt8 else 0).toArray)
  (Libp2p.Identity.Enr.sign k 1
    [⟨.ip, .bytes ip⟩, ⟨.udp, .bytes (Libp2p.Identity.Rlp.ofScalar 30303)⟩]).toOption

private def policyChecks (r : Runner) : IO Unit := do
  let localId := hex "bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9"
  let fill (ip : Nat → List Nat) (incoming : Bool) (n : Nat) : Table :=
    (List.range n).foldl (fun t i => match recordAt i (ip i) with
      | some e => t.insert { id := e.nodeId, record := e, incoming }
      | none => t) (Table.empty localId)
  -- 40 nodes of one global /24.
  let net := fill (fun i => [1, 2, 3, i % 250 + 1]) false 40
  let perBucket := net.buckets.toList.map (·.length)
  r.check "a /24 holds at most 2 places in a bucket" (perBucket.all (· ≤ subnetBucketLimit))
  r.check "a /24 holds at most 10 places in the table" (net.size ≤ subnetTableLimit && 0 < net.size)
  -- 40 loopback nodes: the limits do not apply.
  let lo := fill (fun i => [127, 0, 0, i % 250 + 1]) false 40
  r.check "loopback addresses are not subnet-limited" (lo.size > subnetTableLimit)
  -- Incoming nodes of distinct /24s take at most half a bucket.
  let inc := fill (fun i => [1, i % 250 + 1, 3, 4]) true 80
  r.check "incoming nodes take at most half of each bucket"
    (inc.buckets.toList.all fun b => (b.filter (·.incoming)).length ≤ incomingLimit)
  -- The rate limiter: 9 a second from one IP, 10 in total; a new second
  -- starts again.
  let ipA := [1, 1, 1, 1]
  let ipB := [2, 2, 2, 2]
  let run (steps : List (Nat × List Nat)) : List Bool := Id.run do
    let mut st : Nat × Nat × Std.HashMap (List Nat) Nat := (0, 0, {})
    let mut out : List Bool := []
    for (sec, ip) in steps do
      let (ok, st') := Node.limitStep sec ip st
      st := st'
      out := out ++ [ok]
    return out
  let fromA := run ((List.range 10).map fun _ => (5, ipA))
  r.check "the tenth unsolicited packet of a second from one IP is dropped"
    ((fromA.take 9).all id && fromA.getLast? == some false)
  let mixed := run ((List.range 9).map (fun _ => (5, ipA)) ++ [(5, ipB), (5, ipB)])
  r.check "the eleventh unsolicited packet of a second is dropped"
    (mixed.getLast? == some false && mixed[9]? == some true)
  r.check "a new second admits again"
    ((run ((List.range 9).map (fun _ => (5, ipA)) ++ [(6, ipA)])).getLast? == some true)

/-! ## TALKREQ over UDP -/

/-- The bytes of the protocol name `echo`. -/
private def echoProto : List Nat := [0x65, 0x63, 0x68, 0x6f]

/-- A node whose handler serves `echo` answers it with the request, and
any other protocol with an empty TALKRESP. -/
private def talkChecks (r : Runner) : IO Unit := Conc.Async.run do
  let some ka := key32 "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f"
    | r.check "talk: key A" false
  let some kb := key32 nodeBKey | r.check "talk: key B" false
  let lo := [127, 0, 0, 1]
  let echo (_ : ByteArray) (proto req : List Nat) : BaseIO (List Nat) :=
    pure (if proto == echoProto then req else [])
  let a ← Node.start ka lo 0
  let b ← Node.start kb lo 0 (onTalk := echo)
  let eb ← (b.localEnr : BaseIO _)
  r.check "talk: the handler answers its protocol"
    ((← a.talk eb echoProto [1, 2, 3]) == some [1, 2, 3])
  r.check "talk: an unknown protocol gets an empty TALKRESP"
    ((← a.talk eb [0x78] [1]) == some [])
  a.stop
  b.stop

/-! ## IPv6 over UDP -/

/-- Two nodes bound to `::1` find each other through `ip6`/`udp6`. -/
private def ipv6Checks (r : Runner) : IO Unit := Conc.Async.run do
  let some ka := key32 "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f"
    | r.check "ipv6: key A" false
  let some kb := key32 nodeBKey | r.check "ipv6: key B" false
  let lo6 := List.replicate 15 0 ++ [1]
  let a ← Node.start ka lo6 0
  let b ← Node.start kb lo6 0
  let eb ← (b.localEnr : BaseIO _)
  r.check "ipv6: the record names its endpoint in ip6 and udp6"
    (endpointOf? eb == some { ip := lo6, port := b.port } && (eb.ip?).toOption.join.isNone)
  match ← a.ping eb with
  | some (.pong _ _ ip port) =>
    r.check "ipv6: a PING over ::1 gets a PONG naming the IPv6 endpoint" (ip == lo6 && port == a.port)
  | _ => r.check "ipv6: a PING over ::1 gets a PONG" false
  let found ← a.findNode eb [0]
  r.check "ipv6: FINDNODE at distance 0 returns the record" (found.any (·.nodeId == eb.nodeId))
  a.stop
  b.stop

/-! ## Liveness over UDP -/

/-- A node that checks its table every 100 ms keeps a live peer and
drops a stopped one (discv5-theory.md, "Table Maintenance"). -/
private def livenessChecks (r : Runner) : IO Unit := Conc.Async.run do
  let some kx := key32 "eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f"
    | r.check "liveness: key X" false
  let some ky := key32 nodeBKey | r.check "liveness: key Y" false
  let some kz := key32 "fb757dc581730490a1d7a00deea65e9b1936924caaea8f44d476014856b68736"
    | r.check "liveness: key Z" false
  let lo := [127, 0, 0, 1]
  let x ← Node.start kx lo 0 (revalidateMs := 100)
  let y ← Node.start ky lo 0
  let z ← Node.start kz lo 0
  let ey ← (y.localEnr : BaseIO _)
  let ez ← (z.localEnr : BaseIO _)
  z.stop
  (x.addEnr ey : BaseIO Unit)
  (x.addEnr ez : BaseIO Unit)
  -- Z's check times out after one second, and once more on the retry;
  -- give it six.
  let mut dropped := false
  for _ in [0:120] do
    Conc.select #[← (Conc.Park.sleep 50 () : BaseIO (Conc.Park Unit))]
    let known ← (x.known : BaseIO (List Libp2p.Identity.Enr))
    if !known.any (·.nodeId == ez.nodeId) then
      dropped := true
      break
  r.check "liveness: a node that does not answer leaves the table" dropped
  r.check "liveness: a node that answers stays"
    ((← (x.known : BaseIO (List Libp2p.Identity.Enr))).any (·.nodeId == ey.nodeId))
  -- Y re-signs its record, as a client does when its subnets change; X's
  -- next check sees the higher seq in the PONG and pulls the record.
  r.check "liveness: Y re-signs its record"
    (← (y.updateEnr [⟨eth2Key, .bytes [9, 9, 9, 9]⟩] : BaseIO Bool))
  let mut pulled := false
  for _ in [0:60] do
    Conc.select #[← (Conc.Park.sleep 50 () : BaseIO (Conc.Park Unit))]
    let known ← (x.known : BaseIO (List Libp2p.Identity.Enr))
    if known.any (fun e => e.nodeId == ey.nodeId && e.seq == ey.seq + 1) then
      pulled := true
      break
  r.check "liveness: a PONG with a higher seq pulls the new record" pulled
  x.stop
  y.stop

/-- Serve one node for an outside tester (`scripts/discv5-geth-interop.sh`):
bind `127.0.0.1` at `LEANP2P_DISCV5_PORT` (0 for any), print
`ENR <text>` and flush, and serve for `LEANP2P_DISCV5_MS` milliseconds
(60000 by default). The key is node B's of the wire vectors. -/
def serve : IO Unit := Conc.Async.run do
  let some kb := key32 nodeBKey | throw (IO.userError "discv5 serve: key")
  let port := ((← IO.getEnv "LEANP2P_DISCV5_PORT").bind (·.toNat?)).getD 0
  let ms := ((← IO.getEnv "LEANP2P_DISCV5_MS").bind (·.toNat?)).getD 60000
  -- `echo` answers with the request; any other protocol gets an empty
  -- TALKRESP, the default.
  let echo (_ : ByteArray) (proto req : List Nat) : BaseIO (List Nat) :=
    pure (if proto == [0x65, 0x63, 0x68, 0x6f] then req else [])
  let n ← Node.start kb [127, 0, 0, 1] port (onTalk := echo)
  let e ← (n.localEnr : BaseIO _)
  IO.println s!"ENR {e.toText}"
  (← IO.getStdout).flush
  Conc.select #[← (Conc.Park.sleep ms () : BaseIO (Conc.Park Unit))]
  n.stop

/-- Query an outside node (`scripts/discv5-rust-interop.sh`): the ENR in
`LEANP2P_DISCV5_TARGET` gets a PING, a FINDNODE at distance 0, and a
TALKREQ `echo` of `[1, 2, 3]`. One line per answer; exit code 0 when all
three came back right. The geth driver also runs it
(`scripts/discv5-geth-interop.sh`). -/
def client : IO UInt32 := Conc.Async.run do
  let some kb := key32 nodeBKey | throw (IO.userError "discv5 client: key")
  let some text ← (IO.getEnv "LEANP2P_DISCV5_TARGET" : IO (Option String))
    | throw (IO.userError "discv5 client: LEANP2P_DISCV5_TARGET")
  let .ok target := Libp2p.Identity.Enr.ofText? text
    | throw (IO.userError "discv5 client: the target ENR does not decode")
  let n ← Node.start kb [127, 0, 0, 1] 0
  (n.addEnr target : BaseIO Unit)
  let mut ok := true
  match ← n.ping target with
  | some (.pong _ seq ip port) => IO.println s!"PONG seq {seq} ip {ip} port {port}"
  | _ =>
    IO.println "PING failed"
    ok := false
  let found ← n.findNode target [0]
  let self := found.any (·.nodeId == target.nodeId)
  IO.println s!"NODES {found.length} self {self}"
  ok := ok && self
  -- With `LEANP2P_DISCV5_ECHO=0` the target serves no `echo`, and the
  -- answer must be the empty TALKRESP of an unknown protocol.
  let echoes := (← IO.getEnv "LEANP2P_DISCV5_ECHO") != some "0"
  match ← n.talk target [0x65, 0x63, 0x68, 0x6f] [1, 2, 3] with
  | some resp =>
    IO.println s!"TALKRESP {resp}"
    ok := ok && resp == (if echoes then [1, 2, 3] else [])
  | none =>
    IO.println "TALKREQ failed"
    ok := false
  n.stop
  return if ok then 0 else 1

def run (r : Runner) : IO Unit := do
  r.section "discv5" "devp2p discv5/discv5-wire-test-vectors.md"
  memoryChecks r
  gethChecks r
  policyChecks r
  udpChecks r
  socketChecks r
  talkChecks r
  ipv6Checks r
  livenessChecks r
  -- ECDH.
  match key32 "fb757dc581730490a1d7a00deea65e9b1936924caaea8f44d476014856b68736" with
  | none => r.check "discv5: the ECDH key builds" false
  | some sk =>
    r.check "discv5: ECDH gives the compressed shared point"
      ((Crypto.secp256k1Ecdh sk
          (hex "039961e4c2356d61bedb83052c115d311acb3a96f5777296dcf297351130266231")).toOption ==
        some (hex "033b11a2a1f214567e1537ce5e509ffd9b21373247f2a3ff6841f4976f53165e7e"))
    -- Key derivation.
    match deriveKeys sk (hex "0317931e6e0840220642f230037d285d122bc59063221ef3226b1f403ddc69ca91")
        (challengeData "0000000000000000") srcId destId with
    | .ok k =>
      r.check "discv5: the key derivation gives both keys"
        (k.initiator.bytes == hex "dccc82d81bd610f4f76d3ebe97a40571" &&
          k.recipient.bytes == hex "ac74bb8773749920b0d3a8881c173ec5")
    | .error e => r.check s!"discv5: the key derivation runs ({repr e})" false
    -- The id signature, both ways.
    let eph := hex "039961e4c2356d61bedb83052c115d311acb3a96f5777296dcf297351130266231"
    let sig := hex ("94852a1e2318c4e5e9d422c98eaf19d1d90d876b29cd06ca7cb7546d0fff7b48" ++
      "4fe86c09a064fe72bdbef73ba8e9c34df0cd2b53e9d65528c2c7f336d5dfc6e6")
    r.check "discv5: the id signature matches the vector"
      ((idSign sk (challengeData "0000000000000000") eph destId).toOption == some sig)
    match Crypto.secp256k1PublicKey sk with
    | .ok pub =>
      r.check "discv5: the id signature verifies"
        (idVerify pub sig (challengeData "0000000000000000") eph destId)
      r.check "discv5: the id signature fails for another node id"
        !(idVerify pub sig (challengeData "0000000000000000") eph srcId)
    | .error _ => r.check "discv5: the static public key builds" false
  -- AES-GCM.
  match key16 "9f2d77db7004bf8a1a85107ac686990b",
      Crypto.Nonce12.ofByteArray? (hex "27b5af763c446acd2749fe8e") with
  | some k, some n =>
    r.check "discv5: AES-128-GCM seals the vector"
      ((Crypto.aes128GcmSeal k n (hex "93a7400fa0d6a694ebc24d5cf570f65d04215b6ac00757875e3f3a5f42107903")
          (hex "01c20101")).toOption ==
        some (hex "a5d12a2d94b8ccb3ba55558229867dc13bfa3648"))
  | _, _ => r.check "discv5: the AES-GCM inputs build" false
  -- The ping message packet: unmask as node B, open with the zero key.
  match unmask destId pingPacket, key16 "00000000000000000000000000000000" with
  | .ok u, some k =>
    r.check "discv5: the ping packet is a message packet from node A"
      (u.header.flag == .message && u.header.authdata == srcId &&
        u.header.nonce == hex "ffffffffffffffffffffffff")
    match openMessage k u with
    | .ok pt =>
      r.check "discv5: the ping packet holds PING, request 1, enr-seq 2"
        (pingOf pt == some (1, [0, 0, 0, 1], 2))
      r.check "discv5: the node's encoder writes the vector's PING plaintext"
        ((Message.ping [0, 0, 0, 1] 2).encode.toList == pt.toList)
      r.check "discv5: masking the same header and message rebuilds the packet"
        ((mask destId u.iv u.header u.message).toOption == some pingPacket)
      r.check "discv5: sealing the PING again rebuilds the message"
        ((sealMessage k u.iv u.header pt).toOption == some u.message)
    | .error e => r.check s!"discv5: the ping message opens ({repr e})" false
  | _, _ => r.check "discv5: the ping packet unmasks" false
  -- WHOAREYOU: the challenge data is `masking-iv ‖ header`.
  match unmask destId whoareyouPacket with
  | .ok u =>
    r.check "discv5: WHOAREYOU carries id-nonce and enr-seq 0"
      (u.header.flag == .whoareyou &&
        u.header.authdata == hex "0102030405060708090a0b0c0d0e0f100000000000000000" &&
        u.message.isEmpty)
    r.check "discv5: WHOAREYOU's iv and header are the challenge data"
      (u.iv ++ u.headerBytes == challengeData "0000000000000000")
  | .error e => r.check s!"discv5: WHOAREYOU unmasks ({repr e})" false
  -- The handshake packet: node B derives the keys from its own key and
  -- the ephemeral key in the packet, and opens the PING.
  match unmask destId handshakePacket, key32 nodeBKey with
  | .ok u, some bKey =>
    let ad := u.header.authdata
    let sigSize := (ad.get! 32).toNat
    let ephSize := (ad.get! 33).toNat
    let ephPub := ad.extract (34 + sigSize) (34 + sigSize + ephSize)
    r.check "discv5: the handshake names node A, a 64-byte signature, a 33-byte key"
      (u.header.flag == .handshake && ad.extract 0 32 == srcId && sigSize == 64 && ephSize == 33 &&
        ephPub == hex "039a003ba6517b473fa0cd74aefe99dadfdb34627f90fec6362df85803908f53a5")
    -- Node B's side of ECDH: its static key times the ephemeral public
    -- key gives the same secret as A's ephemeral key times B's public key.
    match deriveKeys bKey ephPub (challengeData "0000000000000001") srcId destId with
    | .ok keys =>
      r.check "discv5: node B derives the read key of the vector"
        (keys.initiator.bytes == hex "4f9fac6de7567d1e3b1241dffe90f662")
      match openMessage keys.initiator u with
      | .ok pt =>
        r.check "discv5: the handshake holds PING, request 1, enr-seq 1"
          (pingOf pt == some (1, [0, 0, 0, 1], 1))
      | .error e => r.check s!"discv5: the handshake message opens ({repr e})" false
    | .error e => r.check s!"discv5: node B derives the keys ({repr e})" false
  | _, _ => r.check "discv5: the handshake packet unmasks" false

end Tests.Discv5
