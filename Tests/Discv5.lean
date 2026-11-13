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

/-- The decoded PING of a packet: `(type, request-id, enr-seq)`. -/
private def pingOf (pt : ByteArray) : Option (UInt8 × List Nat × Nat) :=
  match decodeMessage pt with
  | .ok (t, [.bytes rid, .bytes seq]) => some (t, rid, Libp2p.Identity.Rlp.beNat seq)
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
    r.check "discv5 memory: A recorded B's view of its endpoint" (a2.votes.contains epA)
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
  | _, _ => r.check "discv5 memory: the records sign" false

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
  -- A FINDNODE at C's distance from B returns C's record.
  let d := logDistance eb.nodeId ec.nodeId
  let found ← a.findNode eb [d]
  r.check "discv5 udp: FINDNODE through B returns C" (found.any (·.nodeId == ec.nodeId))
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

def run (r : Runner) : IO Unit := do
  r.section "discv5" "devp2p discv5/discv5-wire-test-vectors.md"
  memoryChecks r
  udpChecks r
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
