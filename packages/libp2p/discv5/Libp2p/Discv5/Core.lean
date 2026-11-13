import Std.Data.HashMap
import Bytes
import Crypto
import Libp2p.Identity
import Libp2p.Discv5.Packet
import Libp2p.Discv5.Message
import Libp2p.Discv5.Table

/-!
# discv5: the protocol core

The pure state machine of a discv5 node (devp2p `discv5-theory.md`,
"Sessions" and "Handshake Steps"): sessions, the WHOAREYOU handshake in
both roles, the answers to PING, FINDNODE, and TALKREQ, and the node
table. The shell (`Libp2p.Discv5.Node`) owns the socket, the clock, and
the randomness, and hands each event the random bytes it may need, so
the core makes no choice of its own and a test replays it.

Spike scope: no request timeouts or retries (the shell's), no session
eviction (the spec's LRU cache), no endpoint votes beyond recording
PONG's `recipient-ip`, and no per-IP limits.
-/

set_option autoImplicit false

namespace Libp2p.Discv5

open Bytes Libp2p.Identity

/-- A UDP endpoint: the IP address bytes, 4 or 16, and the port. -/
structure Endpoint where
  ip : List Nat
  port : Nat
  deriving BEq, Repr

/-- An established session (discv5-theory.md, "Session Cache"). -/
structure Session where
  readKey : Crypto.Key16
  writeKey : Crypto.Key16
  endpoint : Endpoint

/-- A request we sent, by the nonce of its packet, so a WHOAREYOU can
answer it with a handshake. -/
structure Sent where
  destId : ByteArray
  destPub : ByteArray
  endpoint : Endpoint
  message : Message

/-- A WHOAREYOU we sent, by the node id it challenged. -/
structure Challenge where
  challengeData : ByteArray
  endpoint : Endpoint

/-- The core state. -/
structure State where
  key : Crypto.Key32
  localId : ByteArray
  localEnr : Enr
  sessions : Std.HashMap Nat Session := {}
  sent : Std.HashMap (List UInt8) Sent := {}
  challenges : Std.HashMap Nat Challenge := {}
  table : Table
  /-- The `recipient-ip`/`port` each PONG reported, newest first: the
  votes for our external endpoint (discv5-theory.md, "Maintaining The
  Local Node Record"). -/
  votes : List Endpoint := []

/-- The events. Each carries at least `randLen` random bytes. -/
inductive Event where
  /-- A datagram arrived from `src`. -/
  | packet (src : Endpoint) (bytes : ByteArray) (rand : ByteArray)
  /-- Send `m` to the node of `dest` at `endpoint`. -/
  | request (dest : Enr) (endpoint : Endpoint) (m : Message) (rand : ByteArray)

/-- The random bytes an event needs: IV, nonce, id-nonce, ephemeral key,
and a second IV and nonce for the handshake packet. -/
def randLen : Nat := 16 + 12 + 16 + 32 + 16 + 12

/-- The actions. -/
inductive Action where
  /-- Send a datagram. -/
  | send (dst : Endpoint) (bytes : ByteArray)
  /-- A response arrived from the node `src`. -/
  | response (src : ByteArray) (m : Message)

namespace Core

/-- The core of a node with `key` and its signed record. -/
def init (key : Crypto.Key32) (record : Enr) : State :=
  { key, localId := record.nodeId, localEnr := record, table := Table.empty record.nodeId }

private def slice (b : ByteArray) (from_ len : Nat) : ByteArray := b.extract from_ (from_ + len)

private def nonceKey (n : ByteArray) : List UInt8 := n.toList

/-- Seal `m` in an ordinary message packet for `destId` under `key`. -/
private def messagePacket (localId destId : ByteArray) (key : Crypto.Key16) (iv nonce : ByteArray)
    (m : Message) : Option ByteArray := do
  let h : Header := { flag := .message, nonce, authdata := localId }
  let ct ← (sealMessage key iv h m.encode).toOption
  (mask destId iv h ct).toOption

/-- Send `m` to `destId`: in its session when there is one, else as a
message packet with random content, which draws the WHOAREYOU of step 2
(discv5-theory.md, "Step 1"). A request is remembered by its nonce. -/
private def sendTo (s : State) (destId destPub : ByteArray) (ep : Endpoint) (m : Message)
    (rand : ByteArray) : State × List Action :=
  let iv := slice rand 0 16
  let nonce := slice rand 16 12
  let remember (s : State) : State :=
    if m.isRequest then { s with sent := s.sent.insert (nonceKey nonce) { destId, destPub, endpoint := ep, message := m } }
    else s
  match s.sessions.get? (idNat destId) with
  | some ses =>
    match messagePacket s.localId destId ses.writeKey iv nonce m with
    | some p => (remember s, [.send ep p])
    | none => (s, [])
  | none =>
    let h : Header := { flag := .message, nonce, authdata := s.localId }
    -- Random bytes in place of a sealed message: the recipient cannot
    -- open it, and answers WHOAREYOU.
    match mask destId iv h (slice rand 44 20) with
    | .ok p => (remember s, [.send ep p])
    | .error _ => (s, [])

/-- The NODES answers to FINDNODE: our record for distance 0, the table's
records for the others, at most 16, three to a packet so each stays
under 1280 bytes (discv5-wire.md, "NODES Response"). -/
private def nodesAnswers (s : State) (rid : List Nat) (ds : List Nat) : List Message :=
  let records := (ds.flatMap fun d => if d = 0 then [s.localEnr] else s.table.atDistance d).take 16
  let groups := (List.range ((records.length + 2) / 3)).map fun i => (records.drop (3 * i)).take 3
  let groups := if groups.isEmpty then [[]] else groups
  groups.map fun g => .nodes rid groups.length g

/-- Handle a decrypted message from `srcId` at `src`. -/
private def onMessage (s : State) (srcId : ByteArray) (src : Endpoint) (m : Message)
    (rand : ByteArray) : State × List Action :=
  let reply (s : State) (ms : List Message) : State × List Action :=
    match s.sessions.get? (idNat srcId) with
    | none => (s, [])
    | some ses =>
      let packets := (List.range ms.length).zip ms |>.filterMap fun (i, r) =>
        -- Each answer takes its own nonce from the random bytes.
        let nonce := ByteArray.mk ((slice rand 16 12).toList.toArray.set! 11 (UInt8.ofNat i))
        messagePacket s.localId srcId ses.writeKey (slice rand 0 16) nonce r
      (s, packets.map (Action.send ses.endpoint))
  match m with
  | .ping rid _ => reply s [.pong rid s.localEnr.seq src.ip src.port]
  | .findNode rid ds => reply s (nodesAnswers s rid ds)
  | .talkReq rid _ _ => reply s [.talkResp rid []]
  | .pong _ _ ip port =>
    ({ s with votes := ({ ip, port } :: s.votes).take 32 }, [.response srcId m])
  | .nodes _ _ rs =>
    let t := rs.foldl (fun t e => t.insert { id := e.nodeId, record := e }) s.table
    ({ s with table := t }, [.response srcId m])
  | .talkResp .. => (s, [.response srcId m])

/-- Answer a message we cannot open with WHOAREYOU, and remember the
challenge (discv5-theory.md, "Step 2"). -/
private def challenge (s : State) (srcId : ByteArray) (src : Endpoint) (nonce rand : ByteArray) :
    State × List Action :=
  let known := ((s.table.entries.find? (·.id == srcId)).map (·.record.seq)).getD 0
  let seqBytes := ByteArray.mk ((List.range 8).reverse.map fun i => (known / 256 ^ i % 256).toUInt8).toArray
  let h : Header := { flag := .whoareyou, nonce, authdata := slice rand 28 16 ++ seqBytes }
  let iv := slice rand 0 16
  match mask srcId iv h .empty with
  | .ok p =>
    let ch : Challenge := { challengeData := iv ++ h.encode, endpoint := src }
    ({ s with challenges := s.challenges.insert (idNat srcId) ch }, [.send src p])
  | .error _ => (s, [])

/-- Answer a WHOAREYOU with a handshake packet that carries the request
again (discv5-theory.md, "Step 3"). -/
private def onWhoareyou (s : State) (u : Unmasked) (rand : ByteArray) : State × List Action :=
  match s.sent.get? (nonceKey u.header.nonce) with
  | none => (s, [])
  | some p =>
    let challengeData := u.iv ++ u.headerBytes
    let enrSeq := (u.header.authdata.extract 16 24).foldl (fun n b => n * 256 + b.toNat) 0
    let result : Option (State × List Action) := do
      let eph ← Crypto.Key32.ofByteArray? (slice rand 44 32)
      let ephPub ← (Crypto.secp256k1PublicKey eph).toOption
      let keys ← (deriveKeys eph p.destPub challengeData s.localId p.destId).toOption
      let sig ← (idSign s.key challengeData ephPub p.destId).toOption
      let record := if enrSeq < s.localEnr.seq then Enr.encode s.localEnr else .empty
      let authdata := s.localId ++ ByteArray.mk #[64, 33] ++ sig ++ ephPub ++ record
      let iv := slice rand 76 16
      let nonce := slice rand 92 12
      let h : Header := { flag := .handshake, nonce, authdata }
      let ct ← (sealMessage keys.initiator iv h p.message.encode).toOption
      let pkt ← (mask p.destId iv h ct).toOption
      let s := { s with
        sessions := s.sessions.insert (idNat p.destId)
          { readKey := keys.recipient, writeKey := keys.initiator, endpoint := p.endpoint }
        sent := (s.sent.erase (nonceKey u.header.nonce)).insert (nonceKey nonce) p }
      return (s, [.send p.endpoint pkt])
    result.getD (s, [])

/-- Accept a handshake packet against our challenge, set up the session,
and handle its message (discv5-theory.md, "Step 4"). -/
private def onHandshake (s : State) (src : Endpoint) (u : Unmasked) (rand : ByteArray) :
    State × List Action :=
  let ad := u.header.authdata
  let srcId := ad.extract 0 32
  let sigSize := (ad.get! 32).toNat
  let ephSize := (ad.get! 33).toNat
  let sig := ad.extract 34 (34 + sigSize)
  let ephPub := ad.extract (34 + sigSize) (34 + sigSize + ephSize)
  let recordBytes := ad.extract (34 + sigSize + ephSize) ad.size
  let result : Option (State × List Action) := do
    let ch ← s.challenges.get? (idNat srcId)
    -- The record in the packet, or the one the table holds.
    let record ← if recordBytes.isEmpty then
        (s.table.entries.find? (·.id == srcId)).map (·.record)
      else (Enr.decode? recordBytes).toOption
    if record.nodeId != srcId then none
    let pub := ofNatList record.publicKey
    if !idVerify pub sig ch.challengeData ephPub s.localId then none
    let keys ← (deriveKeys s.key ephPub ch.challengeData srcId s.localId).toOption
    let pt ← (openMessage keys.initiator u).toOption
    let m ← Message.decode? pt
    let s := { s with
      sessions := s.sessions.insert (idNat srcId)
        { readKey := keys.initiator, writeKey := keys.recipient, endpoint := src }
      challenges := s.challenges.erase (idNat srcId)
      table := s.table.insert { id := srcId, record } }
    return onMessage s srcId src m rand
  result.getD (s, [])

/-- One step of the core. -/
def step (s : State) : Event → State × List Action
  | .request dest ep m rand =>
    sendTo s dest.nodeId (ofNatList dest.publicKey) ep m rand
  | .packet src bytes rand =>
    match unmask s.localId bytes with
    | .error _ => (s, [])
    | .ok u =>
      match u.header.flag with
      | .message =>
        let srcId := u.header.authdata
        let opened := do
          let ses ← s.sessions.get? (idNat srcId)
          let pt ← (openMessage ses.readKey u).toOption
          Message.decode? pt
        match opened with
        | some m =>
          -- A response clears the request it answers; a NODES answer
          -- may come in several packets, so the request stays until the
          -- shell's timeout in the spike.
          onMessage s srcId src m rand
        | none => challenge s srcId src u.header.nonce rand
      | .whoareyou => onWhoareyou s u rand
      | .handshake => onHandshake s src u rand

end Core

end Libp2p.Discv5
