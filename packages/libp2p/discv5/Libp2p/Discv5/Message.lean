import Bytes
import Libp2p.Identity

/-!
# discv5: the protocol messages

The six messages a consensus node uses (devp2p `discv5-wire.md`,
"Protocol Messages"): PING, PONG, FINDNODE, NODES, TALKREQ, TALKRESP.
The topic messages (REGTOPIC to TOPICNODES) are left out: the consensus
spec finds subnet peers through the record's `attnets` and `syncnets`
(phase0 `p2p-interface.md`, "How are we going to discover peers in a
gossipsub topic?").

Each message is `message-type ‖ RLP(message-data)`, and every
`message-data` list starts with the request id, an RLP byte array of at
most 8 bytes, which a response mirrors.
-/

set_option autoImplicit false

namespace Libp2p.Discv5

open Bytes Libp2p.Identity

/-- The protocol messages. -/
inductive Message where
  /-- PING (0x01): the sender's record sequence number. -/
  | ping (requestId : List Nat) (enrSeq : Nat)
  /-- PONG (0x02): the sender's record sequence number, and the address
  and port the sender saw the PING come from. -/
  | pong (requestId : List Nat) (enrSeq : Nat) (ip : List Nat) (port : Nat)
  /-- FINDNODE (0x03): the log2 distances to collect. -/
  | findNode (requestId : List Nat) (distances : List Nat)
  /-- NODES (0x04): one of `total` answers, with encoded records. -/
  | nodes (requestId : List Nat) (total : Nat) (records : List Enr)
  /-- TALKREQ (0x05). -/
  | talkReq (requestId : List Nat) (protocol : List Nat) (request : List Nat)
  /-- TALKRESP (0x06). -/
  | talkResp (requestId : List Nat) (response : List Nat)

namespace Message

/-- The request id a message carries. -/
def requestId : Message → List Nat
  | .ping r _ | .pong r _ _ _ | .findNode r _ | .nodes r _ _ | .talkReq r _ _ | .talkResp r _ => r

/-- True for a request; a response answers one. -/
def isRequest : Message → Bool
  | .ping .. | .findNode .. | .talkReq .. => true
  | _ => false

private def scalar (n : Nat) : Rlp.Item := .bytes (Rlp.ofScalar n)

/-- The plaintext of a message: its type byte, then its RLP list. -/
def encode : Message → ByteArray
  | .ping r seq => ofNatList (0x01 :: Rlp.encode (.list [.bytes r, scalar seq]))
  | .pong r seq ip port =>
    ofNatList (0x02 :: Rlp.encode (.list [.bytes r, scalar seq, .bytes ip, scalar port]))
  | .findNode r ds => ofNatList (0x03 :: Rlp.encode (.list [.bytes r, .list (ds.map scalar)]))
  | .nodes r total rs =>
    -- A record is an RLP list on the wire; its encoding is that list.
    let items := rs.filterMap fun e =>
      match Rlp.decode? (toNatList (Enr.encode e)) with
      | .ok (v, []) => some v.item
      | _ => none
    ofNatList (0x04 :: Rlp.encode (.list [.bytes r, scalar total, .list items]))
  | .talkReq r proto req => ofNatList (0x05 :: Rlp.encode (.list [.bytes r, .bytes proto, .bytes req]))
  | .talkResp r resp => ofNatList (0x06 :: Rlp.encode (.list [.bytes r, .bytes resp]))

/-- A scalar field, `none` past `maxBytes` bytes or with a leading zero. -/
private def scalarOf? (maxBytes : Nat) : Rlp.Item → Option Nat
  | .bytes b => Rlp.scalar? maxBytes b
  | .list _ => none

/-- A request id: a byte array of at most 8 bytes. -/
private def requestIdOf? : Rlp.Item → Option (List Nat)
  | .bytes b => if b.length ≤ 8 then some b else none
  | .list _ => none

/-- Decode a plaintext. `none` for an unknown type or a malformed body. -/
def decode? (pt : ByteArray) : Option Message := do
  if pt.size = 0 then none
  let (v, rest) ← (Rlp.decode? (toNatList (pt.extract 1 pt.size))).toOption
  if !rest.isEmpty then none
  let .list items := v.item | none
  match pt.get! 0, items with
  | 0x01, [r, seq] => return .ping (← requestIdOf? r) (← scalarOf? 8 seq)
  | 0x02, [r, seq, .bytes ip, port] =>
    if ip.length != 4 && ip.length != 16 then none
    return .pong (← requestIdOf? r) (← scalarOf? 8 seq) ip (← scalarOf? 2 port)
  | 0x03, [r, .list ds] => return .findNode (← requestIdOf? r) (← ds.mapM (scalarOf? 2))
  | 0x04, [r, total, .list rs] =>
    let records ← rs.mapM fun i => (Enr.decode? (ofNatList (Rlp.encode i))).toOption
    return .nodes (← requestIdOf? r) (← scalarOf? 8 total) records
  | 0x05, [r, .bytes proto, .bytes req] => return .talkReq (← requestIdOf? r) proto req
  | 0x06, [r, .bytes resp] => return .talkResp (← requestIdOf? r) resp
  | _, _ => none

end Message

end Libp2p.Discv5
