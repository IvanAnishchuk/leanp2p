import Std.Data.HashMap
import Conc
import Streams
import Crypto
import Libp2p.Identity
import Libp2p.Discv5.Core

/-!
# discv5: the node

The IO shell over `Libp2p.Discv5.Core`: the UDP socket, the randomness,
the waits, and the lookup (devp2p `discv5-theory.md`, "Lookup").

* The core state sits in one `OnceRef`. Each event runs the pure step
  under `updateGet` (PRINCIPLES 3.3), and the shell then performs the
  actions: datagrams go out, responses go to their waiters.
* A reader task feeds each datagram to the core. `stop` closes the
  socket, which wakes the reader, and joins it.
* A request waits for its responses by request id, under a deadline.
  NODES may come in several packets; `findNode` collects them until
  their `total` or the deadline.
* `lookup` walks toward a target: it asks the closest unqueried nodes
  for the log distances around the target, merges what they return,
  and stops when the `k` closest it knows have all been asked. The spike
  asks one node at a time; the spec's `α` runs them concurrently.
* `findPeers` is the consensus client's interface (phase0
  `p2p-interface.md`, "Integration into libp2p stacks"): a lookup toward
  a random target, filtered by the client's predicate over records, such
  as a fork-digest and subnet match on `eth2` and `attnets`.
-/

set_option autoImplicit false

namespace Libp2p.Discv5

open Conc Libp2p.Identity

/-- The endpoint a record names for discv5: `ip` and `udp`, else `ip6`
and `udp6`. -/
def endpointOf? (e : Enr) : Option Endpoint :=
  let v4 : Option Endpoint := do
    let ip ← (e.ip?).toOption.join
    let port ← (e.port? .udp).toOption.join
    return { ip, port }
  let v6 : Option Endpoint := do
    let ip ← (e.ip6?).toOption.join
    let port ← (e.port? .udp6).toOption.join
    return { ip, port }
  v4 <|> v6

/-- A running node. -/
structure Node where
  private core : OnceRef State
  private socket : Streams.Udp.Socket
  private waiters : OnceRef (List (List Nat × Chan Message))
  private nextId : OnceRef Nat
  private tasks : TaskSet
  /-- Closed by `stop`: the revalidation task parks on it between rounds. -/
  private stopping : Chan Unit
  /-- The last liveness check of each table entry, by node id, in
  milliseconds of the monotonic clock. -/
  private checked : OnceRef (Std.HashMap Nat Nat)
  /-- The pause between two liveness checks. -/
  revalidateMs : Nat
  /-- The UDP port the node listens on. -/
  port : Nat

namespace Node

/-- Perform the actions of one core step. -/
private def perform (n : Node) (acts : List Action) : Async Unit := do
  for a in acts do
    match a with
    | .send ep bytes => Streams.Udp.send n.socket bytes ep.ip ep.port
    | .response _ m =>
      for (rid, ch) in ← (n.waiters.get : BaseIO _) do
        if rid == m.requestId then discard (ch.trySend m : BaseIO Bool)

/-- `n` random bytes; a DRBG failure is an IO error. -/
private def random (n : Nat) : IO ByteArray := do
  match ← (Crypto.randomBytes n).run with
  | .ok b => return b
  | .error _ => throw (IO.userError "discv5: no random bytes")

/-- Run one event through the core and perform its actions. -/
private def feed (n : Node) (mk : ByteArray → Event) : Async Unit := do
  let rand ← (random randLen : IO ByteArray)
  let acts ← (n.core.updateGet fun s => let (s', a) := Core.step s (mk rand); (a, s') :
    BaseIO (List Action))
  n.perform acts

/-- The reader: each datagram goes to the core. `partial`, as the IO read
loops are; `stop` ends it by closing the socket. -/
private partial def reader (n : Node) : Async Unit := do
  match ← Streams.Udp.recv n.socket with
  | none => return
  | some (bytes, ip, port) =>
    n.feed (Event.packet { ip, port } bytes)
    n.reader

/-- Stop: close the socket, which wakes the reader, and the stop
channel, which wakes the revalidation task; then join both. -/
def stop (n : Node) : Async Unit := do
  (n.stopping.close : BaseIO Unit)
  Streams.Udp.close n.socket
  n.tasks.joinAll

/-- The node's own record. -/
def localEnr (n : Node) : BaseIO Enr := do
  return (← n.core.get).localEnr

/-- Re-sign the local record under the next `seq`, with `pairs` in place
of the pairs of the same keys: a consensus client does this when its
`eth2`, `attnets`, or `syncnets` change. `false` when the record does not
sign, and the record stays. Peers pull the new record at their next
liveness check. -/
def updateEnr (n : Node) (pairs : List Enr.Pair) : BaseIO Bool :=
  n.core.updateGet fun s =>
    let keep := s.localEnr.pairs.filter fun p => !pairs.any (·.key == p.key)
    match Enr.sign s.key (s.localEnr.seq + 1) (pairs ++ keep) with
    | .ok r => (true, { s with localEnr := r })
    | .error _ => (false, s)

/-- Add a record to the table, as a boot record is. -/
def addEnr (n : Node) (e : Enr) : BaseIO Unit :=
  n.core.update fun s => { s with table := s.table.insert { id := e.nodeId, record := e } }

/-- The records the table holds. -/
def known (n : Node) : BaseIO (List Enr) := do
  return (← n.core.get).table.entries.map (·.record)

/-- The external endpoints the PONGs reported, newest first. -/
def votes (n : Node) : BaseIO (List Endpoint) := do
  return (← n.core.get).votes.map (·.2)

/-- Send `m` (its request id is set here) to `e`, and collect responses
until `done` holds or `timeoutMs` passes. -/
private def ask (n : Node) (e : Enr) (m : List Nat → Message) (timeoutMs : Nat)
    (done : List Message → Bool) : Async (List Message) := do
  let some ep := endpointOf? e | return []
  let num ← (n.nextId.updateGet fun i => (i, i + 1) : BaseIO Nat)
  let rid := (List.range 8).reverse.map fun i => num / 256 ^ i % 256
  let ch : Chan Message ← Chan.new 16
  (n.waiters.update ((rid, ch) :: ·) : BaseIO Unit)
  n.feed (Event.request e ep (m rid))
  let deadline := (← (IO.monoMsNow : IO Nat)) + timeoutMs
  let mut got : List Message := []
  repeat
    if done got then break
    let now ← (IO.monoMsNow : IO Nat)
    if deadline ≤ now then break
    let timer ← (Park.sleep (deadline - now) none : BaseIO (Park (Option Message)))
    -- Park: a response wakes it, and so does the deadline.
    match ← select #[Park.recv ch id, timer] with
    | some r => got := got ++ [r]
    | none => break
  (n.waiters.update (·.filter (·.1 != rid)) : BaseIO Unit)
  -- The core keeps the request until its answer ends; past the deadline
  -- the shell ends it here.
  n.feed fun _ => .forget rid
  return got

/-- PING a node; its PONG, if one came within `timeoutMs`. -/
def ping (n : Node) (e : Enr) (timeoutMs : Nat := 2000) : Async (Option Message) := do
  let seq := (← (n.core.get : BaseIO State)).localEnr.seq
  return (← n.ask e (fun rid => .ping rid seq) timeoutMs (!·.isEmpty)).head?

/-- FINDNODE: the records a node returns for `distances`, from every
NODES packet up to their `total`. -/
def findNode (n : Node) (e : Enr) (distances : List Nat) (timeoutMs : Nat := 2000) :
    Async (List Enr) := do
  let total (ms : List Message) : Option Nat := ms.head?.bind fun m =>
    match m with | .nodes _ t _ => some t | _ => none
  let ms ← n.ask e (fun rid => .findNode rid distances) timeoutMs fun ms =>
    match total ms with | some t => ms.length ≥ t | none => false
  return ms.flatMap fun m => match m with | .nodes _ _ rs => rs | _ => []

/-- α, the FINDNODE requests a lookup runs at once (discv5-theory.md,
"Lookup": "typically 3"). -/
def alpha : Nat := 3

/-- Walk toward `target`: the `k` closest records found
(discv5-theory.md, "Lookup"). -/
def lookup (n : Node) (target : ByteArray) (k : Nat := bucketSize) (rounds : Nat := 8) :
    Async (List Enr) := do
  let s ← (n.core.get : BaseIO State)
  let self := s.localId
  let dist (e : Enr) : Nat := Nat.xor (idNat e.nodeId) (idNat target)
  let mut seen : List Enr := (s.table.closest target k).map (·.record)
  let mut queried : List ByteArray := []
  for _ in [0:rounds * k] do
    -- `stop` ends a lookup between rounds.
    if ← (n.stopping.isClosed : BaseIO Bool) then break
    let sorted := seen.mergeSort fun a b => dist a ≤ dist b
    let batch := ((sorted.take k).filter fun e => !queried.contains e.nodeId).take alpha
    if batch.isEmpty then break
    queried := batch.map (·.nodeId) ++ queried
    -- Up to `alpha` FINDNODEs at once, each on a task of a set this
    -- round joins.
    let results : Chan (List Enr) ← Chan.new alpha
    let ts ← TaskSet.new
    for next in batch do
      let d := logDistance next.nodeId target
      let ds := ([d, d + 1, d - 1].filter fun x => 1 ≤ x && x ≤ 256).eraseDups
      ts.spawn do discard <| results.send (← n.findNode next (if ds.isEmpty then [256] else ds))
    ts.joinAll
    for _ in batch do
      if let some found ← (results.tryRecv : BaseIO (Option (List Enr))) then
        for e in found do
          if e.nodeId != self && !seen.any (·.nodeId == e.nodeId) then
            seen := e :: seen
            n.addEnr e
  return (seen.mergeSort fun a b => dist a ≤ dist b).take k

/-- The client's interface: up to `count` records a lookup toward a
random target turns up that pass `pred`. -/
def findPeers (n : Node) (pred : Enr → Bool) (count : Nat) : Async (List Enr) := do
  let target ← (random 32 : IO ByteArray)
  let found ← n.lookup target
  let known ← (n.known : BaseIO (List Enr))
  let all := found ++ known.filter fun e => !found.any (·.nodeId == e.nodeId)
  return (all.filter pred).take count

/-- The liveness rounds between two refresh lookups. -/
def refreshEvery : Nat := 30

/-- One liveness check: PING the table entry checked longest ago. A node
that does not answer leaves the table, and the newest replacement of its
bucket takes its place (`Table.remove`). An entry never checked goes
first, so a node that just contacted us is checked within a round. -/
private def revalidateOnce (n : Node) : Async Unit := do
  let s ← (n.core.get : BaseIO State)
  let checked ← (n.checked.get : BaseIO (Std.HashMap Nat Nat))
  let pick (best : Option (Entry × Nat)) (e : Entry) : Option (Entry × Nat) :=
    let t := (checked.get? (idNat e.id)).getD 0
    match best with
    | some (_, bt) => if t < bt then some (e, t) else best
    | none => some (e, t)
  let some (e, _) := s.table.entries.foldl pick none | return
  let now ← (IO.monoMsNow : IO Nat)
  (n.checked.update (·.insert (idNat e.id) now) : BaseIO Unit)
  match ← n.ping e.record 1000 with
  | none =>
    (n.core.update fun s => { s with table := s.table.remove e.id } : BaseIO Unit)
    (n.checked.update (·.erase (idNat e.id)) : BaseIO Unit)
  | some (.pong _ seq _ _) =>
    -- "When the PONG response indicates that a new version of the node
    -- record is available, the liveness check should pull the new record"
    -- (discv5-theory.md, "Table Maintenance In Practice").
    if e.record.seq < seq then
      for r in ← n.findNode e.record [0] 1000 do
        if r.nodeId == e.id then (n.addEnr r : BaseIO Unit)
  | some _ => pure ()

/-- The maintenance task (discv5-theory.md, "Table Maintenance In
Practice"): one liveness check every `revalidateMs`, and every
`refreshEvery` rounds a lookup toward a random target, which refreshes
the table. Park: the timer wakes it, and so does `stop`, which closes
`stopping`. `partial`, as the IO loops are. -/
private partial def revalidator (n : Node) (round : Nat := 0) : Async Unit := do
  let timer ← (Park.sleep n.revalidateMs false : BaseIO (Park Bool))
  if ← select #[Park.recv n.stopping (fun _ => true), timer] then return
  n.revalidateOnce
  if (round + 1) % refreshEvery == 0 then
    discard <| n.lookup (← (random 32 : IO ByteArray))
  n.revalidator (round + 1)

/-- Start a node with `key`, bound to `ip`:`port` (0 for the system's
pick). Its record is signed after the bind, so `udp` names the real
port; `extra` adds the client's pairs, such as `eth2` and `tcp`.
`revalidateMs` paces the liveness checks of the table. -/
def start (key : Crypto.Key32) (ip : List Nat) (port : Nat) (extra : List Enr.Pair := [])
    (seq : Nat := 1) (revalidateMs : Nat := 1000) : Async Node := do
  let socket ← (Streams.Udp.bind ip port : IO Streams.Udp.Socket)
  -- An IPv6 bind names itself in `ip6` and `udp6`.
  let (ipKey, portKey) : Enr.Key × Enr.Key := if ip.length == 16 then (.ip6, .udp6) else (.ip, .udp)
  let pairs : List Enr.Pair :=
    [⟨ipKey, .bytes ip⟩, ⟨portKey, .bytes (Rlp.ofScalar socket.port)⟩] ++
      extra.filter fun p => p.key != ipKey && p.key != portKey
  let record ← match Enr.sign key seq pairs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"discv5: the record does not sign ({repr e})")
  let n : Node := {
    core := ← OnceRef.new (Core.init key record), socket
    waiters := ← OnceRef.new [], nextId := ← OnceRef.new 1, tasks := ← TaskSet.new
    stopping := ← Chan.new 1, checked := ← OnceRef.new {}, revalidateMs
    port := socket.port }
  n.tasks.spawn n.reader
  n.tasks.spawn n.revalidator
  return n

end Node

end Libp2p.Discv5
