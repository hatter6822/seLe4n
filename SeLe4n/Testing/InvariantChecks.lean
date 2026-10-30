-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

namespace SeLe4n.Testing

private def lookupQueueTcbB (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  -- AK7-F.reader.hygiene: delegate to AL2-A typed helper.
  st.getTcb? tid

/-- V8-E: Fuel-bounded intrusive queue reachability check.
    Replaces `partial` with structural recursion on `fuel : Nat`.
    Returns `true` iff every node from `cursor` to `tail` is reachable
    with consistent prev/pprev links and no cycles. -/
private def intrusiveQueueReachable
    (st : SystemState)
    (tail : SeLe4n.ThreadId)
    (expectedPrev : Option SeLe4n.ThreadId)
    (expectedPPrev : Option QueuePPrev)
    (cursor : Option SeLe4n.ThreadId)
    (visited : List SeLe4n.ThreadId)
    (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match cursor with
      | none => false
      | some tid =>
          if tid ∈ visited then
            false
          else
            match lookupQueueTcbB st tid with
            | none => false
            | some tcb =>
                if tcb.queuePrev != expectedPrev || tcb.queuePPrev != expectedPPrev then
                  false
                else if tid == tail then
                  tcb.queueNext.isNone
                else
                  match tcb.queueNext with
                  | none => false
                  | some nextTid =>
                      intrusiveQueueReachable st tail (some tid) (some (.tcbNext tid)) (some nextTid) (tid :: visited) fuel

private def intrusiveQueueWellFormedB (st : SystemState) (q : IntrusiveQueue) : Bool :=
  match q.head, q.tail with
  | none, none => true
  | some head, some tail =>
      match lookupQueueTcbB st head, lookupQueueTcbB st tail with
      | some headTcb, some tailTcb =>
          headTcb.queuePrev.isNone
            && headTcb.queuePPrev = some .endpointHead
            && tailTcb.queueNext.isNone
            && intrusiveQueueReachable st tail none (some .endpointHead) (some head) [] (st.objectIndex.length + 1)
      | _, _ => false
  | _, _ => false

/-- WS-H12a: Dual-queue endpoint well-formedness check (Boolean).
Verifies head/tail consistency for both sendQ and receiveQ. -/
private def endpointDualQueueWellFormedB (st : SystemState) (ep : Endpoint) : Bool :=
  intrusiveQueueWellFormedB st ep.sendQ && intrusiveQueueWellFormedB st ep.receiveQ

private def notificationQueueWellFormedB (ntfn : Notification) : Bool :=
  match ntfn.state with
  | .idle => ntfn.waitHead.isNone && !ntfn.pendingBadge.isSome
  | .waiting => ntfn.waitHead.isSome && !ntfn.pendingBadge.isSome
  | .active => ntfn.waitHead.isNone && ntfn.pendingBadge.isSome

private def schedulerQueueCurrentConsistentB (st : SystemState) : Bool :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => true
  | some tid => !(st.queuedOn bootCoreId tid)

private def schedulerRunQueueUniqueB (st : SystemState) : Bool :=
  (st.runQueueWalk bootCoreId).Nodup

private def currentThreadValidB (st : SystemState) : Bool :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => true
  | some tid =>
      -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
      (st.getTcb? tid).isSome

/-- V8-G7: ThreadState consistency check — every TCB's `threadState` field
matches the inferred state from queue membership, IPC state, and scheduler.current.

**Design note**: `assertStateInvariantsFor` calls `syncThreadStates` before
running these checks.  This means the check validates the *inference logic*
(i.e., `inferThreadState` is self-consistent and the sync round-trip is
idempotent) rather than detecting operational drift between threadState and
runtime queues.  The check is intentionally a design-consistency assertion,
not a divergence detector. -/
private def threadStateConsistentChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        let expected := SeLe4n.Kernel.inferThreadState st ⟨oid.toNat⟩ tcb
        (s!"threadState consistent: oid={oid} actual={reprStr tcb.threadState} expected={reprStr expected}",
         tcb.threadState == expected) :: acc
    | none => acc) []

/-- **WS-RR RR7.36**: the *live* thread-state relation, checked on the state as
it stands rather than after a `syncThreadStates` round trip.

`threadStateConsistentChecks` above is a design-consistency assertion because
its caller syncs first, and it has to be: `threadStateConsistent` is a
boot-state theorem and false after any core's first dispatch (no scheduler
dispatch writes `.Running`, no rendezvous writes a `.Blocked*`).  The relation
the live decisions actually read is narrower — `tcbSuspend` / `tcbResume` / the
cross-core cancellation / the fault suspend all test the stored field against
`.Inactive` only — and that one **is** preserved by the dispatch
(`switchToThreadOnCore_preserves_threadInactiveFlagConsistent`).  So this check
is a genuine divergence detector on states the full one cannot speak about, and
it is what makes `assertLiveThreadStateInvariants` below meaningful. -/
def threadInactiveFlagConsistentChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        let inferred := SeLe4n.Kernel.inferThreadState st ⟨oid.toNat⟩ tcb
        (s!"inactive flag consistent: oid={oid} stored={reprStr tcb.threadState} \
inferred={reprStr inferred}",
         (tcb.threadState == .Inactive) == (inferred == .Inactive)) :: acc
    | none => acc) []

/-- **WS-RR RR7.36**: the same relation as a single boolean, for suites that
want to assert it of a state directly. -/
def threadInactiveFlagConsistentBool (st : SystemState) : Bool :=
  (threadInactiveFlagConsistentChecks st.objectIndex st).all (·.2)

/-- **WS-RR RR8.3**: `queuePPrevAgreesWithPrev`, the fourth conjunct of
`dualQueueSystemInvariant`, as a runtime check.

`queuePPrev` carries exactly one bit beyond `queuePrev` — whether the node is
linked into a queue at all — and every other bit of it must agree with
`queuePrev`.  Nothing checked that before RR8.3, and *that* is why WS-OD OD1.1
and OD3.9 each found a removal writing `queuePrev` without its partner: no
`ipcInvariantFull` conjunct read the field, so a stranded successor was invisible
to both the proofs and the harness. -/
def queuePPrevAgreesWithPrevChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        let ok : Bool :=
          match tcb.queuePPrev with
          -- `v0.35.99`: `none` says the thread is on no queue, so it claims
          -- `queuePrev = none` rather than nothing.  It read `true` here and in
          -- the Prop-level predicate, which admitted a queued thread carrying no
          -- back-pointer -- one the dual removal refuses outright and can never
          -- dequeue.
          | none => tcb.queuePrev.isNone
          | some .endpointHead => tcb.queuePrev.isNone
          | some (.tcbNext p) => tcb.queuePrev == some p
        (s!"queuePPrev agrees with queuePrev: oid={oid} prev={reprStr tcb.queuePrev} \
pprev={reprStr tcb.queuePPrev}", ok) :: acc
    | none => acc) []

/-- **WS-RR RR8.3**: the same relation as a single boolean, for suites that assert
it of a state directly — and for the witnesses that show a corrupted back-pointer
fails it. -/
def queuePPrevAgreesWithPrevBool (st : SystemState) : Bool :=
  (queuePPrevAgreesWithPrevChecks st.objectIndex st).all (·.2)

/-- **PR #897 review (`v0.35.108`)**: the FIFTH `dualQueueSystemInvariant`
conjunct — a thread heads at most one endpoint queue, counting a send queue and a
receive queue as different queues.

`v0.35.106` added the conjunct and added no runtime check, one cut after RR8.3
had recorded the rule that a conjunct is *checked at runtime, not only proved*.
The gap was not narrow: **nothing** in `stateInvariantChecksFor` is cross-endpoint
(`endpointDualQueueWellFormedB` is literally the two per-queue checks of one
endpoint) and nothing ties an endpoint queue's head to its own `ipcState`.  So two
endpoints each holding `{head := some t, tail := some t}`, with `t` carrying
`(queuePrev := none, queuePPrev := some .endpointHead, queueNext := none)`, passed
every check while the proof bundle refuses the state — and popping either queue
then clears `t`'s links and strands the other.

The check is per occupied head and asks whether any **other** `(endpoint, kind)`
claims the same one, so it is robust to a repeated object id in `objectIds`
(comparing against "exactly one" would mis-report a duplicated index entry as a
violation).  It says which two queues collide, because the whole content of a
disjointness failure is *which* pair. -/
def endpointQueueHeadDisjointChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  let heads : List (SeLe4n.ObjId × Bool × SeLe4n.ThreadId) :=
    objectIds.foldr (fun oid acc =>
      match st.getEndpoint? oid with
      | some ep =>
          let withSend :=
            match ep.sendQ.head with
            | some hd => (oid, false, hd) :: acc
            | none    => acc
          match ep.receiveQ.head with
          | some hd => (oid, true, hd) :: withSend
          | none    => withSend
      | none => acc) []
  heads.foldr (fun e acc =>
    let others := heads.filter (fun f => f.2.2 == e.2.2 && !(f.1 == e.1 && f.2.1 == e.2.1))
    (s!"endpoint queue heads disjoint: head={e.2.2.toNat} ep={e.1.toNat} \
recvQ={e.2.1} collides={others.map (fun f => (f.1.toNat, f.2.1))}", others.isEmpty) :: acc) []

/-- **PR #897 review (`v0.35.108`)**: the same relation as a single boolean, for
suites that assert it of a state directly — and for the witness that shows a
shared singleton head fails it while every queue stays well formed. -/
def endpointQueueHeadDisjointBool (st : SystemState) : Bool :=
  (endpointQueueHeadDisjointChecks st.objectIndex st).all (·.2)

/-- **WS-ZA ZA5.4 part 27**: `endpointQueueLinksOnlyBlocked`, the 21st
`ipcInvariantFull` conjunct, as a runtime check: a thread with an endpoint-queue
successor is blocked on an endpoint (send, receive or call).

seL4's `valid_objs` / `sym_refs` hold an unqueued TCB's endpoint links null; the
proof bundle states it next-only, and the final delete reads a thread's own
links on that strength.  It reports the thread and its state, because the whole
content of a failure is which thread kept a link it had no queue for. -/
def endpointQueueLinksOnlyBlockedChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        (s!"endpoint queue links only on blocked threads: oid={oid} \
next={reprStr tcb.queueNext} ipcState={reprStr tcb.ipcState}",
          tcb.queueNext.isNone || SeLe4n.Kernel.ipcStateEndpointQueued tcb.ipcState) :: acc
    | none => acc) []

/-- **WS-ZA ZA5.4 part 27**: the same relation as a single boolean, for the
witness that shows a ready thread carrying a queue successor fails it. -/
def endpointQueueLinksOnlyBlockedBool (st : SystemState) : Bool :=
  (endpointQueueLinksOnlyBlockedChecks st.objectIndex st).all (·.2)

/-- **WS-ZA ZA5.4 part 27**: `donationChainWellFormed.nextLinkReciprocal` as a
runtime check: a reply frame linking up to a frame above is answered by that
frame's `prev` (seL4's `sym_refs` over `replyNext` / `replyPrev`).

One row per Reply carrying an upward `.frame` link, so a state with no reply
stacks adds none.  A failing row names both frames, because the content of a
failure is which link dangles: the frame above may be freed by its final delete
while the frame below still names it. -/
def replyNextLinkReciprocalChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getReply? ⟨oid.toNat⟩ with
    | some r =>
        match r.next with
        | some (.frame above) =>
            (s!"reply next link reciprocal: oid={oid} above={above.toObjId}",
              (st.getReply? above).any (fun a => a.prev == some ⟨oid.toNat⟩)) :: acc
        | _ => acc
    | none => acc) []

/-- **WS-ZA ZA5.4 part 27**: the same relation as a single boolean, for the
witness that shows a frame naming a frame above that no longer names it back
fails it. -/
def replyNextLinkReciprocalBool (st : SystemState) : Bool :=
  (replyNextLinkReciprocalChecks st.objectIndex st).all (·.2)

/-- M-11 CSpace coherency: every capability slot — a CNode's slot or a thread's
space slot — whose capability targets an object has that
object present in the object store — and, where the capability names the object's
*kind*, an object of that kind.

Three arms, and the difference between them is what each capability form claims.
An `.object` target claims only that something is there, so the kind-agnostic
`getObject?` is the reader that says it.  A `.cnodeSlot` names the CNode it
descends and a `.replyCap` names a Reply, so those read the typed accessor: a
capability pointing at an object of the wrong kind is not backed *for the purpose
this check states*, and reporting it as backed would be the check agreeing with a
dangling descent.  No fixture in the tree installs a `.cnodeSlot` capability whose
target is a non-CNode, so the discriminating case is unexercised; the arm is
stated this way because it is what the claim means, not because a test drove it. -/
private def slotTargetBacked (st : SystemState) (cap : Capability) : Bool :=
  match cap.target with
  -- Kind-agnostic by intent: the claim is that *some* object backs
  -- the target, whatever its variant, so `getObject?` is the reader
  -- that says it.
  | .object targetId => (st.getObject? targetId).isSome
  -- A `.cnodeSlot` names the CNode it descends, so the typed read is
  -- the stronger and the honest one: a capability pointing at a
  -- non-CNode is not backed for this purpose.
  | .cnodeSlot cnId _ => (st.getCNode? cnId).isSome
  -- WS-SM SM6.D: a reply cap must target an actual `.reply` object, not
  -- merely *some* object sharing that ObjId namespace — `getReply?`
  -- returns `some` only for a `.reply` at `rid.toObjId`.
  | .replyCap rid => (st.getReply? rid).isSome
  -- WS-SM SM9.A.9: an audit-trail capability names no object, so
  -- there is nothing in the store for it to be backed by.  Vacuously
  -- coherent — and deliberately not "check the trail exists", since a
  -- `SystemState` always has one.
  | .auditTrail => true
  -- WS-ZA ZA6.4: a scheduling-control capability names a core, not an object.
  | .schedControl _ => true

/-- One check per occupied capability slot of every listed object: a CNode's
slots and a thread's two space slots, read as `KernelObject.slotCap` reads them. -/
private def objectSlotChecks (objectIds : List SeLe4n.ObjId) (st : SystemState)
    (check : SeLe4n.ObjId → SeLe4n.Slot → Capability → String × Bool) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getObject? oid with
    | some (.cnode cn) => cn.foldCells acc (fun inner slot cap => check oid slot cap :: inner)
    | some (.tcb t) => t.spaceSlotCaps.foldr (fun p inner => check oid p.1 p.2 :: inner) acc
    | _ => acc) []

/-- M-11 CSpace coherency over every listed object's slots (`slotTargetBacked`). -/
private def cspaceSlotCoherencyChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectSlotChecks objectIds st fun oid slot cap =>
    (s!"cspace slot target backed: oid={oid} slot={slot}", slotTargetBacked st cap)

/-- **WS-RR RR8.16** (`v0.35.201`): every occupied slot of a CNode is addressable
by that CNode's own radix width.

`cspaceSlotCountBounded` — `cn.slots.size ≤ cn.slotCount` — was a conjunct of
`capabilityInvariantBundle` (a theorem since WS-ZA ZA5.3's fixed slot array),
and **nothing here asserted it**: the word
`slotCountBounded` appeared nowhere under `SeLe4n/Testing/`.  That is how six
fixture CNodes came to declare `radixWidth := 0` — *one* slot — while holding
capabilities at indices up to 12, the trace harness's own bootstrap root CSpace
among them.  `CNode.resolveSlot` masks with `2 ^ radixWidth`, so each of those
capabilities was unreachable by any CPtr while still consuming a slot-table
entry in an object whose memory was accounted, at retype time, by
`2 ^ radixWidth` slots.

The check is the **structural** property rather than the cardinality: slot keys
are unique (`UniqueSlotMap`), so "every occupied index is below `slotCount`"
entails the count bound, and unlike the count it names the offending slot —
which is the whole content of such a failure. -/
private def cspaceSlotAddressableChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getCNode? oid with
    | some cn =>
        cn.foldCells acc (fun inner slot _ =>
          (s!"cspace slot addressable: oid={oid} slot={slot} slotCount={cn.slotCount}",
            cn.slotAddressable slot) :: inner)
    | _ => acc) []

/-- M-11 Capability rights attenuation: minted (badge-carrying) capabilities must have
rights that are a subset of the source capability's rights. Since the source is not
tracked at runtime, we validate that badge-carrying caps have non-empty rights and
rights belong to the canonical set. This is a conservative structural check. -/
private def capabilityRightsStructuralChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectSlotChecks objectIds st fun oid slot cap =>
    let ok := match cap.badge with
      | some _ => cap.rights.bits != 0  -- WS-F5/D2: non-empty rights (bitmask)
      | none => true
    (s!"capability badge implies non-empty rights: oid={oid} slot={slot}", ok)

/-- M-11 Lifecycle metadata consistency: when lifecycle objectType metadata is present
for a materialized object, it must agree with the actual object type. -/
private def lifecycleMetadataChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getObject? oid, st.lifecycle.objectTypes[oid]? with
    | some obj, some metaTy =>
        (s!"lifecycle objectType metadata consistent: oid={oid}", metaTy == obj.objectType) :: acc
    | _, _ => acc) []

/-- M-11 VSpace ASID uniqueness: no two VSpace root objects share the same ASID. -/
private def vspaceAsidUniquenessChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  let roots : List (SeLe4n.ObjId × SeLe4n.ASID) := objectIds.filterMap fun oid =>
    match st.getVSpaceRoot? oid with
    | some root => some (oid, root.asid)
    | none => none
  roots.map fun (oid, asid) =>
    let duplicates := roots.filter fun (oid', asid') => asid' == asid && oid' != oid
    (s!"vspace ASID unique: oid={oid} asid={asid.toNat}", duplicates.isEmpty)

/-- WS-G3/F-P06: ASID table consistency: for every VSpaceRoot, the asidTable maps its ASID
to the correct ObjId, and every asidTable entry points to a valid VSpaceRoot. -/
private def asidTableConsistencyChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  -- Completeness: every VSpaceRoot has its ASID in the table
  let completenessChecks := objectIds.filterMap fun oid =>
    match st.getVSpaceRoot? oid with
    | some root =>
        let ok := st.asidTable[root.asid]? == some oid
        some (s!"asidTable completeness: oid={oid} asid={root.asid.toNat}", ok)
    | none => none
  -- Soundness: every asidTable entry points to a valid VSpaceRoot with matching ASID
  let soundnessChecks := objectIds.filterMap fun oid =>
    match st.getVSpaceRoot? oid with
    | some root =>
        match st.asidTable[root.asid]? with
        | some tableOid =>
            let ok := tableOid == oid
            some (s!"asidTable soundness: asid={root.asid.toNat} → oid={oid}", ok)
        | none =>
            some (s!"asidTable soundness: asid={root.asid.toNat} missing", false)
    | none => none
  completenessChecks ++ soundnessChecks

/-- WS-F2, WS-ZA ZA5.4: untyped free-index validity, read from the capabilities
(seL4's `untyped_inc`): every CNode slot naming an untyped carries a free index
within the region with the untyped's children below it, and at most one of the
capabilities naming an untyped is not full (the sole carver). -/
private def untypedFreeIndexChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  let untypedCaps : List (SeLe4n.ObjId × UntypedObject × Nat) :=
    objectIds.foldr (fun cnId acc =>
      match st.getCNode? cnId with
      | some cn =>
          cn.cells.toList.foldr (fun cell acc' =>
            match cell with
            | some cap =>
                match cap.target with
                | .object oid =>
                    match st.getUntyped? oid with
                    | some ut => (oid, ut, cap.freeIndex) :: acc'
                    | none => acc'
                | _ => acc'
            | none => acc') acc
      | none => acc) []
  let perCap := untypedCaps.foldr (fun (oid, ut, idx) acc =>
    (s!"untyped free index valid: oid={oid}", decide (idx ≤ ut.regionSize)) ::
    (s!"untyped children below free index: oid={oid}",
      ut.children.all fun c => c.offset + c.size ≤ idx) :: acc) []
  let soleCarver := objectIds.foldr (fun oid acc =>
    match st.getUntyped? oid with
    | some ut =>
        (s!"untyped sole carver: oid={oid}",
          decide ((untypedCaps.filter fun (o, _, idx) => o == oid && idx != ut.regionSize).length ≤ 1))
          :: acc
    | none => acc) []
  perCap ++ soleCarver

/-- WS-G7, WS-ZA ZA4.4: is `t` a TCB blocked on notification `oid`? -/
private def blockedOnNotificationB (st : SystemState) (oid : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? t with
  | some tcb => tcb.ipcState == .blockedOnNotification oid
  | none => false

/-- WS-ZA ZA4.4: walk a notification's waiter queue from its head along the
successor links, at most `fuel` steps. -/
private def notificationQueueWalk (st : SystemState) :
    Nat → Option SeLe4n.ThreadId → List SeLe4n.ThreadId
  | 0, _ => []
  | _ + 1, none => []
  | fuel + 1, some t => t :: notificationQueueWalk st fuel ((st.getTcb? t).bind (·.ntfnNext))

/-- WS-G7, WS-ZA ZA4.4: runtime check for `notificationWaiterConsistent`, clause
by clause.  Each notification's queue ends are both present or both absent, are
TCBs blocked on it, and the tail has no successor; each TCB blocked on a
notification is its head or has a predecessor linking back to it, is its tail
when it has no successor, a successor it has links back to it, and it is reached
by walking the queue from the head.  A queue's head has no predecessor, and a
TCB blocked on no notification holds no notification link (PR #932 review). -/
private def notificationWaiterConsistentChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getNotification? oid with
    | some ntfn =>
        let endsOk :=
          (ntfn.waitHead.isNone == ntfn.waitTail.isNone) &&
          ntfn.waitHead.all (blockedOnNotificationB st oid) &&
          ntfn.waitTail.all (fun t => blockedOnNotificationB st oid t &&
            ((st.getTcb? t).bind (·.ntfnNext)).isNone) &&
          ntfn.waitHead.all (fun h => ((st.getTcb? h).bind (·.ntfnPrev)).isNone)
        (s!"notification queue ends consistent: oid={oid}", endsOk) :: acc
    | none =>
      match st.getTcb? (SeLe4n.ThreadId.ofNat oid.toNat) with
      | some tcb =>
        match tcb.ipcState with
        | .blockedOnNotification n =>
          let tid := SeLe4n.ThreadId.ofNat oid.toNat
          let ok := match st.getNotification? n with
            | some ntfn =>
                (ntfn.waitHead == some tid ||
                  tcb.ntfnPrev.any (fun a => blockedOnNotificationB st n a &&
                    ((st.getTcb? a).bind (·.ntfnNext)) == some tid)) &&
                (tcb.ntfnNext.isSome || ntfn.waitTail == some tid) &&
                tcb.ntfnNext.all (fun b => ntfn.waitHead != some b &&
                  blockedOnNotificationB st n b &&
                  ((st.getTcb? b).bind (·.ntfnPrev)) == some tid) &&
                (notificationQueueWalk st (objectIds.length + 1) ntfn.waitHead).contains tid
            | none => false
          (s!"notification waiter linked consistently: tid={oid}", ok) :: acc
        | _ =>
          (s!"unblocked thread holds no notification link: tid={oid}",
            tcb.ntfnPrev.isNone && tcb.ntfnNext.isNone) :: acc
      | none => acc) []

/-- WS-ZA ZA4.6: runtime check for `SystemState.replyWaitersConsistent`.  Each
thread's reply-waiter queue, walked from its head one step past its recorded
length, has exactly that length, holds no thread twice, links each waiter back
to the one before it and holds only threads reply-blocked on it; every thread
reply-blocked on it is in it.  A thread waits on no reply from itself, the
server it waits on is a live thread, and a thread waiting on no reply holds no
reply-waiter link. -/
private def replyWaitersConsistentChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    let tid := SeLe4n.ThreadId.ofNat oid.toNat
    match st.getTcb? tid with
    | none => acc
    | some tcb =>
        let q := st.replyWaitersWalk (tcb.replyWaitersCount + 1) tcb.replyWaitersHead
        let waitsOn (w : SeLe4n.ThreadId) : Bool :=
          (st.getTcb? w).any (·.blockingServer? == some tid)
        let queueOk :=
          q.length == tcb.replyWaitersCount && q.eraseDups.length == q.length &&
          q.all waitsOn &&
          ((none :: q.map some).zip q).all (fun (p, w) =>
            (st.getTcb? w).any (·.replyWaiterPrev == p)) &&
          objectIds.all (fun o =>
            let w := SeLe4n.ThreadId.ofNat o.toNat
            !waitsOn w || q.contains w)
        let selfOk :=
          tcb.blockingServer? != some tid &&
          tcb.blockingServer?.all (fun s => (st.getTcb? s).isSome) &&
          (tcb.blockingServer?.isSome || (tcb.replyWaiterPrev.isNone && tcb.replyWaiterNext.isNone))
        (s!"reply-waiter queue consistent: tid={oid}", queueOk && selfOk) :: acc) []

/-- WS-G4: RunQueue internal consistency — every thread the boot core's queue
    walks to, along its TCB's run-queue links, records a priority and sits in
    that priority's bucket walk.  The link agreement maintains this
    structurally, but we verify it at runtime as a safety net. -/
private def runQueueThreadPriorityConsistentB (st : SystemState) : Bool :=
  let e := st.scheduler.runQueueEndsOnCore bootCoreId
  (st.runQueueWalk bootCoreId).all fun tid =>
    match st.queuedPriorityOn bootCoreId tid with
    | some p =>
        (SeLe4n.Kernel.LinkedQueue.walk (fun t => (st.runLinkOn bootCoreId t).bucketNext) e.size
          (SeLe4n.Kernel.RunQueue.endsOf e.buckets p).head).contains tid
    | none => false

/-- WS-F7/D1a: Threads blocked on endpoint send must not appear in the runnable list.
A blocked sender dispatched prematurely could cause message duplication or ordering violations. -/
private def blockedOnSendNotRunnableChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnSend _ =>
            let ok := !(st.queuedOn bootCoreId tcb.tid)
            (s!"blockedOnSend not runnable: tid={tcb.tid.toNat}", ok) :: acc
        | .blockedOnCall _ =>
            let ok := !(st.queuedOn bootCoreId tcb.tid)
            (s!"blockedOnCall not runnable: tid={tcb.tid.toNat}", ok) :: acc
        | _ => acc
    | none => acc) []

/-- WS-F7/D1a: Threads blocked on endpoint receive must not appear in the runnable list.
A blocked receiver dispatched prematurely could observe partial state. -/
private def blockedOnReceiveNotRunnableChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReceive _ =>
            let ok := !(st.queuedOn bootCoreId tcb.tid)
            (s!"blockedOnReceive not runnable: tid={tcb.tid.toNat}", ok) :: acc
        | .blockedOnReply _ _ =>
            let ok := !(st.queuedOn bootCoreId tcb.tid)
            (s!"blockedOnReply not runnable: tid={tcb.tid.toNat}", ok) :: acc
        | .blockedOnNotification _ =>
            let ok := !(st.queuedOn bootCoreId tcb.tid)
            (s!"blockedOnNotification not runnable: tid={tcb.tid.toNat}", ok) :: acc
        | _ => acc
    | none => acc) []

/-- V3-G1: the executable mirror of `blockedThreadsPendingMessageConsistent` —
no blocked thread holds a message.

A thread parked to *collect* holds nothing, and (WS-ZA ZA4.7) neither does a
thread parked to *deliver*: a blocked sender keeps its message in its saved
registers and IPC buffer, and the receive that takes it reads it there
(`blockedSenderMessage`), as seL4 does. -/
private def blockedThreadPendingMessageChecks (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  objectIds.foldr (fun oid acc =>
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReceive _ =>
            (s!"blockedOnReceive holds no message: tid={tcb.tid.toNat}",
              tcb.pendingMessage.isNone) :: acc
        | .blockedOnNotification _ =>
            (s!"blockedOnNotification holds no message: tid={tcb.tid.toNat}",
              tcb.pendingMessage.isNone) :: acc
        | .blockedOnSend _ =>
            (s!"blockedOnSend holds no message: tid={tcb.tid.toNat}",
              tcb.pendingMessage.isNone) :: acc
        | .blockedOnCall _ =>
            (s!"blockedOnCall holds no message: tid={tcb.tid.toNat}",
              tcb.pendingMessage.isNone) :: acc
        | _ => acc
    | none => acc) []

/-- WS-F7/D1b: If a thread is currently dispatched, its TCB domain must match the
scheduler's `activeDomain`. Violation would break domain-based temporal isolation. -/
private def currentThreadInActiveDomainB (st : SystemState) : Bool :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => true
  | some tid =>
      -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
      match st.getTcb? tid with
      | some tcb => tcb.domain == (st.scheduler.activeDomainOnCore bootCoreId)
      | none => true  -- missing TCB caught by currentThreadValidB

/-- WS-F7/D1c, WS-ZA ZA4.4: no thread appears twice across the notification
wait queues, walked from each head along the TCB links.  A thread on two queues,
or a queue that loops back on itself, could be double-woken.  The walk is
bounded by the object count, so a loop shows up as a repeat. -/
private def uniqueWaitersCheck (objectIds : List SeLe4n.ObjId) (st : SystemState) : List (String × Bool) :=
  -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
  let allWaiters : List SeLe4n.ThreadId := objectIds.foldr (fun oid acc =>
    match st.getNotification? oid with
    | some ntfn => notificationQueueWalk st (objectIds.length + 1) ntfn.waitHead ++ acc
    | none => acc) []
  if allWaiters.isEmpty then []
  else
    let hasDuplicates := !allWaiters.Nodup
    [("notification waiters globally unique", !hasDuplicates)]

/-- **Every slot whose links the store holds**: each CNode's slots (one per
`slotLinkWords` link words) and each thread's two space slots.  It walks the
store itself rather than the object index, so an object the index does not list
still counts. -/
def objectLinkSlots (st : SystemState) : List SlotRef :=
  st.objects.fold [] fun acc oid obj =>
    match obj with
    | .cnode cn =>
        (List.range (cn.links.size / slotLinkWords)).foldr (fun i acc =>
          { cnode := oid, slot := SeLe4n.Slot.ofNat i } :: acc) acc
    | .tcb _ =>
        { cnode := oid, slot := SeLe4n.Slot.ofNat 0 } ::
          { cnode := oid, slot := SeLe4n.Slot.ofNat 1 } :: acc
    | _ => acc

/-- **The derivation edges the slot links name**, as (parent, child) pairs read
from the stored words: one for each slot (`objectLinkSlots`) whose parent link
is set.  Since WS-ZA ZA5.3 part 5 the tree's edges are a ghost, so tests read
the tree through the links that agree with it (`LinksAgree`). -/
def linkedDerivationEdges (st : SystemState) : List (SlotRef × SlotRef) :=
  (objectLinkSlots st).filterMap fun r => (st.slotLinkAt r .parent).map (·, r)

/-- Whether the slot links place `r` in the derivation tree: it has a parent, a
child or a sibling. -/
def linkMentions (st : SystemState) (r : SlotRef) : Bool :=
  (st.slotLinkAt r .parent).isSome || (st.slotLinkAt r .firstChild).isSome ||
    (st.slotLinkAt r .next).isSome || (st.slotLinkAt r .prev).isSome

/-- Every slot that holds a derivation link (`objectLinkSlots`, `linkMentions`). -/
def linkedSlots (st : SystemState) : List SlotRef :=
  (objectLinkSlots st).filter (linkMentions st)

/-- Runtime check of the derivation links each slot holds (seL4's mapping
database), read from the stored words alone: since WS-ZA ZA5.3 part 5 the tree
they agree with (`LinksAgree`) is a ghost.  The tree is the parent links
(`linkedDerivationEdges`); every other link must agree with it.  Read over every
slot of the object store, a CNode's or a thread's (`objectLinkSlots`):

- at each linked slot, the links agree locally: a next sibling names this slot
  as its previous one and shares its parent, a previous sibling names this slot
  as its next one, a slot with no previous sibling is its parent's first child,
  and a first child names this slot as its parent and has no previous sibling;
- the slots with no parent form sibling chains: the chains from the linked
  slots with no parent and no previous sibling end, repeat no slot between
  them, and list every linked slot with no parent (the boot builds one chain;
  a parentless slot no chain lists is a root alone, as `LinksAgree` allows);
- every linked slot, and every slot a link names, holds a capability
  (`cdtCompleteness`);
- each linked slot's parent chain reaches a root within one step per linked slot
  (`cdtAcyclicity`);
- for every slot that is named as a parent or names a first child, the chain
  from its first child along the next links ends, repeats no slot, and lists
  exactly the slots whose parent link names it, so the link walks a revoke takes
  find every child;
- the tree's edge bound covers the parent links, since the link walks and the
  revoke loop take their fuel from it. -/
private def cdtLinksConsistentCheck (st : SystemState) : List (String × Bool) :=
  let L := st.slotLinkAt
  let linked := linkedSlots st
  let edges := linkedDerivationEdges st
  let consistentAt (r : SlotRef) : Bool :=
    let up := L r .parent
    (match L r .next with
      | some s => L s .prev == some r && L s .parent == up
      | none => true) &&
    (match L r .prev with
      | some s => L s .next == some r
      | none => match up with
        | some p => L p .firstChild == some r
        | none => true) &&
    (match L r .firstChild with
      | some c => L c .parent == some r && (L c .prev).isNone
      | none => true)
  let occupied (r : SlotRef) : Bool := (st.slotCapAt r).isSome
  let namedOccupied (r : SlotRef) : Bool :=
    [LinkField.parent, .firstChild, .next, .prev].all fun f =>
      match L r f with
      | some x => occupied x
      | none => true
  let fuel := linked.length + 1
  let parentChainEnds (r : SlotRef) : Bool :=
    (List.range fuel).foldl (fun (cur : Option SlotRef) _ =>
      cur.bind fun x => L x .parent) (some r) |>.isNone
  let chainWalk (start : Option SlotRef) : Option (List SlotRef) :=
    let step := fun (acc : Option SlotRef × List SlotRef) (_ : Nat) =>
      match acc.1 with
      | some c => (L c .next, c :: acc.2)
      | none => acc
    let (rest, seen) := (List.range fuel).foldl step (start, [])
    if rest.isNone then some seen.reverse else none
  let childWalk (p : SlotRef) : Option (List SlotRef) := chainWalk (L p .firstChild)
  let roots := linked.filter fun r => (L r .parent).isNone
  let rootChains : Bool :=
    let walks := (roots.filter fun r => (L r .prev).isNone).map fun h => chainWalk (some h)
    if walks.all Option.isSome then
      let walk := walks.flatMap (·.getD [])
      walk.Nodup && walk.length == roots.length && walk.all roots.contains
    else false
  let parents : List SlotRef :=
    (edges.map (·.1) ++ linked.filter fun r => (L r .firstChild).isSome).eraseDups
  let listsChildren (p : SlotRef) : Bool :=
    let children := edges.filterMap fun e => if e.1 == p then some e.2 else none
    match childWalk p with
    | some walk => walk.Nodup && walk.length == children.length && walk.all children.contains
    | none => false
  [("cdt slot links fit together as a tree", linked.all consistentAt),
   ("cdt roots form sibling chains", rootChains),
   ("cdt linked slots hold capabilities", linked.all fun r => occupied r && namedOccupied r),
   ("cdt slot links form no cycle", linked.all parentChainEnds),
   ("cdt child chains list each parent's children", parents.all listsChildren),
   ("cdt edge bound covers the slot links", edges.length ≤ st.cdt.edgeBound)]

def stateInvariantChecksFor (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    List (String × Bool) :=
  let schedulerChecks : List (String × Bool) :=
    [ ("scheduler queue/current consistency", schedulerQueueCurrentConsistentB st)
    , ("scheduler runnable queue uniqueness", schedulerRunQueueUniqueB st)
    , ("scheduler current thread validity", currentThreadValidB st)
    , ("scheduler runQueue threadPriority consistency", runQueueThreadPriorityConsistentB st)
    , ("scheduler current thread in active domain", currentThreadInActiveDomainB st)
    ]
  let runnableChecks : List (String × Bool) :=
    (st.runQueueWalk bootCoreId).map fun tid =>
      let label := s!"runnable thread resolves to ready TCB: tid={tid.toNat}"
      -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
      let ok :=
        match st.getTcb? tid with
        | some tcb => tcb.ipcState == .ready
        | none => false
      (label, ok)
  let endpointAndNotificationChecks : List (String × Bool) :=
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    objectIds.foldr (fun oid acc =>
      match st.getEndpoint? oid with
      | some ep =>
          (s!"endpoint dual-queue invariant: oid={oid}", endpointDualQueueWellFormedB st ep) ::
          (s!"endpoint intrusive sendQ invariant: oid={oid}", intrusiveQueueWellFormedB st ep.sendQ) ::
          (s!"endpoint intrusive receiveQ invariant: oid={oid}", intrusiveQueueWellFormedB st ep.receiveQ) :: acc
      | none =>
          match st.getNotification? oid with
          | some ntfn =>
              (s!"notification queue/state invariant: oid={oid}", notificationQueueWellFormedB ntfn) :: acc
          | none => acc) []
  schedulerChecks ++ runnableChecks ++ endpointAndNotificationChecks
    ++ cspaceSlotCoherencyChecks objectIds st
    ++ cspaceSlotAddressableChecks objectIds st
    ++ capabilityRightsStructuralChecks objectIds st
    ++ lifecycleMetadataChecks objectIds st
    ++ vspaceAsidUniquenessChecks objectIds st
    ++ asidTableConsistencyChecks objectIds st
    ++ untypedFreeIndexChecks objectIds st
    ++ notificationWaiterConsistentChecks objectIds st
    ++ replyWaitersConsistentChecks objectIds st
    ++ cdtLinksConsistentCheck st
    ++ blockedOnSendNotRunnableChecks objectIds st
    ++ blockedThreadPendingMessageChecks objectIds st
    ++ blockedOnReceiveNotRunnableChecks objectIds st
    ++ uniqueWaitersCheck objectIds st
    ++ threadStateConsistentChecks objectIds st
    -- WS-RR RR7.36: the live (inactive-flag) relation is implied by the full
    -- classification, so on a synced state this is redundant and cheap; it
    -- earns its place because `stateInvariantChecksFor` is also the surface
    -- `assertStateInvariantsWithoutSync` runs, where the two differ.
    ++ threadInactiveFlagConsistentChecks objectIds st
    -- WS-RR RR8.3: the fourth `dualQueueSystemInvariant` conjunct.  It is what
    -- `endpointQueueRemoveDual`'s guard asks for, and until RR8.3 no conjunct and
    -- no runtime check read `queuePPrev` at all.
    ++ queuePPrevAgreesWithPrevChecks objectIds st
    -- PR #897 review (`v0.35.108`): and the FIFTH.  `v0.35.106` added the conjunct
    -- without its runtime check, one cut after RR8.3 recorded the rule that a
    -- conjunct is checked at runtime and not only proved -- and no other check in
    -- this list is cross-endpoint, so a head shared by two queues passed the whole
    -- surface while the bundle refuses it.
    ++ endpointQueueHeadDisjointChecks objectIds st
    -- WS-ZA ZA5.4 part 27: the 21st `ipcInvariantFull` conjunct.
    ++ endpointQueueLinksOnlyBlockedChecks objectIds st
    -- WS-ZA ZA5.4 part 27: the chain invariant's upward reciprocity.
    ++ replyNextLinkReciprocalChecks objectIds st

/--
Fallback invariant check surface for callers without an explicit object-id inventory.
Discovers materialized objects from `st.objectIndex` (the finite object store's
monotonic ID list) rather than scanning a hardcoded range.  See audit finding
F-10 and WS-D5.
-/
def stateInvariantChecks (st : SystemState) : List (String × Bool) :=
  stateInvariantChecksFor st.objectIndex st

private def failedChecks (checks : List (String × Bool)) : List String :=
  checks.filterMap fun (label, ok) => if ok then none else some label

/-- Check state invariants for the given object IDs, reporting failures as IO errors.

NOTE: Validates inference self-consistency (idempotency of `syncThreadStates`),
not operational drift.  See V8-G7 design note at `threadStateConsistentChecks`. -/
def assertStateInvariantsFor (label : String) (objectIds : List SeLe4n.ObjId) (st : SystemState) :
    IO Unit := do
  -- V8-G: Sync threadState fields before checking, since state may come from
  -- bootstrap builders or operations that don't maintain the field directly.
  let stSynced := SeLe4n.Kernel.syncThreadStates st
  let failures := failedChecks (stateInvariantChecksFor objectIds stSynced)
  if failures.isEmpty then
    pure ()
  else
    throw <| IO.userError s!"{label}: invariant checks failed: {reprStr failures}"

def assertStateInvariants (label : String) (st : SystemState) : IO Unit :=
  assertStateInvariantsFor label st.objectIndex st

/-- Like `assertStateInvariantsFor` but skips the `syncThreadStates` step,
enabling detection of operational drift between `threadState` fields and
runtime queue membership.  Use when you want to verify that a kernel
operation maintained threadState consistency on its own. -/
def assertStateInvariantsWithoutSync (label : String) (objectIds : List SeLe4n.ObjId)
    (st : SystemState) : IO Unit := do
  let failures := failedChecks (stateInvariantChecksFor objectIds st)
  if failures.isEmpty then
    pure ()
  else
    throw <| IO.userError s!"{label}: invariant checks failed (without sync): {reprStr failures}"

/-- **WS-RR RR7.36**: assert the *live* thread-state relation on the state as it
stands.

`assertStateInvariantsWithoutSync` runs the whole surface, which includes the
full classification `threadStateConsistentChecks` — true of a boot state and
false after any core's first dispatch, so it can only be called on quiescent
states.  This entry point runs the relation that survives a dispatch, so a
post-dispatch state can be checked at all.  Both exist because they are
different claims: one says the stored field equals the inferred classification,
the other says the field's `.Inactive` reading is right, which is what every
live decision consults. -/
def assertLiveThreadStateInvariantsFor (label : String) (objectIds : List SeLe4n.ObjId)
    (st : SystemState) : IO Unit := do
  let failures := failedChecks (threadInactiveFlagConsistentChecks objectIds st)
  if failures.isEmpty then
    pure ()
  else
    throw <| IO.userError
      s!"{label}: live thread-state (inactive flag) checks failed: {reprStr failures}"

/-- `assertLiveThreadStateInvariantsFor` over the state's own object index. -/
def assertLiveThreadStateInvariants (label : String) (st : SystemState) : IO Unit :=
  assertLiveThreadStateInvariantsFor label st.objectIndex st

-- ============================================================================
-- AG1-F + WS-AM AM4 audit remediation: Runtime crossSubsystemInvariant
-- checks (11 predicates — extended in WS-AM AM4 to cover the AL6-C
-- `lifecycleObjectTypeLockstep` 11th conjunct). Post-audit fix to close
-- the trace-harness coverage gap surfaced by the WS-AM end-to-end audit:
-- the Prop-level bundle was extended to 11 in AM4, but this boolean
-- runtime checker had remained at 10 until this remediation.
-- ============================================================================

/-- AG1-F audit: Collect queue members by following queueNext pointers.
Mirrors the private `collectQueueMembers` in CrossSubsystem.lean.
Returns `none` on fuel exhaustion (invariant violation signal). -/
private def collectQueueMembersB
    (st : SystemState) (start : Option SeLe4n.ThreadId) (fuel : Nat)
    : Option (List SeLe4n.ThreadId) :=
  match fuel, start with
  | 0, some _ => none
  | _, none => some []
  | fuel + 1, some tid =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? tid with
    | some tcb => (collectQueueMembersB st tcb.queueNext fuel).map (tid :: ·)
    | none => some [tid]

/-- AG1-F-i: Check noStaleEndpointQueueReferences — every thread ID in
endpoint queues (head, tail, AND interior members) has a live TCB. -/
private def checkNoStaleEndpointQueueRefs (st : SystemState) : Bool :=
  st.objectIndex.all fun oid =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getEndpoint? oid with
    | some ep =>
      let checkTid := fun tid => (st.getTcb? tid).isSome
      let headTailOk :=
        (ep.sendQ.head.all checkTid) && (ep.sendQ.tail.all checkTid) &&
        (ep.receiveQ.head.all checkTid) && (ep.receiveQ.tail.all checkTid)
      -- T5-I: Interior member validation via queueNext traversal
      let fuel := st.objectIndex.length
      let sendInteriorOk := match collectQueueMembersB st ep.sendQ.head fuel with
        | some members => members.all fun tid => (st.getTcb? tid).isSome
        | none => false  -- fuel exhaustion signals invariant violation
      let recvInteriorOk := match collectQueueMembersB st ep.receiveQ.head fuel with
        | some members => members.all fun tid => (st.getTcb? tid).isSome
        | none => false
      headTailOk && sendInteriorOk && recvInteriorOk
    | none => true

/-- AG1-F-i: Check noStaleNotificationWaitReferences — each end of every
notification wait queue is a live TCB. -/
private def checkNoStaleNotificationWaitRefs (st : SystemState) : Bool :=
  st.objectIndex.all fun oid =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getNotification? oid with
    | some ntfn =>
      ntfn.queueEnds.all fun tid => (st.getTcb? tid).isSome
    | none => true

/-- AG1-F-ii: Check schedContextStoreConsistent — every SchedContext referenced
by a TCB binding exists in the store. -/
private def checkSchedContextStoreConsistent (st : SystemState) : Bool :=
  st.objectIndex.all fun oid =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
      match tcb.schedContextBinding.scId? with
      | some scId => (st.getSchedContext? scId).isSome
      | none => true
    | none => true

/-- AG1-F-ii: Check schedContextNotDualBound — at most one thread references
any given SchedContext. Uses a simple O(n²) pairwise check. -/
private def checkSchedContextNotDualBound (st : SystemState) : Bool :=
  -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
  let bindings := st.objectIndex.filterMap fun oid =>
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
      match tcb.schedContextBinding.scId? with
      | some scId => some (oid, scId)
      | none => none
    | none => none
  bindings.all fun (oid1, scId1) =>
    bindings.all fun (oid2, scId2) =>
      oid1 == oid2 || scId1 != scId2

/-- AG1-F-ii: Check schedContextRunQueueConsistent — runnable SC-bound threads
have a live SchedContext with positive budget. -/
private def checkSchedContextRunQueueConsistent (st : SystemState) : Bool :=
  (st.runQueueWalk bootCoreId).all fun tid =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? tid with
    | some tcb =>
      match tcb.schedContextBinding.scId? with
      | some scId =>
        match st.getSchedContext? scId with
        | some sc => sc.budgetRemaining.val > 0
        | none => false
      | none => true  -- unbound threads pass vacuously
    | none => false

/-- AG1-F-iii: Check blockingAcyclic via bounded cycle detection.
Uses fuel = number of objects to bound the walk. -/
private def checkBlockingAcyclic (st : SystemState) : Bool :=
  let fuel := st.objectIndex.length
  st.objectIndex.all fun oid =>
    -- AK7-F.reader.hygiene: AL2-A typed helper adoption.
    match st.getTcb? ⟨oid.toNat⟩ with
    | some tcb =>
      match tcb.schedContextBinding with
      | .donated _ owner =>
        -- Walk the blocking chain from `owner`; if we see `oid` again, there's a cycle
        let rec walk (current : SeLe4n.ObjId) (visited : List SeLe4n.ObjId)
            (steps : Nat) : Bool :=
          match steps with
          | 0 => true  -- fuel exhaustion: conservative — assume OK
          | steps + 1 =>
            if current ∈ visited then false  -- cycle detected
            else
              match st.getTcb? ⟨current.toNat⟩ with
              | some tcb2 =>
                match tcb2.schedContextBinding with
                | .donated _ owner2 => walk owner2.toObjId (current :: visited) steps
                | _ => true  -- chain ends
              | none => true  -- chain ends
        walk owner.toObjId [oid] fuel
      | _ => true  -- not in a donation chain
    | none => true

/-- The registrations the endpoints record, each read off its endpoint — since
WS-ZA ZA5.9 the service registry is these records (`SystemState.serviceRegistry`). -/
private def recordedRegistrations (st : SystemState) : List ServiceRegistration :=
  st.objects.fold [] fun acc k o =>
    match o with
    | .endpoint ep => if ep.serviceRegistered then ep.service.registrationAt k :: acc else acc
    | _ => acc

/-- AG1-F audit: checkRegistryEndpointValid — every registered service's endpoint
targets an existing kernel object. -/
private def checkRegistryEndpointValid (st : SystemState) : Bool :=
  (recordedRegistrations st).all fun reg =>
    match reg.endpointCap.target with
    -- Kind-agnostic by intent: the AG1-F claim is that the endpoint capability
    -- names a live object, not that the object is an Endpoint.
    | .object epId => st.getObject? epId != none
    | _ => false

/-- AG1-F audit: checkRegistryInterfaceValid — every registered service references
a known interface specification. -/
private def checkRegistryInterfaceValid (st : SystemState) : Bool :=
  (recordedRegistrations st).all fun reg =>
    st.interfaceRegistry[reg.iface.ifaceId]? != none

/-- AM4 audit remediation: Runtime check for the AL6-C
`lifecycleObjectTypeLockstep` conjunct of `crossSubsystemInvariant`.
For every populated ObjId, the stored object's `objectType` must match
the recorded entry in `lifecycle.objectTypes`. Walks `objectIndex` once
and compares each entry pair; `true` when all match. -/
private def checkLifecycleObjectTypeLockstep (st : SystemState) : Bool :=
  -- Variant-agnostic by intent, so the kind-agnostic member of the typed
  -- accessor family is the reader that says it.
  st.objectIndex.all fun oid =>
    match st.getObject? oid with
    | some obj =>
      match st.lifecycle.objectTypes[oid]? with
      | some ty => ty == obj.objectType
      | none => false
    | none => true

/-- AG1-F-iv + WS-AM AM4 audit remediation: Compose the cross-subsystem
predicate checks into a single boolean function.  Returns `true` only if
all 9 checks pass. The `crossSub:lifecycleObjectTypeLockstep` check was
added by the WS-AM post-delivery audit to close the gap where the
Prop-level `crossSubsystemInvariant` had a conjunct this runtime check
did not exercise. -/
def checkCrossSubsystemInvariant (st : SystemState) : List (String × Bool) :=
  [ ("crossSub:registryEndpointValid", checkRegistryEndpointValid st)
  , ("crossSub:registryInterfaceValid", checkRegistryInterfaceValid st)
  , ("crossSub:noStaleEndpointQueueRefs", checkNoStaleEndpointQueueRefs st)
  , ("crossSub:noStaleNotificationWaitRefs", checkNoStaleNotificationWaitRefs st)
  , ("crossSub:schedContextStoreConsistent", checkSchedContextStoreConsistent st)
  , ("crossSub:schedContextNotDualBound", checkSchedContextNotDualBound st)
  , ("crossSub:schedContextRunQueueConsistent", checkSchedContextRunQueueConsistent st)
  , ("crossSub:blockingAcyclic", checkBlockingAcyclic st)
  , ("crossSub:lifecycleObjectTypeLockstep", checkLifecycleObjectTypeLockstep st) ]

/-- AG1-F-iv: Assert cross-subsystem invariants, throwing IO error on failure. -/
def assertCrossSubsystemInvariant (label : String) (st : SystemState) : IO Unit := do
  let checks := checkCrossSubsystemInvariant st
  let failures := checks.filterMap fun (name, ok) => if ok then none else some name
  if failures.isEmpty then
    pure ()
  else
    throw <| IO.userError s!"{label}: cross-subsystem invariant failed: {reprStr failures}"

/-- AN11-E.2 (TST-M02) — Bundled cross-subsystem invariant assertion.

Returns `true` iff every conjunct of `crossSubsystemInvariant` (currently
11; 12 once AN2-D / `typedIdDisjointness` lands) holds at the supplied
state.  Unlike `assertCrossSubsystemInvariant`, this variant does NOT
throw on the first failure — it walks the full check list and prints a
single composite failure report with EVERY failing conjunct.

Designed for trace-end / scenario-end validation in test harnesses where
a single failure should not mask other regressions; production proof-
chain code that needs early-fail semantics should keep using
`assertCrossSubsystemInvariant`. -/
def assertCrossSubsystemInvariants (st : SystemState) : IO Bool := do
  let checks := checkCrossSubsystemInvariant st
  let failures := checks.filterMap fun (name, ok) => if ok then none else some name
  if failures.isEmpty then
    return true
  else
    IO.println s!"assertCrossSubsystemInvariants: {failures.length}/{checks.length} conjuncts failed:"
    for name in failures do
      IO.println s!"  - {name}"
    return false

end SeLe4n.Testing
