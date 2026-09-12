-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.IPC.DualQueue

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- ============================================================================
-- Generic store/lookup transport lemmas
-- ============================================================================

theorem storeObject_objects_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[id]? = some obj := by
  unfold storeObject at hStore; cases hStore
  simp only [RHTable_getElem?_eq_get?]
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv

theorem storeObject_objects_ne
    (st st' : SystemState) (id oid : SeLe4n.ObjId) (obj : KernelObject)
    (hNe : oid ≠ id)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeObject at hStore; cases hStore
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable_getElem?_insert st.objects id obj hObjInv]
  have : ¬((id == oid) = true) := by intro heq; exact hNe (eq_of_beq heq).symm
  simp [this]

theorem storeObject_scheduler_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore; cases hStore; rfl

theorem tcb_lookup_of_endpoint_store
    (st st' : SystemState) (endpointId tid : SeLe4n.ObjId) (tcb : TCB) (ep' : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hObj : st'.objects[tid]? = some (.tcb tcb)) :
    st.objects[tid]? = some (.tcb tcb) := by
  by_cases hEq : tid = endpointId
  · rw [hEq, storeObject_objects_eq st st' endpointId (.endpoint ep') hObjInv hStore] at hObj; cases hObj
  · rw [storeObject_objects_ne st st' endpointId tid (.endpoint ep') hEq hObjInv hStore] at hObj; exact hObj

theorem runnable_membership_of_endpoint_store
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hRun : tid ∈ st'.scheduler.runnable) :
    tid ∈ st.scheduler.runnable := by
  simpa [storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore] using hRun

theorem not_runnable_membership_of_endpoint_store
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hNotRun : tid ∉ st.scheduler.runnable) :
    tid ∉ st'.scheduler.runnable := by
  simpa [storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore] using hNotRun

-- ============================================================================
-- Endpoint / notification well-formedness definitions
-- ============================================================================

def notificationQueueWellFormed (ntfn : Notification) : Prop :=
  match ntfn.state with
  | .idle => ntfn.waitingThreads.val = [] ∧ ntfn.pendingBadge = none
  | .waiting => ntfn.waitingThreads.val ≠ [] ∧ ntfn.pendingBadge = none
  | .active => ntfn.waitingThreads.val = [] ∧ ntfn.pendingBadge.isSome

def notificationInvariant (ntfn : Notification) : Prop :=
  notificationQueueWellFormed ntfn

-- ============================================================================
-- WS-H5: Intrusive dual-queue structural well-formedness predicates
-- C-04/A-22: Formal well-formedness for intrusive queue linkage.
-- A-23: Safe link dereference under well-formedness.
-- A-24: TCB existence guarantees after popHead.
-- ============================================================================

/-- WS-H5/C-04: Intrusive queue well-formedness predicate.
Encodes structural properties of a doubly-linked intrusive queue using local
boundary/link properties that are directly verifiable without traversal:

1. **Head/tail consistency**: head = none ↔ tail = none.
2. **Head boundary**: head TCB exists with queuePrev = none.
3. **Tail boundary**: tail TCB exists with queueNext = none.
4. **Doubly-linked forward integrity**: for any TCB with queueNext = some b,
   b exists and b.queuePrev = some a.
5. **Doubly-linked reverse integrity**: for any TCB with queuePrev = some a,
   a exists and a.queueNext = some b.

Properties 4-5 are global over all TCBs in the system state. This is deliberately
stronger than scoping to queue members: it ensures no TCB anywhere has a dangling
or inconsistent queue link, which simplifies preservation proofs (no need to
track queue membership through state transitions). -/
def intrusiveQueueWellFormed (q : IntrusiveQueue) (st : SystemState) : Prop :=
  -- P1: Empty queue consistency — head and tail agree on emptiness
  (q.head = none ↔ q.tail = none) ∧
  -- P2: Head boundary — head TCB exists with no predecessor
  (∀ hd, q.head = some hd →
    ∃ tcb, st.objects[hd.toObjId]? = some (.tcb tcb) ∧ tcb.queuePrev = none) ∧
  -- P3: Tail boundary — tail TCB exists with no successor
  (∀ tl, q.tail = some tl →
    ∃ tcb, st.objects[tl.toObjId]? = some (.tcb tcb) ∧ tcb.queueNext = none)

/-- WS-H5/C-04: System-wide doubly-linked integrity for TCB queue links.
If a TCB's queueNext points to b, then b exists and b.queuePrev points back.
If a TCB's queuePrev points to a, then a exists and a.queueNext points forward.
This global property closes A-23 (unvalidated link dereference). -/
def tcbQueueLinkIntegrity (st : SystemState) : Prop :=
  -- Forward integrity: a.queueNext = some b ⟹ b exists ∧ b.queuePrev = some a
  (∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
    st.objects[a.toObjId]? = some (.tcb tcbA) →
    ∀ (b : SeLe4n.ThreadId), tcbA.queueNext = some b →
      ∃ tcbB, st.objects[b.toObjId]? = some (.tcb tcbB) ∧ tcbB.queuePrev = some a) ∧
  -- Reverse integrity: b.queuePrev = some a ⟹ a exists ∧ a.queueNext = some b
  (∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
    st.objects[b.toObjId]? = some (.tcb tcbB) →
    ∀ (a : SeLe4n.ThreadId), tcbB.queuePrev = some a →
      ∃ tcbA, st.objects[a.toObjId]? = some (.tcb tcbA) ∧ tcbA.queueNext = some b)

/-- Transitive closure of the queueNext relation: a path a →⁺ b exists in the
system state when there is a chain of TCBs whose queueNext fields connect a to b. -/
inductive QueueNextPath (st : SystemState) : SeLe4n.ThreadId → SeLe4n.ThreadId → Prop
  | single (a b : SeLe4n.ThreadId) (tcb : TCB) :
      st.objects[a.toObjId]? = some (.tcb tcb) → tcb.queueNext = some b →
      QueueNextPath st a b
  | cons (a b c : SeLe4n.ThreadId) (tcb : TCB) :
      st.objects[a.toObjId]? = some (.tcb tcb) → tcb.queueNext = some b →
      QueueNextPath st b c → QueueNextPath st a c

/-- WS-H5 / AN5-B (SCH-M05): TCB queue chain acyclicity — no thread can
reach itself via `queueNext`. Prevents infinite loops during IPC queue
traversal (`intrusiveQueueWellFormed`, `collectQueueMembers`).

**Naming disambiguation (AN5-B / SCH-M05)**: this predicate is *not* the
priority-inheritance `blockingAcyclic` at
`Scheduler/PriorityInheritance/BlockingGraph.lean:127`. The two operate
on different edge relations:

* `tcbQueueChainAcyclic` (this file, IPC scope) — edge `a → b` iff
  `a.queueNext = some b`. Consumed by IPC dual-queue proofs.
* `blockingAcyclic` (PIP scope) — edge `tid → server` iff `tid` blocks on
  a reply to `server`. Consumed by PIP bounded-inversion + WCRT proofs.

A system can satisfy one without the other. The names are retained
because both are well-established across ~73 + ~76 proof sites; a
rename would cause a mechanical cascade disproportionate to the
clarity gain. -/
def tcbQueueChainAcyclic (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId), ¬ QueueNextPath st tid tid

/-- QueueNextPath composes: if a→⁺b and b→⁺c, then a→⁺c. -/
theorem QueueNextPath_trans {st : SystemState} {a b c : SeLe4n.ThreadId}
    (hab : QueueNextPath st a b) (hbc : QueueNextPath st b c) :
    QueueNextPath st a c := by
  induction hab with
  | single src dst tcb hObj hNext => exact .cons src dst c tcb hObj hNext hbc
  | cons src mid _ tcb hObj hNext _ ih => exact .cons src mid c tcb hObj hNext (ih hbc)

/-- V4-A: Every `QueueNextPath` starts with a queueNext edge from the source. -/
theorem QueueNextPath.firstEdge {st : SystemState} {a b : SeLe4n.ThreadId}
    (h : QueueNextPath st a b) :
    ∃ mid tcb, st.objects[a.toObjId]? = some (.tcb tcb) ∧ tcb.queueNext = some mid := by
  cases h with
  | single _ _ tcb hObj hNext => exact ⟨_, tcb, hObj, hNext⟩
  | cons _ _ _ tcb hObj hNext _ => exact ⟨_, tcb, hObj, hNext⟩

/-- V4-A: If no TCB has a non-none queueNext, then tcbQueueChainAcyclic holds. -/
theorem tcbQueueChainAcyclic_of_allNextNone {st : SystemState}
    (h : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.queueNext = none) :
    tcbQueueChainAcyclic st := by
  intro tid hPath
  obtain ⟨mid, tcb, hObj, hNext⟩ := hPath.firstEdge
  rw [h tid tcb hObj] at hNext; exact absurd hNext (by simp)

/-- Acyclicity implies no self-loop: a thread's queueNext cannot point to itself. -/
theorem tcbQueueChainAcyclic_no_self_loop {st : SystemState}
    (hAcyclic : tcbQueueChainAcyclic st)
    (a : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA)) :
    tcbA.queueNext ≠ some a := by
  intro h
  exact hAcyclic a (.single a a tcbA hA h)

/-- Acyclicity implies no 2-cycle: if a.next=some b, then b.next ≠ some a. -/
theorem tcbQueueChainAcyclic_no_two_cycle {st : SystemState}
    (hAcyclic : tcbQueueChainAcyclic st)
    (a b : SeLe4n.ThreadId) (tcbA tcbB : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA))
    (hB : st.objects[b.toObjId]? = some (.tcb tcbB))
    (hAB : tcbA.queueNext = some b) :
    tcbB.queueNext ≠ some a := by
  intro hBA
  exact hAcyclic a (.cons a b a tcbA hA hAB (.single b a tcbB hB hBA))

/-- WS-H5/C-04: Dual-queue endpoint well-formedness — both sendQ and receiveQ
are individually well-formed. Cross-queue contamination prevention is enforced
by the ipcState exclusivity that endpointQueueEnqueue checks (a thread must
have ipcState = .ready to be enqueued). -/
def dualQueueEndpointWellFormed (epId : SeLe4n.ObjId) (st : SystemState) : Prop :=
  match st.objects[epId]? with
  | some (.endpoint ep) =>
      intrusiveQueueWellFormed ep.sendQ st ∧
      intrusiveQueueWellFormed ep.receiveQ st
  | _ => True  -- Non-endpoint objects trivially satisfy

/-- WS-H5: System-level dual-queue invariant — all endpoints in the system
maintain dual-queue well-formedness AND system-wide TCB link integrity holds.
tcbQueueLinkIntegrity is a system-level property (not per-endpoint) that
ensures every TCB's queueNext/queuePrev links are consistent.
tcbQueueChainAcyclic ensures no thread can reach itself via queueNext,
preventing infinite loops during queue traversal. -/
def dualQueueSystemInvariant (st : SystemState) : Prop :=
  (∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[epId]? = some (.endpoint ep) →
    dualQueueEndpointWellFormed epId st) ∧
  tcbQueueLinkIntegrity st ∧
  tcbQueueChainAcyclic st

/-- WS-H12c: IPC invariant — all notifications satisfy notification queue
well-formedness. The former `endpointInvariant` conjunct (vacuous `True`
since WS-H12a) has been removed; meaningful dual-queue structural checking
lives in `dualQueueSystemInvariant`. -/
def ipcInvariant (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ntfn : Notification), st.objects[oid]? = some (KernelObject.notification ntfn) → notificationInvariant ntfn

/-- WS-H12d/A-09: All pending IPC messages stored in TCBs satisfy payload bounds.
This is a system-level invariant maintained by the bounds checks at every IPC
send boundary (`endpointSendDual`, `endpointCall`, `endpointReply`,
`endpointReplyRecv`).

**AN3-E.4 (IPC-M08) scope note.** This predicate quantifies over _every_
TCB in `st.objects`, so it bounds the payload of every pending message
regardless of whether the carrier thread is still live or whether the
corresponding endpoint remains mapped.  Liveness of the addressed
endpoint is _not_ a direct conjunct here: a TCB that is still blocked
on a since-revoked endpoint retains its pending message, and the bounds
check is about payload size, not about rendezvous reachability.
Endpoint liveness is a _transitive_ property that flows from
`ipcStateQueueMembershipConsistent` (which witnesses that a TCB whose
`ipcState` names an endpoint is enqueued on that endpoint) composed
with the V3-K/J queue membership invariants.  Strengthening this
predicate to cross-check endpoint existence would duplicate those
invariants and make the payload-bounds proof coupled to queue state,
which is not the contract the send-boundary bounds check establishes.
See `ipcStateQueueMembershipConsistent` below for the liveness side. -/
def allPendingMessagesBounded (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (msg : IpcMessage),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.pendingMessage = some msg →
    msg.bounded

/-- WS-RR RR3.11: **every in-flight message satisfies `P`** — the shape shared by
every property of messages parked in a TCB's `pendingMessage`.

`allPendingMessagesBounded` is the `P := IpcMessage.bounded` instance and
`pendingMessageCapBadgesWellFormed` below is the in-flight badge instance; the
transitions preserve the family once, parametrically, rather than once per
property.  The transport is genuinely generic: no step of an IPC transition reads
the *content* of a parked message, it only moves the message from one TCB to
another or leaves it alone, so the same fold discharges any `P`. -/
def pendingMessagesSatisfy (P : IpcMessage → Prop) (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (msg : IpcMessage),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.pendingMessage = some msg →
    P msg

/-- WS-RR RR3.11: `allPendingMessagesBounded` is the boundedness instance of the
generic in-flight family.  Definitional, so either form may be supplied where the
other is expected; stated so the relationship is a checked fact rather than a
convention. -/
theorem allPendingMessagesBounded_iff_pendingMessagesSatisfy (st : SystemState) :
    allPendingMessagesBounded st ↔ pendingMessagesSatisfy IpcMessage.bounded st := Iff.rfl

/-- WS-RR RR3.11: the in-flight family depends only on the object store. -/
theorem pendingMessagesSatisfy_of_getElem_eq {P : IpcMessage → Prop} {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : pendingMessagesSatisfy P s1) : pendingMessagesSatisfy P s2 := by
  intro tid tcb msg hTcb hMsg
  rw [hEq] at hTcb
  exact h tid tcb msg hTcb hMsg

-- ============================================================================
-- WS-F5/D1d: Badge well-formedness invariant
-- ============================================================================

/-- WS-F5/D1d: A single badge value is word-bounded (fits in `machineWordBits`). -/
@[inline] def badgeValid (badge : SeLe4n.Badge) : Prop := badge.valid

/-- WS-F5/D1d: All badges in notification objects are word-bounded.
Asserts that every notification's `pendingBadge` (when present) satisfies
`Badge.valid` (value < 2^machineWordBits). This ensures the model cannot
represent badge values that would be silently truncated on real hardware. -/
def notificationBadgesWellFormed (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ntfn : Notification) (badge : SeLe4n.Badge),
    st.objects[oid]? = some (.notification ntfn) →
    ntfn.pendingBadge = some badge →
    badge.valid

/-- WS-F5/D1d: All badges in capabilities are word-bounded.
Asserts that every capability's badge (when present) in every CNode
satisfies `Badge.valid`. -/
def capabilityBadgesWellFormed (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (badge : SeLe4n.Badge),
    st.objects[oid]? = some (.cnode cn) →
    cn.lookup slot = some cap →
    cap.badge = some badge →
    badge.valid

/-- WS-F5/D1d: System-wide badge well-formedness — all badges in notifications
and capabilities are word-bounded to `machineWordBits` (64 bits). -/
def badgeWellFormed (st : SystemState) : Prop :=
  notificationBadgesWellFormed st ∧ capabilityBadgesWellFormed st

/-- WS-RR RR3.11: every capability carried by a message has a word-bounded badge —
the in-flight counterpart of `capabilityBadgesWellFormed`, which says the same of
the badges at rest in a CNode. -/
def messageCapBadgesValid (m : IpcMessage) : Prop :=
  ∀ (i : Nat) (c : TransferCap) (badge : SeLe4n.Badge),
    m.caps[i]? = some c →
    c.cap.badge = some badge →
    badge.valid

/-- WS-RR RR3.11: badges on capabilities **in flight** — carried inside a TCB's
`pendingMessage` — are word-bounded, exactly as `capabilityBadgesWellFormed`
requires of the badges at rest in a CNode.

`badgeWellFormed` constrains badges *at rest*; the IPC capability transfer
installs an in-flight capability into the receiver's CNode verbatim
(`ipcTransferSingleCap` stores `tc.cap`, it does not re-resolve it), so without
this the transfer can turn an out-of-range in-flight badge into an out-of-range
badge at rest.  That is the hole the `*WithCaps` `ipcInvariantFull` bundles were
covering by threading `badgeWellFormed` on their post-state; stated here as a
pre-state property, it is dischargeable and the bundles establish the conjunct
instead. -/
def pendingMessageCapBadgesWellFormed (st : SystemState) : Prop :=
  pendingMessagesSatisfy messageCapBadgesValid st

/-- WS-RR RR3.11: the in-flight badge property depends only on the object store. -/
theorem pendingMessageCapBadgesWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : pendingMessageCapBadgesWellFormed s1) : pendingMessageCapBadgesWellFormed s2 :=
  pendingMessagesSatisfy_of_getElem_eq hEq h

/-- V3-G1 (M-PRF-5): **`pendingMessage` agrees with the blocking state, in both
    directions.**

    A thread parked to *collect* holds nothing; a thread parked to *deliver*
    holds what it is delivering:

    - `blockedOnReceive` (waiting for a send) — `pendingMessage = none`
    - `blockedOnNotification` (waiting for a signal) — `pendingMessage = none`
    - `blockedOnSend` (queued to deliver) — `pendingMessage.isSome`
    - `blockedOnCall` (queued to deliver, awaiting a reply) — `pendingMessage.isSome`

    The receiver direction is the older half: no message has been delivered
    yet, so a wake path may overwrite `pendingMessage` without losing data.

    The sender direction was added at PR #873 round 11, and the reason is worth
    stating because its absence was load-bearing.  This docstring used to read
    "`blockedOnSend` and `blockedOnCall` threads MAY have a pending message",
    which made "a parked sender is carrying its message" a *convention*: true of
    every state the live park sites produce (`endpointSendDual` /
    `endpointCall` both store `some msg` atomically with the block), but not
    something any consumer could rely on.  So every consumer that read a parked
    sender had to re-derive it defensively, and each one that did not was a
    defect — `frozenQueuePopHead` handing a receiver `none` while the provenance
    join claimed a delivery (round 7), then `endpointReceiveDual` doing the same
    on the live path (round 11).  Stating it here makes the malformed state
    unreachable rather than merely refused, so a consumer that forgets to check
    is no longer wrong.

    `blockedOnReply` threads do hold `pendingMessage = none` in practice (the
    receive path clears it) but are deliberately not constrained: nothing reads
    a reply-blocked thread's message, so pinning it would add a preservation
    obligation with no consumer. -/
def blockedThreadsPendingMessageConsistent (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    match tcb.ipcState with
    | .blockedOnReceive _ => tcb.pendingMessage = none
    | .blockedOnNotification _ => tcb.pendingMessage = none
    | .blockedOnSend _ => tcb.pendingMessage.isSome
    | .blockedOnCall _ => tcb.pendingMessage.isSome
    | _ => True

/-- Full IPC invariant including system-level dual-queue structural
well-formedness, TCB link integrity, message payload bounds, and badge
well-formedness.
WS-H12c: Dual-queue well-formedness is enforced at the system level via
`dualQueueSystemInvariant` (per-endpoint `dualQueueEndpointWellFormed` +
system-wide `tcbQueueLinkIntegrity`).
WS-H12d: `allPendingMessagesBounded` ensures every pending message stored in
a TCB satisfies `maxMessageRegisters`/`maxExtraCaps` bounds.
WS-F5/D1d: `badgeWellFormed` ensures all badges in notifications and
capabilities are word-bounded.
V3-G6: `blockedThreadsPendingMessageConsistent` ties `pendingMessage` to the
blocking state in both directions -- a thread parked to collect holds nothing, a
thread parked to deliver holds what it is delivering.
V3-K: `endpointQueueNoDup` ensures no self-loops and send/receive queue head
disjointness.
V3-J: `ipcStateQueueMembershipConsistent` ensures every blocked thread is
reachable from its endpoint's queue head.

Note: The actual definition of `ipcInvariantFull` is placed after the
V3-K and V3-J predicate definitions to ensure forward reference resolution. -/
-- Forward reference: see `ipcInvariantFull` below (after V3-K/V3-J definitions)

-- ============================================================================
-- Scheduler-IPC coherence contract predicates (M3.5)
-- ============================================================================

def runnableThreadIpcReady (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb,
    st.objects[tid.toObjId]? = some (.tcb tcb) → tid ∈ st.scheduler.runnable → tcb.ipcState = .ready

def blockedOnSendNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnSend endpointId →
    tid ∉ st.scheduler.runnable

def blockedOnReceiveNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnReceive endpointId →
    tid ∉ st.scheduler.runnable

/-- WS-H1/C-01: A Call sender blocked on the send queue is not runnable. -/
def blockedOnCallNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnCall endpointId →
    tid ∉ st.scheduler.runnable

/-- WS-H1/C-01: A thread blocked awaiting a reply is not runnable. -/
def blockedOnReplyNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId replyTarget,
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnReply endpointId replyTarget →
    tid ∉ st.scheduler.runnable

/-- WS-F6/D2: A thread blocked on notification wait is not runnable.
Closes the HIGH-03 gap: threads in ipcState = `.blockedOnNotification oid` must
not appear in the runnable queue. Without this, a notification-blocked thread could
be scheduled despite being logically blocked, violating temporal isolation. -/
def blockedOnNotificationNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb notificationId,
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnNotification notificationId →
    tid ∉ st.scheduler.runnable

/-- WS-F6/D2: Extended from 5-tuple to 6-tuple with `blockedOnNotificationNotRunnable`.
All IPC blocking states now have non-runnability contracts. -/
def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧ blockedOnSendNotRunnable st ∧ blockedOnReceiveNotRunnable st ∧
  blockedOnCallNotRunnable st ∧ blockedOnReplyNotRunnable st ∧
  blockedOnNotificationNotRunnable st

/-- Under dequeue-on-dispatch QCC, the current thread (if any) has ipcState = .ready.
This is needed because ensureRunnable adds the woken target to the run queue, and
QCC requires the current thread to NOT be in the run queue. We must therefore show
current ≠ target, which follows from their differing ipcState. -/
def currentThreadIpcReady (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid => ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .ready

/-- Under dequeue-on-dispatch QCC, the current thread must not appear as the
head of any endpoint queue (send or receive). This ensures that when
endpointQueuePopHead pops a thread, it differs from the current thread. -/
def currentNotEndpointQueueHead (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid =>
    ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[oid]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid

/-- Under dequeue-on-dispatch QCC, the current thread must not appear on any
notification wait list. This ensures ensureRunnable on a signaled waiter
does not conflict with the current thread. -/
def currentNotOnNotificationWaitList (st : SystemState) : Prop :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | none => True
  | some tid =>
    ∀ (oid : SeLe4n.ObjId) (ntfn : Notification),
      st.objects[oid]? = some (.notification ntfn) →
      tid ∉ ntfn.waitingThreads

/-- Combined dequeue-on-dispatch coherence predicate: the current thread
has ready ipcState, is not an endpoint queue head, and is not on any
notification wait list. -/
def currentThreadDequeueCoherent (st : SystemState) : Prop :=
  currentThreadIpcReady st ∧ currentNotEndpointQueueHead st ∧ currentNotOnNotificationWaitList st

/-- Helper: endpointQueuePopHead returns the head of the relevant queue. -/
theorem endpointQueuePopHead_returns_head
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st : SystemState)
    (ep : Endpoint) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st')) :
    (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some tid := by
  unfold endpointQueuePopHead SystemState.getObject? at hPop
  rw [hObj] at hPop; simp only at hPop
  cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => simp [hHead] at hPop
  | some headTid =>
    simp only [hHead] at hPop
    cases hLk : lookupTcb st headTid with
    | none => simp [hLk] at hPop
    | some headTcb =>
      simp only [hLk] at hPop
      -- PR #873 round 11: the send-queue message-presence guard --
      -- a head that fails it errors, so it is not this `.ok`.
      split at hPop
      · simp at hPop
      revert hPop
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases headTcb.queueNext with
        | none =>
          simp only []
          cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
          | error e => simp
          | ok st3 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            rintro ⟨rfl, _, _⟩; rfl
        | some nextTid =>
          simp only []
          cases hLkNext : lookupTcb pair.2 nextTid with
          | none => simp
          | some nextTcb =>
            simp only []
            cases hLink : storeTcbQueueLinks pair.2 nextTid _ _ _ with
            | error e => simp
            | ok st2 =>
              simp only []
              cases hFinal : storeTcbQueueLinks st2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                rintro ⟨rfl, _, _⟩; rfl

/-- Helper: endpointQueuePopHead returns the pre-state TCB for the dequeued thread.
The returned TCB matches the one at tid.toObjId in the pre-state st. -/
theorem endpointQueuePopHead_returns_pre_tcb
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st : SystemState)
    (ep : Endpoint) (tid : SeLe4n.ThreadId) (headTcb : TCB) (st' : SystemState)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    st.objects[tid.toObjId]? = some (.tcb headTcb) := by
  unfold endpointQueuePopHead SystemState.getObject? at hPop
  rw [hObj] at hPop; simp only at hPop
  cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => simp [hHead] at hPop
  | some headTid =>
    simp only [hHead] at hPop
    cases hLk : lookupTcb st headTid with
    | none => simp [hLk] at hPop
    | some tcb =>
      simp only [hLk] at hPop
      -- PR #873 round 11: the send-queue message-presence guard --
      -- a head that fails it errors, so it is not this `.ok`.
      split at hPop
      · simp at hPop
      revert hPop
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases tcb.queueNext with
        | none =>
          simp only []
          cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
          | error e => simp
          | ok st3 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            rintro ⟨rfl, rfl, _⟩
            exact lookupTcb_some_objects st headTid tcb hLk
        | some nextTid =>
          simp only []
          cases hLkNext : lookupTcb pair.2 nextTid with
          | none => simp
          | some nextTcb =>
            simp only []
            cases hLink : storeTcbQueueLinks pair.2 nextTid _ _ _ with
            | error e => simp
            | ok st2 =>
              simp only []
              cases hFinal : storeTcbQueueLinks st2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                rintro ⟨rfl, rfl, _⟩
                exact lookupTcb_some_objects st headTid tcb hLk

/-- WS-SM SM6 (PR #873 round 11): **a dequeued sender is carrying its message.**

The converse of the guard in `endpointQueuePopHead`, and the fact the receive
path needs: a send-queue dequeue that succeeds hands its caller a `TCB` whose
`pendingMessage` is present, so the delivery it feeds moves real content and the
provenance edge `receiverTaintEdges` declares has content to join.

This is the *unconditional* form: it holds of every state, invariant or not,
because the dequeue refuses the malformed head rather than relying on the
invariant to exclude it.  For states that do satisfy `ipcInvariantFull` the fact
is available a second way -- `blockedThreadsPendingMessageConsistent` requires
`.blockedOnSend` / `.blockedOnCall` to carry a message -- and that is the
carrier the receive paths should be read against; this theorem is what lets a
consumer below the invariant (a thawed snapshot, a below-API construction) reach
the same conclusion.  Stated on the returned TCB rather than the queue head
because that is the value both receives read the message out of. -/
theorem endpointQueuePopHead_send_sender_carries_message
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st : SystemState)
    (ep : Endpoint) (tid : SeLe4n.ThreadId) (headTcb : TCB) (st' : SystemState)
    (hSend : isReceiveQ = false)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    headTcb.pendingMessage.isSome := by
  have hMsg : ∀ t : TCB,
      ¬((!isReceiveQ && t.pendingMessage.isNone) = true) → t.pendingMessage.isSome := by
    intro t h
    cases hp : t.pendingMessage with
    | none => rw [hSend, hp] at h; simp at h
    | some m => simp
  unfold endpointQueuePopHead SystemState.getObject? at hPop
  rw [hObj] at hPop; simp only at hPop
  cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => simp [hHead] at hPop
  | some headTid =>
    simp only [hHead] at hPop
    cases hLk : lookupTcb st headTid with
    | none => simp [hLk] at hPop
    | some tcb =>
      simp only [hLk] at hPop
      split at hPop
      · simp at hPop
      · rename_i hGuard
        revert hPop
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases tcb.queueNext with
          | none =>
            simp only []
            cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
            | error e => simp
            | ok st3 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              rintro ⟨_, rfl, _⟩
              exact hMsg tcb hGuard
          | some nextTid =>
            simp only []
            cases hLkNext : lookupTcb pair.2 nextTid with
            | none => simp
            | some nextTcb =>
              simp only []
              cases hLink : storeTcbQueueLinks pair.2 nextTid _ _ _ with
              | error e => simp
              | ok st2 =>
                simp only []
                cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                | error e => simp
                | ok st3 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  rintro ⟨_, rfl, _⟩
                  exact hMsg tcb hGuard

-- ============================================================================
-- Scheduler invariant bundle preservation
-- WS-E3/H-09: Multi-step tracking through storeObject → storeTcbIpcState → removeRunnable/ensureRunnable.
-- ============================================================================

/-- Helper: after storeObject + storeTcbIpcState, the scheduler is unchanged from pre-state. -/
theorem scheduler_unchanged_through_store_tcb
    (st st1 st2 : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStore : storeObject oid obj st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    st2.scheduler = st.scheduler := by
  rw [storeTcbIpcState_scheduler_eq st1 st2 tid ipc hTcb,
      storeObject_scheduler_eq st st1 oid obj hStore]

/-- WS-F1: After storeObject + storeTcbIpcStateAndMessage, the scheduler is
unchanged.  Mirrors `scheduler_unchanged_through_store_tcb` for the store that
also writes `pendingMessage`. -/
theorem scheduler_unchanged_through_store_tcb_msg
    (st st1 st2 : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStore : storeObject oid obj st = .ok ((), st1))
    (hTcb : storeTcbIpcStateAndMessage st1 tid ipc msg = .ok st2) :
    st2.scheduler = st.scheduler := by
  rw [storeTcbIpcStateAndMessage_scheduler_eq st1 st2 tid ipc msg hTcb,
      storeObject_scheduler_eq st st1 oid obj hStore]

/-- Helper: TCB at tid.toObjId is preserved through storeObject (endpoint) if tid's TCB exists. -/
private theorem tcb_preserved_through_endpoint_store
    (st st1 : SystemState) (endpointId : SeLe4n.ObjId) (obj : KernelObject) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcbExists : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hEndpoint : ∃ ep, st.objects[endpointId]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId obj st = .ok ((), st1)) :
    st1.objects[tid.toObjId]? = some (.tcb tcb) := by
  have hNe : tid.toObjId ≠ endpointId := by
    rcases hEndpoint with ⟨ep, hObj⟩; intro h; rw [h] at hTcbExists; simp_all
  rwa [storeObject_objects_ne st st1 endpointId tid.toObjId obj hNe hObjInv hStore]

-- ============================================================================
-- WS-G7/F-P11: Notification waiter consistency invariant
-- ============================================================================

/-- WS-G7: If a thread is in a notification's waiting list, its TCB ipcState
must be `.blockedOnNotification oid` for that notification. This invariant
enables the O(1) TCB ipcState duplicate-check in `notificationWait`. -/
def notificationWaiterConsistent (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ntfn : Notification) (tid : SeLe4n.ThreadId),
    st.objects[oid]? = some (.notification ntfn) →
    tid ∈ ntfn.waitingThreads →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = .blockedOnNotification oid

/-- WS-G7: Bridge lemma: under `notificationWaiterConsistent`, if a thread's
ipcState is NOT `.blockedOnNotification oid`, then it is NOT in that
notification's waiting list. -/
theorem not_mem_waitingThreads_of_ipcState_ne
    (st : SystemState) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hConsist : notificationWaiterConsistent st)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hNe : tcb.ipcState ≠ .blockedOnNotification oid) :
    tid ∉ ntfn.waitingThreads := by
  intro hMem
  obtain ⟨tcb', hTcb', hIpc'⟩ := hConsist oid ntfn tid hNtfn hMem
  rw [hTcb] at hTcb'; cases hTcb'
  exact hNe hIpc'

-- ============================================================================
-- Notification uniqueness (F-12 / WS-D4 / WS-G7)
-- ============================================================================

-- WS-RC R4.C close-out (Phase C2.c4): the historical state-level
-- `uniqueWaiters` predicate, its `uniqueWaiters_holds` substantive
-- discharge, and its `uniqueWaiters_trivial` plan-named alias have all
-- been deleted.  Per-Notification Nodup is now carried structurally by
-- `Notification.waitingThreads : NoDupList ThreadId` via the
-- `NoDupList.hNodup` field; the canonical discharge is
-- `SeLe4n.NoDupList.nodup_witness` (or its plan-named alias
-- `SeLe4n.Kernel.notification_waiters_nodup`).

/-- AJ1-B (M-04): Every thread in `blockedOnReply` state has an explicit
`replyTarget`. All production paths (`endpointCall`, `endpointReceiveDual`)
create `blockedOnReply` with `some receiver`, making the `none` authorization
branch in `endpointReply` unreachable under this invariant. -/
def blockedOnReplyHasTarget (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (endpointId : SeLe4n.ObjId)
    (replyTarget : Option SeLe4n.ThreadId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.ipcState = .blockedOnReply endpointId replyTarget →
    replyTarget.isSome

/-- WS-SM SM6.D (PR #822 review): **bidirectional** consistency between a TCB's
`replyObject` forward link and the Reply object's `caller` back-link.  The public
`.reply` path resolves authority through `reply.caller`, and `consumeCallerReply`
clears `tcb.replyObject`, so the two must stay reciprocal — without this conjunct
`ipcInvariantFull` would admit a state where a TCB points at an absent/different
Reply, or a `reply.caller` is not reciprocated, letting a stale reply cap act on
or erase the wrong outstanding reply link.  Two directions:

* **forward** (`tcb.replyObject = some rid` ⇒ the Reply exists and names this TCB);
* **backward** (`reply.caller = some tid` ⇒ that TCB exists, points back, **and is
  `blockedOnReply`** — the only state from which the public `.reply` path can
  consume it; without this the invariant would admit a Reply linked to a `.ready`
  caller that `.reply` then rejects, leaving the Reply in-use and unconsumable).

Established by `linkCallerReply` (sets both fields reciprocally on a `blockedOnReply`
caller, fail-closed on an in-use reply) and preserved by `consumeCallerReply`
(clears both reciprocally); all other IPC transitions frame it (they touch neither
field nor a linked caller's IPC state). -/
def replyCallerLinkageReciprocal (st : SystemState) : Prop :=
  (∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.replyObject = some rid →
      ∃ r, st.objects[rid.toObjId]? = some (.reply r) ∧ r.caller = some tid) ∧
  (∀ (rid : SeLe4n.ReplyId) (r : Reply) (tid : SeLe4n.ThreadId),
      st.objects[rid.toObjId]? = some (.reply r) →
      r.caller = some tid →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb.replyObject = some rid ∧
        ∃ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
          tcb.ipcState = .blockedOnReply ep rt)

/-- WS-SM SM6.D (#7.4 / IPC de-threading D2): the **third clause** of
`replyCallerLinkage`, as a first-class predicate — every `.blockedOnReply` caller
already carries a `replyObject`.  Named separately so the bundle's per-transition
preservation can *concretely establish* it (rather than threading it), via a reusable
frame family (`blockedOnReplyHasReplyObject_*`), and so consumers get a named
projection.  The #7 D6 fold links the caller's reply atomically with the blocking
store, so this holds at the transition boundary. -/
def blockedOnReplyHasReplyObject (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnReply ep rt →
      ∃ rid, tcb.replyObject = some rid

/-- WS-SM SM6.D (#7.4): `replyCallerLinkage` = the bidirectional reciprocity
(`replyCallerLinkageReciprocal`) **plus** the forward guarantee that every
`.blockedOnReply` caller already carries a `replyObject` (`blockedOnReplyHasReplyObject`).
The #7 D6 fold links the caller's reply object **atomically** with the blocking store
(inside `endpointCall` / `endpointCallOnCore` / `endpointReceiveDual{,OnCore}`), so
`blockedOnReply ⇒ replyObject` now holds at the **transition boundary**, not merely at
syscall boundaries — closing the false-assurance gap where `ipcInvariantFull` (whose
16th conjunct this is) admitted a `.blockedOnReply` caller with no Reply object to answer
it (a thread blocked forever, since the public `.reply` path resolves authority through
`reply.caller`).  The reciprocal clauses are factored out because they are the strongest
invariant that survives the fold's intermediate state (post-blocking-store, pre-link):
there the caller is `.blockedOnReply` yet not-yet-linked, so the third clause is
momentarily false while reciprocity holds. -/
def replyCallerLinkage (st : SystemState) : Prop :=
  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st

/-- WS-SM SM6.D (PR #822 review): `replyCallerLinkage` reads only `st.objects`, so
any transition that leaves the object store unchanged frames it.  Used by the
non-IPC transitions (timer tick, register/context writes) and the default state. -/
theorem replyCallerLinkage_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : replyCallerLinkage st) :
    replyCallerLinkage st' := by
  unfold replyCallerLinkage replyCallerLinkageReciprocal blockedOnReplyHasReplyObject at h ⊢
  rw [hObjs]; exact h

/-- WS-SM SM6.D (#7.4 / IPC de-threading D2, **consumer**): the safety property the
strengthened `replyCallerLinkage` *delivers* — **every `.blockedOnReply` caller is
answerable**.  Combining the third clause (`blockedOnReply ⇒ replyObject`) with the
forward reciprocal clause (`replyObject ⇒ the Reply exists and names this TCB back`)
shows that a blocked caller always has a concrete backing Reply object that names it,
so the public `.reply` path (which resolves authority through `reply.caller`) can always
answer it.  This is the formal statement of "no thread blocks forever on an unanswerable
reply" — the false-assurance gap #7.4 closed, now cashed in as a usable lemma rather than
a write-only invariant. -/
theorem blockedOnReply_caller_is_answerable (st : SystemState)
    (h : replyCallerLinkage st)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hBlk : tcb.ipcState = .blockedOnReply ep rt) :
    ∃ (rid : SeLe4n.ReplyId) (r : Reply),
      tcb.replyObject = some rid ∧
      st.objects[rid.toObjId]? = some (.reply r) ∧ r.caller = some tid := by
  obtain ⟨rid, hRep⟩ := h.2 tid tcb ep rt hTcb hBlk
  obtain ⟨r, hr, hrc⟩ := h.1.1 tid tcb rid hTcb hRep
  exact ⟨rid, r, hRep, hr, hrc⟩

/-- WS-RR RR7.22 (residual), the **contrapositive** consumer of the same
reciprocity: a thread that is *not* `.blockedOnReply` holds no Reply object.

Clause 1 of the reciprocal turns a held `replyObject` into a Reply naming this
thread back, and clause 2 turns that Reply into the thread being
`.blockedOnReply` — so holding one and not being blocked on it is contradictory.
This is what lets a transition that moves a thread out of a blocking state
(cancellation, timeout) discharge the "holds no reply" side conditions of the
reply-linkage and donation-owner frames from the bundle it already has, rather
than carrying them as extra hypotheses. -/
theorem replyObject_none_of_not_blockedOnReply (st : SystemState)
    (h : replyCallerLinkage st) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hNot : ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt) :
    tcb.replyObject = none := by
  cases hRO : tcb.replyObject with
  | none => rfl
  | some rid =>
    exfalso
    obtain ⟨r, hr, hrc⟩ := h.1.1 tid tcb rid hTcb hRO
    obtain ⟨tcb', hTcb', _, ep, rt, hBlk⟩ := h.1.2 rid r tid hr hrc
    rw [hTcb] at hTcb'
    have hx : tcb' = tcb := (KernelObject.tcb.inj (Option.some.inj hTcb')).symm
    rw [hx] at hBlk
    exact hNot ep rt hBlk

/-- WS-SM SM6.D (PR #822 review 6J9Kjg/6J9Kp6): a server-first receive **stash**
(`TCB.pendingReceiveReply`) is well-formed — it occurs only on a TCB that is still
`.blockedOnReceive` (the only state in which the server is awaiting its next `Call`
to link the Reply), and it names an **existing free** Reply object (`reply.caller =
none`).  Without this conjunct `ipcInvariantFull` admits a blocked receiver stashing
an absent or already-linked Reply, which a later server-first `Call` (the folded
`linkServerStashedReply`) then rejects with `.replyCapInvalid` while the receive stays pending.  Operationally
already maintained: `resolveRecvReplyId` only stashes a free, present `rid`, and
exit from `.blockedOnReceive` clears the stash (v0.31.111 / `replyIsStashed`); this
conjunct *states* it.  The second clause states the stash is **injective** (no two
blocked receivers stash the same Reply id) — see its inline note. -/
def pendingReceiveReplyWellFormed (st : SystemState) : Prop :=
  (∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.getTcb? tid = some tcb →
    tcb.pendingReceiveReply = some rid →
    (∃ ep, tcb.ipcState = .blockedOnReceive ep) ∧
    (∃ r, st.getReply? rid = some r ∧ r.caller = none)) ∧
  -- WS-SM SM6.D (PR #822 review): the stash is **injective** — at most one blocked
  -- receiver stashes any given Reply id.  Without this a model state could have two
  -- blocked servers stashing the same `rid`; a server-first `Call` linking one
  -- (the folded `linkServerStashedReply` → `linkCallerReply`, which consumes `reply.caller`) would
  -- silently invalidate the other's stash, so its later `Call` fails closed
  -- `.replyCapInvalid` while its receive completes.  Operationally maintained by
  -- `resolveRecvReplyId` (it stashes only an un-stashed `rid`, `!replyIsStashed`).
  (∀ (tid₁ tid₂ : SeLe4n.ThreadId) (tcb₁ tcb₂ : TCB) (rid : SeLe4n.ReplyId),
    st.getTcb? tid₁ = some tcb₁ → st.getTcb? tid₂ = some tcb₂ →
    tcb₁.pendingReceiveReply = some rid → tcb₂.pendingReceiveReply = some rid →
    tid₁ = tid₂)

/-- WS-SM SM6.D (PR #822 review): `pendingReceiveReplyWellFormed` reads only the
object store (through the typed `getTcb?` / `getReply?` accessors), so any transition
that leaves the object store unchanged frames it (timer tick, register/context
writes, the default state). -/
theorem pendingReceiveReplyWellFormed_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed st' := by
  unfold pendingReceiveReplyWellFormed SystemState.getTcb? SystemState.getReply? at h ⊢
  rw [hObjs]; exact h

/-- WS-SM SM6.E: `ipcInvariant` reads only the object store, so any
transition that leaves the object store unchanged frames it (the cross-core
deschedule, the replenishment migration, per-core scheduler-queue edits). -/
theorem ipcInvariant_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : ipcInvariant st) :
    ipcInvariant st' := by
  intro oid ntfn hL
  exact h oid ntfn (hObjs ▸ hL)

-- ============================================================================
-- WS-SM SM6.D (#7.1 fold): upstream reply-link / server-first-stash frames.
--
-- The #7 receive fold folds reply-linking into `endpointReceiveDual`: the Call
-- branch threads `SystemState.linkCallerReply` (a `.reply` write then a `.tcb`
-- `replyObject` write) and the no-sender branch writes the server-first stash
-- (a `.tcb` `pendingReceiveReply` write).  None of those fields is read by any
-- *structural* conjunct, so each new store frames every structural conjunct.
-- These bare frames live here (upstream of every per-conjunct preservation file)
-- so each consumer re-points its `endpointReceiveDual` proof to a named frame
-- rather than re-deriving the store semantics inline.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): storing any object that is **not** a `.notification`
preserves `ipcInvariant` (notification well-formedness reads only `.notification`
objects, and the stored slot post-store holds a non-notification).  The fold's
`linkCallerReply` (`.reply` then `.tcb`) and server-first stash (`.tcb`) are all
non-notification stores. -/
theorem storeObject_preserves_ipcInvariant_of_ne_notification
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNotNtfn : ∀ n, obj ≠ .notification n)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    ipcInvariant st' := by
  intro oid ntfn hObj
  by_cases hNe : oid = id
  · rw [hNe, storeObject_objects_eq st st' id obj hObjInv hStore] at hObj
    exact absurd (Option.some.inj hObj) (hNotNtfn ntfn)
  · exact hInv oid ntfn (by rwa [storeObject_objects_ne st st' id oid obj hNe hObjInv hStore] at hObj)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` preserves `objects.invExt` — its two
stores (`linkReply` at `rid.toObjId`, the caller-TCB `replyObject` write) each
preserve the object-store extensional invariant. -/
theorem linkCallerReply_preserves_objects_invExt (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hObjInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · exact storeObject_preserves_objects_invExt st1 st' caller.toObjId _ hObjInv1 hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` preserves the notification
well-formedness conjunct `ipcInvariant` — both its `.reply` and `.tcb` stores are
non-notification (cf. `storeObject_preserves_ipcInvariant_of_ne_notification`). -/
theorem linkCallerReply_preserves_ipcInvariant
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hObjInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    have hInv1 : ipcInvariant st1 := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_preserves_ipcInvariant_of_ne_notification st st1 rid.toObjId
            (.reply { r with caller := some caller }) (fun _ => by exact KernelObject.noConfusion)
            hInv hObjInv hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · exact storeObject_preserves_ipcInvariant_of_ne_notification st1 st' caller.toObjId
          (.tcb { tcb with replyObject := some rid }) (fun _ => by exact KernelObject.noConfusion)
          hInv1 hObjInv1 hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` leaves the scheduler unchanged (both
its stores are `storeObject`, which does not touch the scheduler). -/
theorem linkCallerReply_scheduler_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hSched1 : st1.scheduler = st.scheduler := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_scheduler_eq st st1 rid.toObjId _ hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · exact (storeObject_scheduler_eq st1 st' caller.toObjId _ hStep).trans hSched1
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` leaves the machine unchanged (both
its stores are `storeObject`, which does not touch the machine registers). -/
theorem linkCallerReply_machine_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hMach1 : st1.machine = st.machine := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_machine_eq st st1 rid.toObjId _ hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · exact (storeObject_machine_eq st1 st' caller.toObjId _ hStep).trans hMach1
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` preserves `objects.invExt` —
it composes `linkCallerReply` (which preserves it) with a single `pendingReceiveReply`
TCB store (which preserves it). -/
theorem linkServerStashedReply_preserves_objects_invExt (st st' : SystemState)
    (caller server : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hStep : linkServerStashedReply caller server st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hObjInv1
      | some sTcb =>
        simp only [hT] at hStep
        exact storeObject_preserves_objects_invExt st1 st' server.toObjId _ hObjInv1 hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` preserves `ipcInvariant` — both
its sub-stores are non-notification (the `linkCallerReply` reply/TCB stores and the
`pendingReceiveReply` TCB store). -/
theorem linkServerStashedReply_preserves_ipcInvariant
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : linkServerStashedReply caller server st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hInv1 := linkCallerReply_preserves_ipcInvariant st st1 caller rid hInv hObjInv hLink
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hInv1
      | some sTcb =>
        simp only [hT] at hStep
        exact storeObject_preserves_ipcInvariant_of_ne_notification st1 st' server.toObjId
          (.tcb { sTcb with pendingReceiveReply := none }) (fun _ => by exact KernelObject.noConfusion)
          hInv1 hObjInv1 hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` leaves the scheduler unchanged
(every sub-store is `storeObject`, which does not touch the scheduler). -/
theorem linkServerStashedReply_scheduler_eq (st st' : SystemState)
    (caller server : SeLe4n.ThreadId)
    (hStep : linkServerStashedReply caller server st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hSched1 := linkCallerReply_scheduler_eq st st1 caller rid hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hSched1
      | some sTcb =>
        simp only [hT] at hStep
        exact (storeObject_scheduler_eq st1 st' server.toObjId _ hStep).trans hSched1

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` leaves the machine unchanged
(every sub-store is `storeObject`, which does not touch the machine registers). -/
theorem linkServerStashedReply_machine_eq (st st' : SystemState)
    (caller server : SeLe4n.ThreadId)
    (hStep : linkServerStashedReply caller server st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hMach1 := linkCallerReply_machine_eq st st1 caller rid hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hMach1
      | some sTcb =>
        simp only [hT] at hStep
        exact (storeObject_machine_eq st1 st' server.toObjId _ hStep).trans hMach1

/-- AK1-B (I-H02): Soundness bridge for the fail-closed reply guard.
Under `blockedOnReplyHasTarget`, any `.blockedOnReply` state always has an
explicit target. This theorem is the formal discharge of the claim that the
new `none => .error .replyCapInvalid` arm in `endpointReply`/`endpointReplyRecv`
does not change behavior on invariant-satisfying states — the `none` arm is
unreachable. -/
theorem blockedOnReplyHasTarget_implies_some_replyTarget
    (st : SystemState)
    (hInv : blockedOnReplyHasTarget st)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (endpointId : SeLe4n.ObjId) (replyTarget : Option SeLe4n.ThreadId)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hIpc : tcb.ipcState = .blockedOnReply endpointId replyTarget) :
    ∃ t, replyTarget = some t := by
  have h := hInv tid tcb endpointId replyTarget hTcb hIpc
  cases replyTarget with
  | none => simp at h
  | some t => exact ⟨t, rfl⟩

-- WS-RC R4.C close-out: `notificationWait_preserves_uniqueWaiters` was
-- deleted along with the `uniqueWaiters` predicate it preserved.  The
-- per-notification Nodup invariant now holds structurally via
-- `Notification.waitingThreads.hNodup`; the state-level predicate has
-- no remaining role in the proof surface.

-- ============================================================================
-- WS-G7: notificationWaiterConsistent — base case + documentation
-- ============================================================================

/-- WS-G7: The default (empty) state trivially satisfies `notificationWaiterConsistent`
because the object store is empty, so no notification objects exist. -/
theorem default_notificationWaiterConsistent :
    notificationWaiterConsistent (default : SystemState) := by
  intro oid ntfn _ hObj _
  have h : (default : SystemState).objects[oid]? = none := by
    simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
  rw [h] at hObj; exact absurd hObj (by simp)

/-! ### WS-G7: Preservation path for `notificationWaiterConsistent`

`notificationWaiterConsistent` is a bridging invariant that enables the O(1)
duplicate-wait check in `notificationWait`. Its preservation through the kernel
transition surface is sketched here for documentation:

1. **`notificationWait`** (wait path): Prepends `waiter` to the notification's
   waiting list and sets `waiter.ipcState = .blockedOnNotification oid`.
   Pre-condition: `runnableThreadIpcReady` ensures the calling thread has
   `ipcState = .ready`, so it is not in any notification's waiting list.
   Preservation holds because the new waiter gets the correct ipcState and
   existing TCBs are unchanged.

2. **`notificationWait`** (badge path): Empties the target notification's
   waiting list. Preservation holds vacuously for the target; other
   notifications are unchanged.

3. **`notificationSignal`** (wake path): Removes the head waiter and sets its
   ipcState to `.ready`. The woken thread does not appear elsewhere in the
   remaining list — guaranteed structurally by `NoDupList.hNodup` on
   `Notification.waitingThreads` (WS-RC R4.C close-out; the historical
   state-level `uniqueWaiters` precondition is no longer required since the
   field-level invariant is unconditional). Remaining threads' TCBs are
   unchanged, so their ipcState is preserved.

4. **`notificationSignal`** (merge path): No TCB modification; only the
   notification badge is updated. All waiting lists are unchanged.

5. **Other kernel operations** (endpoint, scheduler, lifecycle, capability):
   These do not modify notification waiting lists. They may change a thread's
   ipcState, but only for threads that are `.ready` or blocked on
   non-notification objects, so `notificationWaiterConsistent` is preserved.

R3-C/M-19: Formal preservation theorems are proved in
`NotificationPreservation.lean` and `Structural.lean`:
- `storeObject_notification_preserves_notificationWaiterConsistent` — notification
  store with subset waiting list
- `storeObject_nonNotification_preserves_notificationWaiterConsistent` — non-notification
  store with ipcState consistency hypothesis
- `storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent` — TCB ipc
  state change when target thread is not in any notification wait list
- `notificationSignal_preserves_notificationWaiterConsistent` — R3-C.1: wake path
  (removes head waiter; structural `NoDupList.hNodup` ensures the woken
  thread does not appear elsewhere) + merge path (vacuous)
- `frame_preserves_notificationWaiterConsistent` — R3-C.2: general frame lemma
  for operations that preserve notification objects and waiter TCBs
- `endpointReply_preserves_notificationWaiterConsistent` — R3-C.2: concrete
  endpoint reply preservation (target is `.blockedOnReply`, not in wait list)
The base case (`default_notificationWaiterConsistent`) and the runtime check
(`notificationWaiterConsistentCheck`) complete the chain.
-/

-- ============================================================================
-- Notification operation ipcInvariant preservation (WS-E4 preparation)
-- ============================================================================

/-- WS-RC R4.C: notificationSignal result notification is well-formed.
    - Wake path: remaining waiters determine idle/waiting state, badge cleared.
    - Merge path: no waiters, active state with merged badge.

    `rest` is the `NoDupList`-typed tail produced by `tail?`; emptiness
    is detected via `rest.val.isEmpty`. -/
theorem notificationSignal_result_wellFormed_wake
    (rest : SeLe4n.NoDupList SeLe4n.ThreadId) :
    notificationQueueWellFormed
      { state := if rest.val.isEmpty then NotificationState.idle else .waiting,
        waitingThreads := rest,
        pendingBadge := none } := by
  unfold notificationQueueWellFormed
  by_cases hEmpty : rest.val = []
  · simp [hEmpty, List.isEmpty]
  · have hNotEmpty : rest.val.isEmpty = false := by
      cases hL : rest.val with
      | nil => exact absurd hL hEmpty
      | cons _ _ => rfl
    simp [hNotEmpty, hEmpty]

theorem notificationSignal_result_wellFormed_merge
    (mergedBadge : SeLe4n.Badge) :
    notificationQueueWellFormed
      { state := .active,
        waitingThreads := SeLe4n.NoDupList.empty,
        pendingBadge := some mergedBadge } := by
  unfold notificationQueueWellFormed; simp

/-- notificationWait result notification is well-formed (badge-consume path):
    idle state, empty waiters, no badge. -/
theorem notificationWait_result_wellFormed_badge :
    notificationQueueWellFormed
      { state := NotificationState.idle,
        waitingThreads := SeLe4n.NoDupList.empty,
        pendingBadge := none } := by
  unfold notificationQueueWellFormed; simp

/-- WS-G7/F-P11/WS-RC R4.C: notificationWait result notification is well-formed
    (wait path): waiting state, non-empty waiter list (prepended), no badge.

    The prepended list is the smart-constructor result
    `consWithGuard? waiter waiters = some wt'`; `wt'.val = waiter ::
    waiters.val` follows from `NoDupList.consWithGuard?_eq_some_iff`. -/
theorem notificationWait_result_wellFormed_wait
    (waiter : SeLe4n.ThreadId)
    (waiters : SeLe4n.NoDupList SeLe4n.ThreadId)
    (wt' : SeLe4n.NoDupList SeLe4n.ThreadId)
    (hCons : wt'.val = waiter :: waiters.val) :
    notificationQueueWellFormed
      { state := .waiting, waitingThreads := wt', pendingBadge := none } := by
  unfold notificationQueueWellFormed
  refine ⟨?_, rfl⟩
  intro h
  rw [hCons] at h
  cases h

-- ============================================================================
-- WS-L3/L3-C: ipcState-queue consistency invariant
-- ============================================================================

/-- WS-L3/L3-C1: ipcState-endpoint consistency. If a thread's ipcState
references an endpoint (blockedOnSend, blockedOnReceive, or blockedOnCall),
that endpoint must exist in the system state. This captures the safety-
critical forward direction of L-G03: no thread can be blocked on a
nonexistent endpoint.

Design note: we use the "endpoint exists" form rather than the stronger
"thread is reachable from queue head" because: (1) it captures the key
safety property, (2) endpointQueuePopHead doesn't update ipcState, creating
a transient state where the thread is dequeued but still "blocked" until
the caller sets it to .ready, and (3) the existence form composes cleanly
with all queue and IPC operations.

**AN3-E.3 (IPC-M07) reachability scope note.** This predicate does not
directly append `∀ tid ∈ queue, st.objectIndex.contains tid.toObjId` —
the object-index reachability property is captured by the orthogonal
`objectIndexSetComplete` invariant (`SeLe4n.Model.State.objectIndexSetComplete`,
`∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true`),
composed with the stronger reachability predicate
`ipcStateQueueMembershipConsistent` (defined just below) which walks the
queueNext chain from each endpoint's queue head.  At every call site
where queue-member object-index reachability is needed, callers thread
these independent invariants; this separation is intentional (Option B
of the plan) because the invariants are preserved by disjoint means:
`ipcStateQueueConsistent` is preserved by every IPC operation that
modifies `ipcState`, while `objectIndexSetComplete` is preserved by
every operation that modifies `objects` or `objectIndexSet`.  Merging
them would force both to co-evolve in every preservation proof, which
would multiply the cascade size without tightening any safety
conclusion the combination already admits at call sites. -/
def ipcStateQueueConsistent (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    match tcb.ipcState with
    | .blockedOnSend epId =>
        ∃ ep, st.objects[epId]? = some (.endpoint ep)
    | .blockedOnReceive epId =>
        ∃ ep, st.objects[epId]? = some (.endpoint ep)
    | .blockedOnCall epId =>
        ∃ ep, st.objects[epId]? = some (.endpoint ep)
    | _ => True

-- ============================================================================
-- V3-G (M-PRF-5): blockedThreadsPendingMessageConsistent invariant
-- (Definition moved above ipcInvariantFull for forward-reference resolution)
-- ============================================================================

/-- V3-J (L-IPC-3): Strengthened ipcState-queue consistency with queue
    reachability predicate. If a thread is blocked on an endpoint, the thread
    must be reachable from that endpoint's corresponding queue head via the
    TCB linkage chain (sendQ for `blockedOnSend`, receiveQ for
    `blockedOnReceive`/`blockedOnCall`).

    Design note: this is stronger than `ipcStateQueueConsistent` which only
    checks endpoint existence. The reachability property captures the
    bidirectional consistency between TCB state and endpoint queue membership.

    The queue reachability is encoded via `QueueNextPath` (defined in
    `Structural.lean`), which follows `queueNext` pointers from the queue
    head. Membership means the thread is reachable from the head within
    a bounded number of hops. -/
def ipcStateQueueMembershipConsistent (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (KernelObject.tcb tcb) →
    match tcb.ipcState with
    | .blockedOnSend epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnReceive epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | .blockedOnCall epId =>
        ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             TCB.queueNext prevTcb = some tid)
    | _ => True

/-- V3-K (L-LIFE-1): No thread appears twice in any endpoint queue.
    For intrusive queues, this means the `queueNext` chain starting from
    `ep.sendQ.head` (resp. `receiveQ.head`) never revisits a thread ID.
    This is captured by `tcbQueueChainAcyclic` (defined above) which
    prevents self-loops and cycles in the `QueueNextPath` relation. The
    endpoint-level property ensures that each endpoint's queues are
    individually cycle-free and non-overlapping. -/
def endpointQueueNoDup (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[oid]? = some (.endpoint ep) →
    -- No thread has itself as queueNext (no self-loops in intrusive chains)
    (∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.objects[tid.toObjId]? = some (.tcb tcb) →
      TCB.queueNext tcb ≠ some tid) ∧
    -- Disjointness: no thread is simultaneously head of both sendQ and receiveQ
    (ep.sendQ.head = none ∨ ep.receiveQ.head = none ∨
     ep.sendQ.head ≠ ep.receiveQ.head)

-- ============================================================================
-- V3-J-cross: Queue-next blocking consistency (cross-queue link prevention)
-- ============================================================================

/-- Helper: the blocking-compatibility condition for two IPC states linked by queueNext.
    Compatible queue types: blockedOnSend and blockedOnCall both map to sendQ,
    so they are mutually compatible. blockedOnReceive maps to receiveQ and is
    only compatible with itself. Cross-queue blocking pairs (receive↔send/call)
    are explicitly rejected (False) to ensure queueNext chains are strictly
    intra-queue, which is required for PopHead V3-J preservation.
    Non-blocking states are unconstrained (True). -/
def queueNextBlockingMatch (s1 s2 : ThreadIpcState) : Prop :=
  match s1, s2 with
  | .blockedOnSend epA, .blockedOnSend epB => epA = epB
  | .blockedOnSend epA, .blockedOnCall epB => epA = epB
  | .blockedOnCall epA, .blockedOnSend epB => epA = epB
  | .blockedOnCall epA, .blockedOnCall epB => epA = epB
  | .blockedOnReceive epA, .blockedOnReceive epB => epA = epB
  | .blockedOnSend _, .blockedOnReceive _ => False
  | .blockedOnReceive _, .blockedOnSend _ => False
  | .blockedOnCall _, .blockedOnReceive _ => False
  | .blockedOnReceive _, .blockedOnCall _ => False
  | _, _ => True

/-- V3-J-cross: If a.queueNext = some b, then a and b are blocked on the same
    endpoint with compatible queue types. This ensures queueNext chains are
    intra-queue, preventing cross-endpoint/cross-queue links that would break
    V3-J preservation through PopHead operations. -/
def queueNextBlockingConsistent (st : SystemState) : Prop :=
  ∀ (a b : SeLe4n.ThreadId) (tcbA tcbB : TCB),
    st.objects[a.toObjId]? = some (.tcb tcbA) →
    st.objects[b.toObjId]? = some (.tcb tcbB) →
    tcbA.queueNext = some b →
    queueNextBlockingMatch tcbA.ipcState tcbB.ipcState

-- ============================================================================
-- V3-J-head: Queue head blocking state consistency
-- ============================================================================

/-- V3-J-head: Queue heads are blocked on the correct endpoint/queue.
    If a thread is the head of an endpoint's receiveQ, it must be
    blockedOnReceive on that endpoint. If it's the head of sendQ, it must
    be blockedOnSend or blockedOnCall on that endpoint. This property is
    needed to discharge hHeadBlocked in PopHead-based V3-J preservation. -/
def queueHeadBlockedConsistent (st : SystemState) : Prop :=
  ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[epId]? = some (.endpoint ep) →
    st.objects[hd.toObjId]? = some (.tcb tcb) →
    (ep.receiveQ.head = some hd → tcb.ipcState = .blockedOnReceive epId) ∧
    (ep.sendQ.head = some hd →
      tcb.ipcState = .blockedOnSend epId ∨ tcb.ipcState = .blockedOnCall epId)

/-- IPC de-threading D4 (Finding F-2): queue **tail** blocking-state consistency — the dual of
`queueHeadBlockedConsistent` for the tail boundary.  If a thread is the tail of an endpoint's
`receiveQ`, it is `.blockedOnReceive` on that endpoint; if it is the tail of `sendQ`, it is
`.blockedOnSend`/`.blockedOnCall` on that endpoint.

This is the missing *reachable→blocked* fact (specialised to the tail) that the enqueue-style
transitions need: `endpointQueueEnqueue` links the **old tail**'s `queueNext` to the freshly
enqueued thread, so establishing `queueNextBlockingConsistent` on the post-state requires the old
tail to be blocked on the same endpoint (`queueNextBlockingMatch`).  The existing
`ipcStateQueueMembershipConsistent` is the *blocked→reachable* converse and does not supply it.

Preserved by every transition by construction: `endpointQueueEnqueue` makes the freshly-enqueued
thread the new tail and the paired block-store sets it `.blockedOnSend`/`.blockedOnReceive`/`.blockedOnCall`;
`endpointQueuePopHead` either leaves the tail unchanged (≥2 elements) or empties the queue
(`tail = none`, vacuous); all other transitions touch neither endpoint tails nor the relevant
`ipcState`s. -/
def endpointQueueTailBlockedConsistent (st : SystemState) : Prop :=
  ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tl : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[epId]? = some (.endpoint ep) →
    st.objects[tl.toObjId]? = some (.tcb tcb) →
    (ep.receiveQ.tail = some tl → tcb.ipcState = .blockedOnReceive epId) ∧
    (ep.sendQ.tail = some tl →
      tcb.ipcState = .blockedOnSend epId ∨ tcb.ipcState = .blockedOnCall epId)

/-- IPC de-threading D4 Slice 2c: the *strict* per-link blocking-propagation invariant — the
intra-queue successor of a blocked thread is blocked on the **same** endpoint/queue.

This is the strict form of `queueNextBlockingMatch` (which admits a `.ready` successor via its
catch-all): if `a.queueNext = some b` and `a` is blocked-on-a-queue, then `b` carries the *same*
blocking direction and endpoint.  Together with `queueHeadBlockedConsistent` (the head is blocked)
it yields "every reachable queue member is blocked", which is exactly the fact the **pop**
(rendezvous) leg needs to re-establish `queueHeadBlockedConsistent`: after popping the head `H`
(blocked on `epId` by the head invariant), the new head is `H.queueNext`, whose blockedness on
`epId` is *not* derivable from the existing conjuncts (`queueNextBlockingMatch`'s catch-all permits a
`.ready` target; `ipcStateQueueMembershipConsistent` is the blocked→reachable converse;
`intrusiveQueueWellFormed` constrains only the head/tail boundary).  It generalises
`endpointQueueTailBlockedConsistent` (the tail specialisation, which becomes derivable from this plus
a tail-membership fact).

Preserved by every transition by construction: `endpointQueueEnqueue` links the old tail's
`queueNext` to the freshly enqueued thread and the paired block-store sets that thread blocked on the
same endpoint (so the new link matches); `endpointQueuePopHead` removes the head's outgoing link
(dropping the only obligation whose source leaves the queue) and leaves every interior link intact;
all other transitions touch neither `queueNext` nor the relevant `ipcState`s. -/
def queueNextTargetBlocked (st : SystemState) : Prop :=
  ∀ (a b : SeLe4n.ThreadId) (tcbA tcbB : TCB),
    st.objects[a.toObjId]? = some (.tcb tcbA) →
    st.objects[b.toObjId]? = some (.tcb tcbB) →
    tcbA.queueNext = some b →
    (∀ ep, tcbA.ipcState = .blockedOnReceive ep → tcbB.ipcState = .blockedOnReceive ep) ∧
    (∀ ep, (tcbA.ipcState = .blockedOnSend ep ∨ tcbA.ipcState = .blockedOnCall ep) →
      (tcbB.ipcState = .blockedOnSend ep ∨ tcbB.ipcState = .blockedOnCall ep))

-- ============================================================================
-- Z6-J: Blocked thread timeout consistency
-- ============================================================================

/-- Z6-J: Blocked thread timeout consistency invariant.

For every thread with `timeoutBudget = some scId`:
1. The referenced SchedContext exists in the object store
2. The thread's `ipcState` is one of the blocking states
   (blockedOnSend, blockedOnReceive, blockedOnCall, blockedOnReply)

This prevents dangling timeout references and ensures `timeoutBlockedThreads`
only encounters valid state when scanning for timed-out threads.

Note: In Z6, `timeoutBudget` defaults to `none` (timeout metadata is deferred
to Z7 donation). This invariant is trivially satisfied when all threads have
`timeoutBudget = none`, which is the case for Z6. The invariant definition is
provided here for completeness and future Z7 integration. -/
def blockedThreadTimeoutConsistent (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.timeoutBudget = some scId →
    -- (1) The SchedContext exists
    (∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc)) ∧
    -- (2) The thread is in a blocking IPC state
    (match tcb.ipcState with
     | .blockedOnSend _ | .blockedOnReceive _ | .blockedOnCall _ | .blockedOnReply _ _ => True
     | _ => False)

/-- Z6-J: Any state where all timeoutBudget fields are `none` trivially
satisfies `blockedThreadTimeoutConsistent`. This covers all states in Z6
since timeout metadata is not set until Z7 donation. -/
theorem blockedThreadTimeoutConsistent_of_all_none
    (st : SystemState)
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.timeoutBudget = none) :
    blockedThreadTimeoutConsistent st := by
  intro tid tcb scId hTcb hBudget
  have := hNone tid tcb hTcb
  rw [this] at hBudget
  cases hBudget

/-- IPC de-threading D5: the strong, transition-invariant form of the timeout-budget discipline —
**no** thread carries a timeout budget.  The seL4-faithful `blockedThreadTimeoutConsistent`
(budget ⇒ blocking IPC state) is strictly *weaker*; this form is what every IPC transition actually
preserves, because no transition ever writes `timeoutBudget := some` (every TCB store either omits
the `timeoutBudget` field or sets it `none`).  A state with all budgets `none` satisfies
`blockedThreadTimeoutConsistent` vacuously (`blockedThreadTimeoutConsistent_of_all_none`), so a
bundle can establish the conjunct on the post-state from this single, uniformly-dischargeable
pre-state precondition — no per-thread "woken thread carries no budget" side-conditions. -/
def allTimeoutBudgetsNone (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.timeoutBudget = none

/-- IPC de-threading D5: the reusable timeout-budget preservation frame.  Every post-state thread's
`timeoutBudget` matches a pre-state thread at the same key — true of every IPC transition, whose TCB
stores all preserve the `timeoutBudget` field (none ever writes `timeoutBudget := some`).  A
fresh-TCB retype is handled directly rather than through this frame, since the retyped slot has no
pre-state TCB to transport back from. -/
def timeoutBudgetFrame (st st' : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    st'.objects[tid.toObjId]? = some (.tcb tcb') →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb.timeoutBudget = tcb'.timeoutBudget

namespace timeoutBudgetFrame

/-- Reflexivity. -/
theorem refl (st : SystemState) : timeoutBudgetFrame st st :=
  fun _ tcb' h => ⟨tcb', h, rfl⟩

/-- Transitivity: chain two frames. -/
theorem trans {st st' st'' : SystemState}
    (h1 : timeoutBudgetFrame st st') (h2 : timeoutBudgetFrame st' st'') :
    timeoutBudgetFrame st st'' := by
  intro tid tcb'' h
  obtain ⟨tcb', h', hB'⟩ := h2 tid tcb'' h
  obtain ⟨tcb, hh, hB⟩ := h1 tid tcb' h'
  exact ⟨tcb, hh, hB.trans hB'⟩

/-- A step that leaves the object map untouched frames trivially. -/
theorem of_objects_eq {st st' : SystemState} (hEq : st'.objects = st.objects) :
    timeoutBudgetFrame st st' :=
  fun _ tcb' h => ⟨tcb', by rw [hEq] at h; exact h, rfl⟩

end timeoutBudgetFrame

/-- IPC de-threading D5: a timeout-budget frame carries `allTimeoutBudgetsNone` forward. -/
theorem allTimeoutBudgetsNone_of_frame {st st' : SystemState}
    (hFrame : timeoutBudgetFrame st st') (hAll : allTimeoutBudgetsNone st) :
    allTimeoutBudgetsNone st' := by
  intro tid tcb' hTcb'
  obtain ⟨tcb, hTcb, hBudgetEq⟩ := hFrame tid tcb' hTcb'
  rw [← hBudgetEq]; exact hAll tid tcb hTcb

/-- IPC de-threading D5: establish `blockedThreadTimeoutConsistent` on the post-state of a
budget-framing transition from the pre-state `allTimeoutBudgetsNone` precondition. -/
theorem blockedThreadTimeoutConsistent_of_frame {st st' : SystemState}
    (hFrame : timeoutBudgetFrame st st') (hAll : allTimeoutBudgetsNone st) :
    blockedThreadTimeoutConsistent st' :=
  blockedThreadTimeoutConsistent_of_all_none st' (allTimeoutBudgetsNone_of_frame hFrame hAll)

-- ============================================================================
-- Z7-F: Donation chain acyclicity
-- ============================================================================

/-- Z7-F: No circular SchedContext donation chains.

If thread A has `.donated(scId, B)` binding (A borrowed B's SchedContext),
then B must NOT have a `.donated(_, A)` binding. This prevents resource leaks
from circular donation where no thread can return the SchedContext.

Formalized as: for every pair of threads with donated bindings, the donation
edges do not form a cycle of length 2. Longer cycles are prevented by the
IPC structure: a thread blocked on reply cannot initiate another Call.

WS-OD OD2: this is about the **binding** graph — the `.donated scId owner` edges
— and it stays true once donation becomes transitive, because the binding's
`owner` is always the *immediate* donor, so a `.donated` thread never acquires an
outgoing edge at all.  The transitive structure is the reply stack, and its
acyclicity is `donationChainWellFormed`'s obligation, not this conjunct's.

AF5-E (AF-39): `donationChainAcyclic` explicitly prevents 2-cycles (mutual
donation pairs). Longer cycles (k > 2) are prevented by IPC protocol:
a thread in `.blockedOnReply` state (waiting for reply from its donation
target) cannot initiate a new `Call` (its ipcState is not `.ready`),
breaking any potential chain of length > 2.

AG8-F: The structural building blocks are `donationChainAcyclic_general`
(re-extracts the blocked-on-reply property from `donationOwnerValid`) and
`blockedOnReply_cannot_call` (proves blocked threads cannot call). These
provide the *ingredients* of the k>2 prevention argument, but the formal
bridge lemma from donation edges to `blockingAcyclic` (proving donation
chains are a sub-relation of the blocking graph) is recorded as a post-1.0
hardening candidate; registered in `docs/REGISTERED_DEBT.md`
(Registered debt index, C.1). -/
def donationChainAcyclic (st : SystemState) : Prop :=
  ∀ (tid1 tid2 : SeLe4n.ThreadId) (tcb1 tcb2 : TCB)
    (scId1 scId2 : SeLe4n.SchedContextId),
    st.objects[tid1.toObjId]? = some (.tcb tcb1) →
    st.objects[tid2.toObjId]? = some (.tcb tcb2) →
    tcb1.schedContextBinding = .donated scId1 tid2 →
    tcb2.schedContextBinding = .donated scId2 tid1 →
    False

-- ============================================================================
-- Z7-G: Donation owner validity
-- ============================================================================

/-- Z7-G: Every donated SchedContext binding references valid objects.

For every TCB with `.donated(scId, originalOwner)`:
1. The SchedContext object exists in the store and points to the server
2. The original owner thread exists as a TCB
3. The original owner is blocked on reply (waiting for the server to reply)
4. (AUD-7 / Finding F-3) The original owner's binding is `.unbound` — the donor
   gave up its SchedContext when it donated (`donateSchedContext` clears it),
   so the SchedContext is referenced by **exactly one** binding (the server's
   `.donated`).  This is what makes `donationBudgetTransfer` satisfiable for
   donated states.  The donor is recoverable through the reply object (clause 3),
   not through a residual `.bound` binding: `returnDonatedSchedContext` rebinds
   it on reply.  `.unbound` is distinct from `.donated`, so this clause keeps the
   **binding graph** free of `.donated` chains of length ≥ 2 (see
   `donationOwnerValid_implies_donationChainAcyclic` and
   `donationChain_no_extension`).

   WS-OD OD2: read that as a statement about *bindings*, which is what it is —
   not as a bound on how far a scheduling context may travel.  Onward donation
   keeps it true at every call depth by keeping the binding's `owner` at the
   **immediate** donor: in a chain `D0 → D1 → D2`, only `D2` is `.donated sc D1`,
   while `D1` and `D0` are `.unbound` ∧ `.blockedOnReply`.  The transitive
   structure lives in the reply stack (`Reply.prev` / `SchedContext.scReply`),
   where `donationChainWellFormed` constrains it, so this clause and a depth-`n`
   chain are not in tension. -/
def donationOwnerValid (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .donated scId owner →
    (∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      sc.boundThread = some tid) ∧
    (∃ ownerTcb, st.objects[owner.toObjId]? = some (.tcb ownerTcb) ∧
      ownerTcb.schedContextBinding = .unbound ∧
      ∃ epId replyTarget, ownerTcb.ipcState = .blockedOnReply epId replyTarget)

/-- WS-OD OD4.4: **the one clause of `donationReturnOuterValid` a caller must
supply.**

`outerCallerAcceptable` — the pop's own O(1) guard — decides the other three
(the outer caller is a stored, `.unbound`, reply-blocked TCB, and is neither of
the two threads the pop rewrites).  This one is quantified over the **whole
store**, so no O(1) guard can decide it and it stays where it can be discharged:
at the caller, from the reachability layer.

It is what `donationOwnerUnique` needs.  The pop makes the rebound thread name
`outer`, and the rebound thread is provably not the pre-state holder of a
donation (it is `.unbound` before the step), so a pre-state donation naming
`outer` would leave two distinct threads naming it.  True of every chain this
kernel builds — a thread that donated onward gave up its binding, and the
binding that named it was overwritten by the onward donation — and not a
consequence of the other three clauses. -/
def donationOuterUnowned (st : SystemState)
    (newOwner? : Option SeLe4n.ThreadId) : Prop :=
  ∀ outer, newOwner? = some outer →
    ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scIdx : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scIdx outer

/-- WS-OD OD4.4: vacuous at the bottom of the reply stack. -/
theorem donationOuterUnowned_none (st : SystemState) :
    donationOuterUnowned st none := fun _ h => by cases h

/-- WS-OD OD3.2: **what a depth-≥ 2 donation return owes `donationOwnerValid`.**

The pop writes `donationReturnBinding scId newOwner?` at the thread it hands the
scheduling context back to.  At the bottom of the reply stack that is
`.bound scId` and `donationOwnerValid` has nothing to say about it; one level up
it is `.donated scId outer`, and the conjunct then demands of `outer` exactly
what `donateSchedContext`'s own donation site demands of a donor — a TCB that
gave up its binding and is waiting on its reply.

Two things this predicate is, deliberately.  It is a **pre-state** obligation
with the two distinctness conditions that carry it across the pop's own writes
(`outer` is neither the thread being rebound nor the server being unbound), so a
caller discharges it from what it knew before the step.  And it is stated *now*,
in the row that widens the binding, rather than in the row that first produces a
`some` — a live transition whose preservation theorem is conditioned on an arm it
can take is exactly the shape this project's plan rule forbids.

Vacuous at `newOwner? = none` (`donationReturnOuterValid_none`), which is every
call site in the tree today; discharged from the reply stack at depth ≥ 2, where
`donationChainWellFormed` and the outer reply together identify `outer` as the
caller the next frame down. -/
structure donationReturnOuterValid (st : SystemState)
    (serverTid originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) : Prop where
  /-- The outer caller is a thread that has given up its binding and is waiting
  on a reply — the donor shape `donationOwnerValid` requires. -/
  outerIsDonor : ∀ outer, newOwner? = some outer →
    ∃ outerTcb, st.objects[outer.toObjId]? = some (.tcb outerTcb) ∧
      outerTcb.schedContextBinding = .unbound ∧
      ∃ epId replyTarget, outerTcb.ipcState = .blockedOnReply epId replyTarget
  /-- The outer caller is not the thread being rebound: a donation whose owner is
  itself would be a self-loop, and the pop would then be writing the fact it is
  supposed to be reading. -/
  outerNeTarget : ∀ outer, newOwner? = some outer → outer ≠ originalOwner
  /-- The outer caller is not the server being unbound: the server's own binding
  is overwritten by this step, so a claim about its pre-state shape would not
  survive it. -/
  outerNeServer : ∀ outer, newOwner? = some outer → outer ≠ serverTid
  /-- No thread already names the outer caller as its donation owner.  The pop
  makes the rebound thread name `outer`, and `donationOwnerUnique` says at most
  one thread may — true of a real chain, where every thread above `outer` gave up
  its binding when it donated onward, and false of nothing this kernel builds,
  but not a consequence of the other three clauses. -/
  outerUnowned : donationOuterUnowned st newOwner?

/-- WS-OD OD3.2: the obligation is vacuous when the context goes back to the
bottom of the stack.  That was the shape of *every* donation return in the tree
until OD4.1 (`v0.35.2`) made a stack of depth ≥ 2 reachable; it is now the
depth-1 case, which is still the common one. -/
theorem donationReturnOuterValid_none (st : SystemState)
    (serverTid originalOwner : SeLe4n.ThreadId) :
    donationReturnOuterValid st serverTid originalOwner none :=
  { outerIsDonor := fun _ h => by cases h
    outerNeTarget := fun _ h => by cases h
    outerNeServer := fun _ h => by cases h
    outerUnowned := donationOuterUnowned_none st }


/-- WS-OD OD4.4: **the outer caller a reply stack names is a proper waiting
donor, and nobody else owns it.**

The obligation a call site carries once it threads `replyStackOuterCaller?`.
Two clauses, because the pop needs two different kinds of fact about the thread
the context settles on and only one of them is decidable in O(1):

* `outerCallerAcceptable` is the pop's **own** guard — a stored, `.unbound`,
  reply-blocked TCB that is neither of the two threads the pop rewrites.  Stating
  it here as an obligation rather than reading it off the pop's success is what
  makes a *success* theorem statable at all: `returnDonatedSchedContext` refuses
  an unacceptable outer caller, so a site that must not refuse has to know the
  guard passes before it runs.
* `donationOuterUnowned` is whole-store quantified, so no O(1) guard can decide
  it; `donationOwnerUnique` is what needs it.

Both are vacuous when the resolver answers `none`
(`replyStackOuterCallerValid_of_no_stack`), which is every state the tree reached
before OD4.1's push and every depth-1 state after it.  At depth ≥ 2 they are what
a strengthened chain invariant will discharge — the chain constrains
`Reply.prev` and `Reply.next` and says of `Reply.caller` only that a linked frame
has one, so the thread-side facts are stated rather than derived. -/
def replyStackOuterCallerValid (st : SystemState) (scId : SeLe4n.SchedContextId)
    (serverTid originalOwner : SeLe4n.ThreadId) : Prop :=
  ∀ newOwner?, replyStackOuterCaller? st scId = .ok newOwner? →
    outerCallerAcceptable st serverTid originalOwner newOwner? = true ∧
    donationOuterUnowned st newOwner?

/-- WS-OD OD4.4: on a context that heads no reply stack the obligation is
discharged outright — the resolver answers `none`, and both clauses are vacuous
there. -/
theorem replyStackOuterCallerValid_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (serverTid originalOwner : SeLe4n.ThreadId)
    (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNoHead : sc.scReply = none) :
    replyStackOuterCallerValid st scId serverTid originalOwner := by
  intro newOwner? hRes
  rw [replyStackOuterCaller?_of_no_stack st scId sc hSc hNoHead] at hRes
  obtain rfl : newOwner? = none := (Except.ok.inj hRes).symm
  exact ⟨outerCallerAcceptable_none st serverTid originalOwner, donationOuterUnowned_none st⟩

/-- WS-OD OD4.4: **the obligation discharged whole, on a state whose scheduling
contexts head no reply stacks.**

The shape every inhabitation witness and every pre-push state has: no context
heads a stack, so the resolver answers `none` at every context that resolves and
refuses at every context that does not, and both clauses are vacuous either way. -/
theorem replyStackOuterCallerValid_of_no_stacks (st : SystemState)
    (hNoHeads : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
      st.getSchedContext? scId = some sc → sc.scReply = none)
    (scId : SeLe4n.SchedContextId) (serverTid originalOwner : SeLe4n.ThreadId) :
    replyStackOuterCallerValid st scId serverTid originalOwner := by
  intro newOwner? hRes
  cases hSc : st.getSchedContext? scId with
  | none => unfold replyStackOuterCaller? at hRes; rw [hSc] at hRes; cases hRes
  | some sc =>
    exact replyStackOuterCallerValid_of_no_stack st scId serverTid originalOwner sc hSc
      (hNoHeads scId sc hSc) newOwner? hRes

/-- WS-OD OD4.4: **the outer-caller obligation for a cleanup pop.**

The pre-receive cleanup and thread destruction resolve their scheduling context
from the *receiver's own binding* rather than taking it as an argument, so the
obligation their bundle proofs carry is stated over the receiver: whatever
context the receiver holds, the outer caller its stack names is a proper waiting
donor.  Vacuous on every state where that context heads no reply stack. -/
def cleanupDonationStackValid (st : SystemState) (receiver : SeLe4n.ThreadId) : Prop :=
  ∀ (recvTcb : TCB) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    lookupTcb st receiver = some recvTcb →
    recvTcb.schedContextBinding = .donated scId owner →
    replyStackOuterCallerValid st scId receiver owner

/-- WS-OD OD4.4: **what the pop's outer-caller guard decides**, unpacked.

Three facts, read off one Boolean: the outer caller is neither of the two threads
the pop rewrites, and it is a stored TCB in the donor shape `donationOwnerValid`
demands of a donation's owner. -/
theorem outerCallerAcceptable_some_char (st : SystemState)
    (serverTid originalOwner outer : SeLe4n.ThreadId)
    (h : outerCallerAcceptable st serverTid originalOwner (some outer) = true) :
    outer ≠ originalOwner ∧ outer ≠ serverTid ∧
    ∃ outerTcb, st.getTcb? outer = some outerTcb ∧
      outerTcb.schedContextBinding = .unbound ∧
      ∃ epId replyTarget, outerTcb.ipcState = .blockedOnReply epId replyTarget := by
  unfold outerCallerAcceptable at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  revert h3
  cases hT : st.getTcb? outer with
  | none => intro hc; exact absurd hc (by simp)
  | some outerTcb =>
    simp only []
    intro h3
    simp only [Bool.and_eq_true] at h3
    obtain ⟨hB, hI⟩ := h3
    -- `BEq SchedContextBinding` is hand-written (`SchedContext/Types.lean`), so
    -- the `==` is discharged by evaluation on the three constructors rather than
    -- through a `LawfulBEq` instance the type does not carry.
    have hBnd : outerTcb.schedContextBinding = SchedContextBinding.unbound := by
      revert hB; cases outerTcb.schedContextBinding <;> simp [BEq.beq]
    -- The `cases` above substituted the typed read in the goal, so the
    -- conclusion's equation is definitional here.
    refine ⟨outerTcb, rfl, hBnd, ?_⟩
    revert hI
    cases hIpc : outerTcb.ipcState with
    | blockedOnReply ep rt => intro _; exact ⟨ep, rt, rfl⟩
    | ready => intro hc; exact absurd hc (by simp)
    | blockedOnSend _ => intro hc; exact absurd hc (by simp)
    | blockedOnReceive _ => intro hc; exact absurd hc (by simp)
    | blockedOnCall _ => intro hc; exact absurd hc (by simp)
    | blockedOnNotification _ => intro hc; exact absurd hc (by simp)

/-- WS-OD OD4.4: **the obligation, from the pop's own guard plus the one clause
the guard cannot decide.**

This is what makes OD4.4's call sites cheap: a site that has threaded a resolved
`newOwner?` and holds `donationOuterUnowned` gets `donationReturnOuterValid` for
free, because the operation it is about to run has already checked the rest. -/
theorem donationReturnOuterValid_of_acceptable (st : SystemState)
    (serverTid originalOwner : SeLe4n.ThreadId) (newOwner? : Option SeLe4n.ThreadId)
    (hAcc : outerCallerAcceptable st serverTid originalOwner newOwner? = true)
    (hUnowned : donationOuterUnowned st newOwner?) :
    donationReturnOuterValid st serverTid originalOwner newOwner? := by
  cases hN : newOwner? with
  | none => subst hN; exact donationReturnOuterValid_none st serverTid originalOwner
  | some outer =>
    subst hN
    obtain ⟨hNeT, hNeS, outerTcb, hObj, hUnbound, hBlk⟩ :=
      outerCallerAcceptable_some_char st serverTid originalOwner outer hAcc
    exact
      { outerIsDonor := fun o hO => by
          obtain rfl := Option.some.inj hO
          exact ⟨outerTcb, (SystemState.getTcb?_eq_some_iff st outer outerTcb).mp hObj,
            hUnbound, hBlk⟩
        outerNeTarget := fun o hO => by obtain rfl := Option.some.inj hO; exact hNeT
        outerNeServer := fun o hO => by obtain rfl := Option.some.inj hO; exact hNeS
        outerUnowned := hUnowned }

/-- WS-OD OD4.4: **and from a successful pop**, which is the form the call sites
actually reach for: the guard is a consequence of the operation returning `.ok`,
so a site that has already run the pop need not re-evaluate it. -/
theorem donationReturnOuterValid_of_ok
    {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (hUnowned : donationOuterUnowned st newOwner?) :
    donationReturnOuterValid st serverTid originalOwner newOwner? :=
  donationReturnOuterValid_of_acceptable st serverTid originalOwner newOwner?
    (returnDonatedSchedContext_ok_outerAcceptable st st' serverTid scId originalOwner
      newOwner? h) hUnowned

/-- WS-OD OD4.4: **and from the stack obligation at a resolved answer** — the
form the six threaded call sites reach for, since none of them names a
`newOwner?`: they thread the resolver, and their hypothesis is about whatever it
answers. -/
theorem donationReturnOuterValid_of_stackValid {st : SystemState}
    {scId : SeLe4n.SchedContextId} {serverTid originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (hValid : replyStackOuterCallerValid st scId serverTid originalOwner)
    (hRes : replyStackOuterCaller? st scId = .ok newOwner?) :
    donationReturnOuterValid st serverTid originalOwner newOwner? :=
  donationReturnOuterValid_of_acceptable st serverTid originalOwner newOwner?
    (hValid newOwner? hRes).1 (hValid newOwner? hRes).2

/-- WS-OD OD4.4: and the cleanup-shaped obligation with it. -/
theorem cleanupDonationStackValid_of_no_stacks (st : SystemState)
    (hNoHeads : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
      st.getSchedContext? scId = some sc → sc.scReply = none)
    (receiver : SeLe4n.ThreadId) :
    cleanupDonationStackValid st receiver :=
  fun _ scId owner _ _ =>
    replyStackOuterCallerValid_of_no_stacks st hNoHeads scId receiver owner

-- ============================================================================
-- WS-OD OD5.2 — what a cancelled MIDDLE caller's scheduling context does
-- ============================================================================

/-- **WS-OD OD5.2: the answers plan §3.4 puts to this workstream, named.**

What happens to the scheduling context of a *middle* caller taken out of a chain
— by a cancellation, or by a delegated reply capability answering out of order —
is a decision, and the plan forbids inheriting one by omission.  Every candidate
is named here so that the choice below is a statement rather than an accident of
a field read.

**The premise this list was first written under is gone** (`v0.35.4`).  It read
"`Reply` carries `prev` and no `next`, so a middle frame cannot be spliced out of
a reply stack by a backward scan", which was true of the singly linked stack and
has not been true since the stack became doubly linked: `Reply.next` is exactly
the field a splice needs.  `spliceOutTheCut` is the candidate that field made
available, and it is named rather than the stale sentence being trimmed — a
policy justified by a data structure the tree no longer has is a justification
that has stopped being read. -/
inductive CancelledMiddleCallerPolicy where
  /-- **Sever at the cut.**  The frame above the cut stops linking down
  (`detachReplyFrameAbove` writes `prev := none`), so every frame *below* the cut
  leaves the context's stack; the pop that later reaches the frame above reads
  `none` and binds that caller `.bound scId`.  `O(1)` at every depth, and the
  policy this kernel implements.

  What it costs is **measured** at stack depth three in `tests/SmpIpcSuite.lean`
  §3.22, not described: at depth two the frame below the cut is the bottom of the
  stack, so this and `spliceOutTheCut` write the same value into the frame above
  and the two cannot be told apart. -/
  | severAtCut
  /-- **Splice the cut frame out.**  The ordinary doubly-linked-list removal: the
  frame above takes the cut frame's own `prev`, the frame below takes its `next`.
  The frames below stay on the stack, so the reservation goes on travelling
  outward to the thread that owns it — strictly better accounting, and also
  `O(1)`.

  **This is what seL4-MCS does**, confirmed against its source at `v0.35.14`
  rather than assumed: `reply_remove`'s non-head branch writes
  `REPLY_PTR(call_stack_get_callStackPtr(reply->replyNext))->replyPrev =
  reply->replyPrev`, so the frame above inherits the cut frame's own outward
  pointer and every frame below stays reachable from the head.  `severAtCut` is
  therefore a **divergence** from upstream and not an inheritance of it — which
  is the opposite of what this file asserted before that check.

  `cancelledMiddleCallerPolicy`'s third reason is why this kernel diverges, and
  it is a property of **when this kernel pops** rather than of the splice
  itself. -/
  | spliceOutTheCut
  /-- **Reclaim to the cancelled thread.**  The cancellation reaches the
  context's real holder through `SchedContext.scReply` / `boundThread` and hands
  the context back to the thread being cancelled, consistent with the depth-1
  head case.  A deliberate divergence from seL4: it takes the budget away from a
  callee that is still running on it, and unwinding the frames between costs
  `O(depth)`. -/
  | reclaimToCancelledThread
  deriving DecidableEq, Repr

/-- **WS-OD OD5.2: this kernel severs at the cut.**

Chosen for three reasons, in order of weight.

1. **It is what the pop already does**, so the depth-1 head case and the
   depth-`n` middle case are one program rather than two:
   `replyStackOuterCaller?` answers `none` in both, and
   `cancelledMiddleCaller_severs_at_cut` proves the pop's *effect* is the same
   one.  The alternative needs a second transition and a second set of bundle
   proofs for a state the first one already reaches.
2. **It is `O(1)`.**  The alternative walks the frames between the cancelled
   thread and the holder; a `LockSet` is capped at `maxLockSetSize` and a chain
   is not, so a reclaim that traverses the chain could not be given a footprint
   at all -- the same argument OD3.7 makes for the pop's single frame of
   lookahead.
3. **It keeps this kernel's pop trigger sound**, which is the reason that
   actually carries the decision and the one a reader must not mistake for an
   appeal to upstream.  This kernel decides whether a reply pops a donation from
   the **recorded server's binding** (`endpointReplyServerDonation?`, resolved
   through `recordedReplyServer?`), *not* from whether the answered frame heads a
   context.  Under `severAtCut` those two facts stay equivalent: a frame heads a
   context exactly while the server it recorded still holds the donation, since a
   server that donated onward pushed a new head, and the frames below a cut leave
   the stack altogether rather than waiting to be re-headed.

   `spliceOutTheCut` breaks the equivalence.  It re-heads a frame whose recorded
   server is by then gone and `.unbound`, so answering that frame runs **no** pop;
   `Reply.consumed` keeps a head's links; and the resulting state is a consumed
   frame heading a context while a live `.donated` holder still names its owner —
   exactly what `replyStackOuterCaller?_of_consumed_frame` refuses, and the object
   pinning `v0.35.4` closed.  The three coherence facts the reply path carries as
   *stated* pre-state hypotheses — `replyStackHeadIsAnsweredReply`,
   `replyDonationOwnerIsAnsweredCaller` and `answeredHeadContextIsServerDonation`
   — are that equivalence in the form their consumers need, and no invariant in
   this tree entails them.

   So taking the splice means moving the pop's *trigger* to head-ness and its
   *source* to `SchedContext.boundThread`, which is a workstream rather than a
   field write.  It is registered in `docs/REGISTERED_DEBT.md` with a closure
   target, not left as an unexamined preference.

   **And this is a divergence from seL4-MCS, stated as one.**  Until `v0.35.14`
   this file asserted the opposite — that severing was upstream's structural
   answer.  Checked against the source, `reply_remove`'s non-head branch splices
   (`next->replyPrev = reply->replyPrev`), so every frame below a cut stays on
   the stack there and the reservation goes on travelling outward.  The
   divergence costs what `tests/SmpIpcSuite.lean` §3.22 measures, it is registered
   in `docs/REGISTERED_DEBT.md` with an owner and a closure target, and v1.0.0
   must not claim seL4-MCS reply-stack semantics at chain depth ≥ 3.  A
   `reply_remove_tcb` reference elsewhere in this tree names an operation's
   *shape*; it is not evidence about what upstream writes.

   Before `v0.35.4` the same policy was implemented by *leaving the cut frame on
   the stack* with its `caller` consumed and letting the pop read a consumed
   frame as the bottom.  That frame then headed the stack forever: nothing
   popped it, so its Reply object and the context could never be retyped and the
   Reply could never be linked again — an ordinary `.tcbSuspend` of a client
   whose server nested a call burned one of the server's Reply objects per round.
   The detach is what closes that; the resolver now **refuses** a consumed frame
   (`replyStackOuterCaller?_of_consumed_frame`, `.error .illegalState`) rather
   than reading it as the bottom.

What it costs is measured rather than hidden.  Neither the cut thread nor the
chain's **original** owner gets the scheduling context back: it settles on the
caller immediately above the cut, bound `.bound scId` outright, and **no later
pop carries it below the cut** -- the frames below left the stack, and a `.bound`
holder is not a donation, so nothing pops it.  At stack depth three
(`tests/SmpIpcSuite.lean` §3.22) that owner is two hops outside the cut and the
reservation settles on a thread strictly inside the chain, where the *same* stack
unwound in order delivers it outward still owed; depth three is the shallowest
stack on which this is visible at all.

The authority needed is the authority to unblock the thread being cut -- a
suspend right over it, or possession of its reply capability, which a callee's
confederate may legitimately hold.  It is a **fairness** divergence, not a safety
one: the resulting state satisfies `donationOwnerValid` and `passiveServerIdle`,
no budget is lost to the system, and -- since `v0.35.4` -- no object is pinned,
because a frame cut off the stack carries no `.head` link and so is cleared
outright when its own caller is consumed (`Reply.consumed`'s non-head branch,
exercised in §3.22). -/
def cancelledMiddleCallerPolicy : CancelledMiddleCallerPolicy := .severAtCut

/-- WS-OD OD5.2: and the decision is checkable, not merely declared -- a cut that
switched the policy has to change this line and the two theorems that read it. -/
@[simp] theorem cancelledMiddleCallerPolicy_eq :
    cancelledMiddleCallerPolicy = CancelledMiddleCallerPolicy.severAtCut := rfl

/-- **WS-OD OD5.2 / `v0.35.4`: the resolver implements `severAtCut` at the cut.**

After the detach the frame above the cut has no `prev` — it is the bottom of the
stack it heads — so the resolver answers `none` at it and the pop binds its
caller outright.  Stated against the policy constant, so the policy has a
consumer rather than being a name nothing reads; a cut that chose
`reclaimToCancelledThread` would have to make this false.  The companion
`replyStackOuterCaller?_of_consumed_frame` is the *other* half of the same
decision: a frame that was left below a head with its caller consumed — the
pre-`v0.35.4` implementation of the policy — is refused, never read as the
bottom. -/
theorem replyStackOuterCaller?_follows_policy (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (hSc : st.getSchedContext? scId = some sc)
    (hHead : donationHeadOf? st scId sc = .ok (some (rid, r)))
    (hCut : r.prev = none) :
    cancelledMiddleCallerPolicy = CancelledMiddleCallerPolicy.severAtCut ∧
      replyStackOuterCaller? st scId = .ok none :=
  ⟨rfl, replyStackOuterCaller?_of_bottom_head st scId sc rid r hSc hHead hCut⟩

/-- Z7-H': Donation-owner uniqueness.  No two **distinct** threads name the same `owner` in a
`.donated _ owner` binding.  Semantically: a thread becomes a donation `owner` only by donating
its (single) SchedContext on a `Call`, and while it is `.blockedOnReply` it cannot make another
call — so at most one server holds a `.donated _ owner` binding for it at a time.

This is the consistency property the donation **return** needs: when `returnDonatedSchedContext`
hands the SchedContext back (the owner goes `.unbound` → `.bound scId`), `donationOwnerValid`
requires the *owner of every remaining donation* to still be `.unbound`; uniqueness guarantees the
just-rebound owner is not the owner of any *other* live donation, so no remaining obligation
breaks.  It is preserved by every IPC transition: the binding-frame transitions inject post-state
donations into the pre-state (`sameSchedContextBindings`, backward), and the donation **return**
only *removes* a donation. -/
def donationOwnerUnique (st : SystemState) : Prop :=
  ∀ (tid1 tid2 : SeLe4n.ThreadId) (tcb1 tcb2 : TCB)
    (scId1 scId2 : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.objects[tid1.toObjId]? = some (.tcb tcb1) →
    st.objects[tid2.toObjId]? = some (.tcb tcb2) →
    tcb1.schedContextBinding = .donated scId1 owner →
    tcb2.schedContextBinding = .donated scId2 owner →
    tid1 = tid2

/-- Z7-H': the empty/donation-free state satisfies `donationOwnerUnique` vacuously. -/
theorem donationOwnerUnique_of_no_donations
    (st : SystemState)
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
      (owner : SeLe4n.ThreadId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId owner) :
    donationOwnerUnique st := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 _ hB1 _
  exact absurd hB1 (hNone tid1 tcb1 scId1 owner h1)

/-- IPC de-threading D6: an object-store-preserving step frames `donationOwnerUnique`. -/
theorem donationOwnerUnique_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : donationOwnerUnique st) :
    donationOwnerUnique st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  rw [hObjs] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

/-- WS-RR RR2.5: an object-store-preserving step frames `donationOwnerValid` — it
reads the store and nothing else.  The `_of_objects_eq` family already carried
`donationOwnerUnique` and `endpointQueueTailBlockedConsistent`; the two remaining
donation conjuncts that read only the store were missing from it, so every
scheduler-only transition had to re-derive them. -/
theorem donationOwnerValid_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : donationOwnerValid st) :
    donationOwnerValid st' := by
  intro tid tcb scId owner hTcb hBind
  rw [hObjs] at hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ownerTcb, hOwner, hUnbound, hBlk⟩ := h tid tcb scId owner hTcb hBind
  exact ⟨⟨sc, by rw [hObjs]; exact hSc, hBound⟩,
    ownerTcb, by rw [hObjs]; exact hOwner, hUnbound, hBlk⟩

/-- WS-RR RR2.5: an object-store-preserving step frames `donationChainAcyclic`. -/
theorem donationChainAcyclic_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : donationChainAcyclic st) :
    donationChainAcyclic st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  rw [hObjs] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

/-- IPC de-threading D4 (Finding F-2): an object-preserving step frames
`endpointQueueTailBlockedConsistent`. -/
theorem endpointQueueTailBlockedConsistent_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent st' := by
  intro epId ep tl tcb hEp hTcb
  rw [hObjs] at hEp hTcb
  exact h epId ep tl tcb hEp hTcb

-- ============================================================================
-- Z7-H: Passive server idle invariant
-- ============================================================================

/-- Z7-H: Unbound threads not in the RunQueue are passive servers or donors.

An unbound thread that is not runnable and not the current thread must be in a
benign idle/blocked state:
- `.ready` (inactive, not yet enqueued), or
- blocked on receive (a passive server waiting for a client call), or
- blocked on notification, or
- blocked on reply (Finding F-3): a **donor** that donated its SchedContext to a
  passive server during a Call and is now `.unbound`, awaiting the reply that
  `returnDonatedSchedContext` will rebind it through.

It must **not** be blocked on send/call — those require a SchedContext for the
timeout, which an unbound thread does not hold.  (A donor is `.blockedOnReply`,
*not* `.blockedOnSend`/`.blockedOnCall`: it has already completed its Call.) -/
def passiveServerIdle (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .unbound →
    tid ∉ (st.scheduler.runQueueOnCore bootCoreId) →
    (st.scheduler.currentOnCore bootCoreId) ≠ some tid →
    (tcb.ipcState = .ready ∨
     (∃ epId, tcb.ipcState = .blockedOnReceive epId ∨
              tcb.ipcState = .blockedOnNotification epId) ∨
     ∃ epId replyTarget, tcb.ipcState = .blockedOnReply epId replyTarget)

/-- The set of `ipcState`s permitted for an unbound, descheduled (passive) thread by
`passiveServerIdle` — `.ready`, `.blockedOnReceive`, `.blockedOnNotification`, or
`.blockedOnReply` (definitionally the disjunction in `passiveServerIdle`'s conclusion).
The excluded states are `.blockedOnSend`/`.blockedOnCall`, which require a SchedContext for
their timeout. -/
def passiveServerIdleAllowed (s : ThreadIpcState) : Prop :=
  s = .ready ∨
  (∃ epId, s = .blockedOnReceive epId ∨ s = .blockedOnNotification epId) ∨
  ∃ epId replyTarget, s = .blockedOnReply epId replyTarget

/-- IPC de-threading D6 (`passiveServerIdle`): the reusable preservation frame.

A transition preserves `passiveServerIdle` whenever every thread that is **unbound + descheduled**
(not in the boot run queue, not the boot current thread) **and not already in an allowed state** in
the post-state pulls **back** to an unbound + descheduled thread in the pre-state with the *same*
`ipcState`.

The `¬ passiveServerIdleAllowed` filter is the crux: the only threads a transition newly drives into
a `.blockedOnSend`/`.blockedOnCall` (non-allowed) state are the running sender/caller — which hold a
SchedContext (not `.unbound`, so excluded by the `unbound` hypothesis) — while every thread the
transition *blocks* into an allowed state (`.blockedOnReceive`/`.blockedOnNotification`/
`.blockedOnReply`) or *wakes* `.ready` is filtered out by `passiveServerIdleAllowed`.  Hence the
pullback obligation only ever fires on threads the transition leaves untouched. -/
structure passiveServerIdleFrame (st st' : SystemState) : Prop where
  pullback : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    st'.objects[tid.toObjId]? = some (.tcb tcb') →
    tcb'.schedContextBinding = .unbound →
    tid ∉ (st'.scheduler.runQueueOnCore bootCoreId) →
    (st'.scheduler.currentOnCore bootCoreId) ≠ some tid →
    ¬ passiveServerIdleAllowed tcb'.ipcState →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.schedContextBinding = .unbound ∧
      tid ∉ (st.scheduler.runQueueOnCore bootCoreId) ∧
      (st.scheduler.currentOnCore bootCoreId) ≠ some tid ∧
      tcb.ipcState = tcb'.ipcState

namespace passiveServerIdleFrame

/-- Reflexivity: a state frames onto itself. -/
theorem refl (st : SystemState) : passiveServerIdleFrame st st :=
  ⟨fun _ tcb' h hU hQ hC _ => ⟨tcb', h, hU, hQ, hC, rfl⟩⟩

/-- Transitivity: chain two passive-server frames. -/
theorem trans {st st' st'' : SystemState}
    (h1 : passiveServerIdleFrame st st') (h2 : passiveServerIdleFrame st' st'') :
    passiveServerIdleFrame st st'' :=
  ⟨fun tid tcb'' h hU hQ hC hNA => by
    obtain ⟨tcb', h', hU', hQ', hC', hIpc'⟩ := h2.pullback tid tcb'' h hU hQ hC hNA
    obtain ⟨tcb, hh, hUU, hQQ, hCC, hIpc⟩ := h1.pullback tid tcb' h' hU' hQ' hC' (hIpc' ▸ hNA)
    exact ⟨tcb, hh, hUU, hQQ, hCC, hIpc.trans hIpc'⟩⟩

/-- A step that leaves the object map **and** the boot-core scheduler state untouched frames
trivially. -/
theorem of_objects_scheduler_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects)
    (hRq : st'.scheduler.runQueueOnCore bootCoreId = st.scheduler.runQueueOnCore bootCoreId)
    (hCur : st'.scheduler.currentOnCore bootCoreId = st.scheduler.currentOnCore bootCoreId) :
    passiveServerIdleFrame st st' :=
  ⟨fun _ tcb' h hU hQ hC _ =>
    ⟨tcb', by rw [hObjs] at h; exact h, hU, by rw [hRq] at hQ; exact hQ,
      by rw [hCur] at hC; exact hC, rfl⟩⟩

end passiveServerIdleFrame

-- ============================================================================
-- WS-OD OD2.4 / OD2.5 / `v0.35.4`: the SchedContext donation chain (the MCS reply stack)
-- ============================================================================

/-! ### The reply stack, and the two projections every reader of it goes through

A `Call` that donates a scheduling context pushes the donor's Reply object onto
that context's stack.  Since `v0.35.4` the stack is **doubly linked**, exactly as
seL4's (`replyPrev` / `replyNext`, `src/object/reply.c`): a frame records the
frame below it (`prev`) and the frame above it — or, on the head frame alone, the
context whose stack it heads (`next : Option ReplyStackLink`, `.frame` / `.head`)
— and the context records the top of the stack (`SchedContext.scReply`).  The
context is therefore recorded **at the head only**, which is what makes taking a
frame out of the *middle* of a stack an `O(1)` operation on three objects
(`detachReplyFrameAbove`) rather than a walk clearing a per-frame context field
on every frame below the cut — the walk this kernel's first design refused to
pay for, and then paid for by leaving frames dead on the stack forever.

The walk and the frame both read the object store through **`replyStackLinks?`**
and **`schedContextStackHead?`** rather than through a raw lookup — the walk
through `replyStackLinksAt?`, which is the first of them applied to a state and a
reply id, so the two are one projection and not two.  That is not a convenience.
It makes the chain's data dependence *structural*: a step that leaves those
projections alone frames the whole predicate through
`donationChainWellFormed_of_frame` with no case analysis on what else it wrote,
and a field the chain starts reading has to enter a projection before any frame
can be re-proved — where a frame stated over hand-listed fields would simply
stop mentioning it and keep passing.

**The relation is stated downward.**  Every `prev` link is answered by the frame
it names (`prevLinkReciprocal`: that frame's `next` is `.frame` of the one
above), and every head is answered by its context (`headLinkReciprocal` /
`headLinkResolves`).  The converse — every upward `.frame` link answered by a
`prev` — is deliberately **not** required: a frame the detach cut off keeps an
upward link naming a Reply that has since been consumed (`Reply.consumed`), and
nothing reads an upward link without checking the answer.  Every walk and every
pop validator follows `prev` and validates the target's `next`, so a stale upward
link in a cut-off part is never trusted and never reached from a head. -/

/-- WS-OD OD2.4 / `v0.35.4`: the reply-stack data an object carries **as a
Reply** — the link down to the frame below it and the link up to the frame above
it (or to the context it heads).

`none` for every object that is not a Reply, and for an absent key, so an
equality of this projection at a key says both *the same kind is there* and *it
carries the same links*.  Everything the chain walk reads of a Reply is here;
`caller`, `replyId` and `lock` are deliberately absent, because a link is
validated by the target's own upward link and never by who is blocked on it. -/
def replyStackLinks? :
    Option KernelObject → Option (Option SeLe4n.ReplyId × Option ReplyStackLink)
  | some (.reply r) => some (r.prev, r.next)
  | _ => none

/-- WS-OD OD2.4: the reply-stack data an object carries **as a SchedContext** —
the head of its stack.  `none` for every other object and for an absent key. -/
def schedContextStackHead? : Option KernelObject → Option (Option SeLe4n.ReplyId)
  | some (.schedContext sc) => some sc.scReply
  | _ => none

/-- The reply-stack links at a reply id of a state — `replyStackLinks?` applied
to the state's own lookup, so the walk and the frame read one projection. -/
def replyStackLinksAt? (st : SystemState) (rid : SeLe4n.ReplyId) :
    Option (Option SeLe4n.ReplyId × Option ReplyStackLink) :=
  replyStackLinks? (st.getObject? rid.toObjId)

@[simp] theorem replyStackLinks?_reply (r : Reply) :
    replyStackLinks? (some (.reply r)) = some (r.prev, r.next) := rfl
@[simp] theorem replyStackLinks?_none : replyStackLinks? none = none := rfl
@[simp] theorem replyStackLinks?_tcb (t : TCB) :
    replyStackLinks? (some (.tcb t)) = none := rfl
@[simp] theorem replyStackLinks?_schedContext (sc : SchedContext) :
    replyStackLinks? (some (.schedContext sc)) = none := rfl
@[simp] theorem schedContextStackHead?_schedContext (sc : SchedContext) :
    schedContextStackHead? (some (.schedContext sc)) = some sc.scReply := rfl
@[simp] theorem schedContextStackHead?_none : schedContextStackHead? none = none := rfl
@[simp] theorem schedContextStackHead?_tcb (t : TCB) :
    schedContextStackHead? (some (.tcb t)) = none := rfl
@[simp] theorem schedContextStackHead?_reply (r : Reply) :
    schedContextStackHead? (some (.reply r)) = none := rfl

/-- A `some` reading of the Reply projection is exactly a Reply with those links. -/
theorem replyStackLinks?_eq_some_iff {o : Option KernelObject}
    {below : Option SeLe4n.ReplyId} {up : Option ReplyStackLink} :
    replyStackLinks? o = some (below, up) ↔
      ∃ r : Reply, o = some (.reply r) ∧ r.prev = below ∧ r.next = up := by
  constructor
  · intro h
    cases o with
    | none => cases h
    | some obj =>
      cases obj with
      | reply r =>
        have hPair := Option.some.inj h
        exact ⟨r, rfl, congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
      | _ => cases h
  · rintro ⟨r, rfl, rfl, rfl⟩; rfl

/-- A `some` reading of the SchedContext projection is exactly a SchedContext with
that head. -/
theorem schedContextStackHead?_eq_some_iff {o : Option KernelObject}
    {head : Option SeLe4n.ReplyId} :
    schedContextStackHead? o = some head ↔
      ∃ sc : SchedContext, o = some (.schedContext sc) ∧ sc.scReply = head := by
  constructor
  · intro h
    cases o with
    | none => cases h
    | some obj =>
      cases obj with
      | schedContext sc => exact ⟨sc, rfl, Option.some.inj h⟩
      | _ => cases h
  · rintro ⟨sc, rfl, rfl⟩; rfl

/-- WS-OD OD2.4 / `v0.35.4`: **the reply-stack walk**, generalised over the link
each frame is expected to carry upward.

`donationChainWalk st expect fuel rid?` is `some chain` when the `prev`-walk from
`rid?` reaches the bottom of the stack (`none`) in at most `fuel` steps, with
every reply on the way resolving in `st` and **answering the link it was reached
by**: the first frame's `next` must be `expect` — `.head scId` when the walk
starts at a context's head — and every later frame's `next` must be `.frame` of
the frame it was reached from.  It is `none` when the walk runs out of fuel,
meets a `ReplyId` that resolves to no Reply, or meets one whose upward link does
not answer.

Three decisions, each a decision rather than a default.

* **Fuel, not well-founded recursion.**  The `prev` graph is exactly what the
  invariant is *about*, so a definition that presupposed its acyclicity in order
  to terminate would be circular.  Fuel makes the walk total on any store, and
  "this stack terminates" becomes the ∃-statement `donationChainWellFormed`
  carries rather than a side condition of the definition.  It also means the
  fuel is not a budget on call depth: the invariant asks for *some* fuel, so a
  deeper chain is admitted with a larger one, and nothing here caps how far a
  Call chain may nest.
* **A link is validated by the target's own upward link, never by its
  `caller`.**  Reply objects are re-linked to new callers
  (`replyIdEstablishFresh`), so a stale `prev` naming a *reused* Reply would let
  a donation return read the new caller and hand the original thread's
  scheduling context to an unrelated thread, in another domain, driven by object
  reuse.  The reciprocity test is what refuses that: a re-linked Reply carries
  no link back to the frame above, so the walk stops at it rather than walking
  through it.
* **The chain is returned, not merely accepted.**  The list is what makes
  `donationChainFrom_mem` available, and with it the freshness fact the push
  needs — a Reply carrying no upward link is on no chain. -/
def donationChainWalk (st : SystemState) :
    ReplyStackLink → Nat → Option SeLe4n.ReplyId → Option (List SeLe4n.ReplyId)
  | _, _, none => some []
  | _, 0, some _ => none
  | expect, fuel + 1, some rid =>
    match replyStackLinksAt? st rid with
    | some (below, up) =>
      if up = some expect then
        (donationChainWalk st (.frame rid) fuel below).map (rid :: ·)
      else none
    | none => none

/-- The walk of a context's stack from its head: the first frame must head this
context, every later frame must answer the frame above it. -/
def donationChainFrom (st : SystemState) (scId : SeLe4n.SchedContextId)
    (fuel : Nat) (rid? : Option SeLe4n.ReplyId) : Option (List SeLe4n.ReplyId) :=
  donationChainWalk st (.head scId) fuel rid?

@[simp] theorem donationChainWalk_bottom
    (st : SystemState) (expect : ReplyStackLink) (fuel : Nat) :
    donationChainWalk st expect fuel none = some [] := by
  cases fuel <;> rfl

@[simp] theorem donationChainWalk_zero
    (st : SystemState) (expect : ReplyStackLink) (rid : SeLe4n.ReplyId) :
    donationChainWalk st expect 0 (some rid) = none := rfl

theorem donationChainWalk_succ
    (st : SystemState) (expect : ReplyStackLink) (fuel : Nat) (rid : SeLe4n.ReplyId) :
    donationChainWalk st expect (fuel + 1) (some rid) =
      match replyStackLinksAt? st rid with
      | some (below, up) =>
        if up = some expect then
          (donationChainWalk st (.frame rid) fuel below).map (rid :: ·)
        else none
      | none => none := rfl

@[simp] theorem donationChainFrom_bottom
    (st : SystemState) (scId : SeLe4n.SchedContextId) (fuel : Nat) :
    donationChainFrom st scId fuel none = some [] := by
  unfold donationChainFrom; simp

@[simp] theorem donationChainFrom_zero
    (st : SystemState) (scId : SeLe4n.SchedContextId) (rid : SeLe4n.ReplyId) :
    donationChainFrom st scId 0 (some rid) = none := rfl

theorem donationChainFrom_succ
    (st : SystemState) (scId : SeLe4n.SchedContextId) (fuel : Nat) (rid : SeLe4n.ReplyId) :
    donationChainFrom st scId (fuel + 1) (some rid) =
      match replyStackLinksAt? st rid with
      | some (below, up) =>
        if up = some (.head scId) then
          (donationChainWalk st (.frame rid) fuel below).map (rid :: ·)
        else none
      | none => none := rfl

/-- The walk's first step, unfolded: what a `some` result at `fuel + 1` says
about the frame it started from. -/
theorem donationChainWalk_succ_some
    {st : SystemState} {expect : ReplyStackLink} {fuel : Nat} {rid : SeLe4n.ReplyId}
    {chain : List SeLe4n.ReplyId}
    (h : donationChainWalk st expect (fuel + 1) (some rid) = some chain) :
    ∃ (r : Reply) (tail : List SeLe4n.ReplyId),
      st.objects[rid.toObjId]? = some (.reply r) ∧ r.next = some expect ∧
      donationChainWalk st (.frame rid) fuel r.prev = some tail ∧ chain = rid :: tail := by
  rw [donationChainWalk_succ] at h
  revert h
  cases hLinks : replyStackLinksAt? st rid with
  | none => intro h; cases h
  | some pair =>
    obtain ⟨below, up⟩ := pair
    simp only []
    by_cases hUp : up = some expect
    · rw [if_pos hUp]
      intro h
      obtain ⟨r, hR, hPrev, hNext⟩ := replyStackLinks?_eq_some_iff.mp hLinks
      cases hRec : donationChainWalk st (.frame rid) fuel below with
      | none => rw [hRec] at h; cases h
      | some tail =>
        rw [hRec] at h
        simp only [Option.map_some] at h
        refine ⟨r, tail, hR, by rw [hNext, hUp], ?_, (Option.some.inj h).symm⟩
        rw [hPrev]; exact hRec
    · rw [if_neg hUp]; intro h; cases h

/-- More fuel never changes a successful walk. -/
theorem donationChainWalk_mono (st : SystemState) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain →
      donationChainWalk st expect (fuel + 1) rid? = some chain := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h
    cases rid? with
    | none => simp at h ⊢; exact h
    | some rid => cases h
  | succ n ih =>
    intro expect rid? chain h
    cases rid? with
    | none => simp at h ⊢; exact h
    | some rid =>
      obtain ⟨r, tail, hR, hNext, hRec, rfl⟩ := donationChainWalk_succ_some h
      rw [donationChainWalk_succ]
      have hLinks : replyStackLinksAt? st rid = some (r.prev, r.next) := by
        unfold replyStackLinksAt? SystemState.getObject?; rw [hR]; rfl
      rw [hLinks]
      simp only []
      rw [if_pos hNext, ih (.frame rid) r.prev tail hRec]
      rfl

theorem donationChainWalk_mono_le (st : SystemState)
    {fuel : Nat} {expect : ReplyStackLink} {rid? : Option SeLe4n.ReplyId}
    {chain : List SeLe4n.ReplyId}
    (h : donationChainWalk st expect fuel rid? = some chain) :
    ∀ fuel', fuel ≤ fuel' → donationChainWalk st expect fuel' rid? = some chain := by
  intro fuel' hLe
  induction fuel' with
  | zero =>
    have hZero : fuel = 0 := Nat.le_zero.mp hLe
    subst hZero; exact h
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hLe with hEq | hLt
    · subst hEq; exact h
    · exact donationChainWalk_mono st m expect rid? chain (ih (Nat.lt_succ_iff.mp hLt))

theorem donationChainFrom_mono (st : SystemState) (scId : SeLe4n.SchedContextId) :
    ∀ (fuel : Nat) (rid? : Option SeLe4n.ReplyId) (chain : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel rid? = some chain →
      donationChainFrom st scId (fuel + 1) rid? = some chain :=
  fun fuel rid? chain h => donationChainWalk_mono st fuel (.head scId) rid? chain h

theorem donationChainFrom_mono_le (st : SystemState) (scId : SeLe4n.SchedContextId)
    {fuel : Nat} {rid? : Option SeLe4n.ReplyId} {chain : List SeLe4n.ReplyId}
    (h : donationChainFrom st scId fuel rid? = some chain) :
    ∀ fuel', fuel ≤ fuel' → donationChainFrom st scId fuel' rid? = some chain :=
  donationChainWalk_mono_le st h

/-- Every member of a walk resolves to a Reply carrying an upward link. -/
theorem donationChainWalk_mem (st : SystemState) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain →
      ∀ rid ∈ chain, ∃ r : Reply,
        st.objects[rid.toObjId]? = some (.reply r) ∧ r.next.isSome := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h rid hMem
    cases rid? with
    | none => simp at h; subst h; cases hMem
    | some _ => cases h
  | succ n ih =>
    intro expect rid? chain h rid hMem
    cases rid? with
    | none => simp at h; subst h; cases hMem
    | some rid0 =>
      obtain ⟨r, tail, hR, hNext, hRec, rfl⟩ := donationChainWalk_succ_some h
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact ⟨r, hR, by rw [hNext]; rfl⟩
      · exact ih (.frame rid0) r.prev tail hRec rid hTail

/-- Each member of a walk **answers the link it was reached by**: the first the
expected link, every later one `.frame` of an earlier member.  This is what puts
a frame on at most one stack — a Reply heading `scId` answers no link on another
context's walk, and a frame answering `rid` is on no walk `rid` is not on. -/
theorem donationChainWalk_mem_next (st : SystemState) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain →
      ∀ rid ∈ chain, ∃ r : Reply,
        st.objects[rid.toObjId]? = some (.reply r) ∧
        (r.next = some expect ∨ ∃ p ∈ chain, r.next = some (.frame p)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h rid hMem
    cases rid? with
    | none => simp at h; subst h; cases hMem
    | some _ => cases h
  | succ n ih =>
    intro expect rid? chain h rid hMem
    cases rid? with
    | none => simp at h; subst h; cases hMem
    | some rid0 =>
      obtain ⟨r0, tail, hR0, hNext0, hRec, rfl⟩ := donationChainWalk_succ_some h
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact ⟨r0, hR0, Or.inl hNext0⟩
      · obtain ⟨r, hR, hOr⟩ := ih (.frame rid0) r0.prev tail hRec rid hTail
        refine ⟨r, hR, ?_⟩
        rcases hOr with hEq | ⟨p, hp, hEq⟩
        · exact Or.inr ⟨rid0, List.mem_cons_self, hEq⟩
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hEq⟩

/-- Each member of a walk is either the frame the walk started from or the `prev`
of an earlier member — the downward reading of `donationChainWalk_mem_next`, and
what puts a frame no `prev` names on no chain but its own context's head. -/
theorem donationChainWalk_mem_prev (st : SystemState) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain →
      ∀ rid ∈ chain, rid? = some rid ∨
        ∃ (p : SeLe4n.ReplyId) (rp : Reply), p ∈ chain ∧
          st.objects[p.toObjId]? = some (.reply rp) ∧ rp.prev = some rid := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h rid hMem
    cases rid? with
    | none => simp at h; subst h; cases hMem
    | some _ => cases h
  | succ n ih =>
    intro expect rid? chain h rid hMem
    cases rid? with
    | none => simp at h; subst h; cases hMem
    | some rid0 =>
      obtain ⟨r0, tail, hR0, _, hRec, rfl⟩ := donationChainWalk_succ_some h
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact Or.inl rfl
      · rcases ih (.frame rid0) r0.prev tail hRec rid hTail with hEq | ⟨p, rp, hp, hRp, hPrev⟩
        · exact Or.inr ⟨rid0, r0, List.mem_cons_self, hR0, hEq⟩
        · exact Or.inr ⟨p, rp, List.mem_cons_of_mem _ hp, hRp, hPrev⟩

/-- **A walk survives clearing one member's `prev`.**  If the post-state agrees
with the pre-state on every member's links, except that some members have had
their `prev` cleared with `next` kept, the post-state walk exists: it follows the
same frames and stops at the first cleared one.  This is what the cancellation's
`O(1)` detach costs the chain invariant — a shorter stack, never a broken one. -/
theorem donationChainWalk_exists_of_agree_or_cut {st st' : SystemState} :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain →
      (∀ q ∈ chain, replyStackLinksAt? st' q = replyStackLinksAt? st q ∨
        ∃ (rq rq' : Reply), st.objects[q.toObjId]? = some (.reply rq) ∧
          st'.objects[q.toObjId]? = some (.reply rq') ∧ rq'.prev = none ∧ rq'.next = rq.next) →
      ∃ chain', donationChainWalk st' expect fuel rid? = some chain' := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h _
    cases rid? with
    | none => exact ⟨[], by simp⟩
    | some _ => cases h
  | succ n ih =>
    intro expect rid? chain h hAgree
    cases rid? with
    | none => exact ⟨[], by simp⟩
    | some rid0 =>
      obtain ⟨r0, tail, hR0, hNext0, hRec, rfl⟩ := donationChainWalk_succ_some h
      rcases hAgree rid0 List.mem_cons_self with hEq | ⟨rq, rq', hRq, hRq', hPrev', hNext'⟩
      · obtain ⟨tail', hTail'⟩ := ih (.frame rid0) r0.prev tail hRec
          (fun q hq => hAgree q (List.mem_cons_of_mem _ hq))
        refine ⟨rid0 :: tail', ?_⟩
        rw [donationChainWalk_succ]
        have hLinks : replyStackLinksAt? st' rid0 = some (r0.prev, r0.next) := by
          rw [hEq]; unfold replyStackLinksAt? SystemState.getObject?; rw [hR0]; rfl
        rw [hLinks]
        simp [hNext0, hTail']
      · have hrq : rq = r0 := KernelObject.reply.inj (Option.some.inj (hRq.symm.trans hR0))
        refine ⟨[rid0], ?_⟩
        rw [donationChainWalk_succ]
        have hLinks : replyStackLinksAt? st' rid0 = some (none, r0.next) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hRq']; simp [hPrev', hNext', hrq]
        rw [hLinks]
        simp [hNext0]

theorem donationChainFrom_mem (st : SystemState) (scId : SeLe4n.SchedContextId) :
    ∀ (fuel : Nat) (rid? : Option SeLe4n.ReplyId) (chain : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel rid? = some chain →
      ∀ rid ∈ chain, ∃ r : Reply,
        st.objects[rid.toObjId]? = some (.reply r) ∧ r.next.isSome :=
  fun fuel rid? chain h => donationChainWalk_mem st fuel (.head scId) rid? chain h

/-- **Freshness**: a Reply carrying no upward link is on no chain — the fact the
push consumes about the frame it is about to push (`donationPushFrame?` admits
only a frame with both links clear). -/
theorem not_mem_donationChainFrom_of_unlinked
    {st : SystemState} {scId : SeLe4n.SchedContextId} {fuel : Nat}
    {rid? : Option SeLe4n.ReplyId} {chain : List SeLe4n.ReplyId}
    (hChain : donationChainFrom st scId fuel rid? = some chain)
    {rid : SeLe4n.ReplyId} {r : Reply}
    (hR : st.objects[rid.toObjId]? = some (.reply r))
    (hNext : r.next = none) :
    rid ∉ chain := by
  intro hMem
  obtain ⟨r', hR', hSome⟩ := donationChainFrom_mem st scId fuel rid? chain hChain rid hMem
  rw [hR] at hR'
  have hEq : r = r' := KernelObject.reply.inj (Option.some.inj hR')
  subst hEq
  rw [hNext] at hSome; cases hSome

/-- Two states agreeing on the Reply projection at every key walk identically. -/
theorem donationChainWalk_congr {st st' : SystemState}
    (hLinks : ∀ oid : SeLe4n.ObjId,
      replyStackLinks? st'.objects[oid]? = replyStackLinks? st.objects[oid]?) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId),
      donationChainWalk st' expect fuel rid? = donationChainWalk st expect fuel rid? := by
  intro fuel
  induction fuel with
  | zero => intro expect rid?; cases rid? <;> rfl
  | succ n ih =>
    intro expect rid?
    cases rid? with
    | none => rfl
    | some rid =>
      rw [donationChainWalk_succ, donationChainWalk_succ]
      have hAt : replyStackLinksAt? st' rid = replyStackLinksAt? st rid := hLinks rid.toObjId
      rw [hAt]
      cases replyStackLinksAt? st rid with
      | none => rfl
      | some pair =>
        obtain ⟨below, up⟩ := pair
        simp only []
        rw [ih (.frame rid) below]

theorem donationChainFrom_congr {st st' : SystemState} (scId : SeLe4n.SchedContextId)
    (hLinks : ∀ oid : SeLe4n.ObjId,
      replyStackLinks? st'.objects[oid]? = replyStackLinks? st.objects[oid]?) :
    ∀ (fuel : Nat) (rid? : Option SeLe4n.ReplyId),
      donationChainFrom st' scId fuel rid? = donationChainFrom st scId fuel rid? :=
  fun fuel rid? => donationChainWalk_congr hLinks fuel (.head scId) rid?

theorem donationChainWalk_length_le (st : SystemState) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain → chain.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h
    cases rid? with
    | none => simp at h; subst h; exact Nat.le_refl 0
    | some _ => cases h
  | succ n ih =>
    intro expect rid? chain h
    cases rid? with
    | none => simp at h; subst h; exact Nat.zero_le _
    | some rid =>
      obtain ⟨r, tail, _, _, hRec, rfl⟩ := donationChainWalk_succ_some h
      exact Nat.succ_le_succ (ih (.frame rid) r.prev tail hRec)

theorem donationChainFrom_length_le (st : SystemState) (scId : SeLe4n.SchedContextId) :
    ∀ (fuel : Nat) (rid? : Option SeLe4n.ReplyId) (chain : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel rid? = some chain → chain.length ≤ fuel :=
  fun fuel rid? chain h => donationChainWalk_length_le st fuel (.head scId) rid? chain h

/-- **A walk from a frame is a function of the frame alone**: whatever link it
was expected to answer and whatever fuel sufficed, two successful walks from the
same frame return the same chain.  The first step pins the expected link (the
frame's `next` answers exactly one), and every later step is the same recursion. -/
theorem donationChainWalk_deterministic (st : SystemState) :
    ∀ (f₁ : Nat) (e₁ e₂ : ReplyStackLink) (f₂ : Nat) (rid? : Option SeLe4n.ReplyId)
      (c₁ c₂ : List SeLe4n.ReplyId),
      donationChainWalk st e₁ f₁ rid? = some c₁ →
      donationChainWalk st e₂ f₂ rid? = some c₂ → c₁ = c₂ := by
  intro f₁
  induction f₁ with
  | zero =>
    intro e₁ e₂ f₂ rid? c₁ c₂ h₁ h₂
    cases rid? with
    | none => simp at h₁ h₂; subst h₁; subst h₂; rfl
    | some _ => cases h₁
  | succ n ih =>
    intro e₁ e₂ f₂ rid? c₁ c₂ h₁ h₂
    cases rid? with
    | none => simp at h₁ h₂; subst h₁; subst h₂; rfl
    | some rid =>
      cases f₂ with
      | zero => cases h₂
      | succ m =>
        obtain ⟨r, t₁, hR, _, hRec₁, rfl⟩ := donationChainWalk_succ_some h₁
        obtain ⟨r', t₂, hR', _, hRec₂, rfl⟩ := donationChainWalk_succ_some h₂
        rw [hR] at hR'
        have hEq : r = r' := KernelObject.reply.inj (Option.some.inj hR')
        subst hEq
        rw [ih (.frame rid) (.frame rid) m r.prev t₁ t₂ hRec₁ hRec₂]

theorem donationChainFrom_deterministic (st : SystemState) (scId : SeLe4n.SchedContextId)
    {f₁ f₂ : Nat} {rid? : Option SeLe4n.ReplyId} {c₁ c₂ : List SeLe4n.ReplyId}
    (h₁ : donationChainFrom st scId f₁ rid? = some c₁)
    (h₂ : donationChainFrom st scId f₂ rid? = some c₂) :
    c₁ = c₂ :=
  donationChainWalk_deterministic st f₁ (.head scId) (.head scId) f₂ rid? c₁ c₂ h₁ h₂

/-- Every suffix of a walk beginning at a member is itself a walk from that
member — for some expected link and no more fuel. -/
theorem donationChainWalk_suffix_walk (st : SystemState) :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (pre : List SeLe4n.ReplyId) (rid : SeLe4n.ReplyId) (rest : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some (pre ++ rid :: rest) →
      ∃ (f : Nat) (e : ReplyStackLink), f ≤ fuel ∧
        donationChainWalk st e f (some rid) = some (rid :: rest) := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? pre rid rest h
    cases rid? with
    | none => simp at h
    | some _ => cases h
  | succ n ih =>
    intro expect rid? pre rid rest h
    cases rid? with
    | none => simp at h
    | some rid0 =>
      obtain ⟨r, tail, hR, hNext, hRec, hEq⟩ := donationChainWalk_succ_some h
      cases pre with
      | nil =>
        simp only [List.nil_append] at hEq
        obtain ⟨hRid, hTail⟩ := List.cons.inj hEq
        subst hRid; subst hTail
        exact ⟨n + 1, expect, Nat.le_refl _, h⟩
      | cons p ps =>
        simp only [List.cons_append] at hEq
        have hTail := (List.cons.inj hEq).2
        subst hTail
        obtain ⟨f, e, hLe, hWalk⟩ := ih (.frame rid0) r.prev ps rid rest hRec
        exact ⟨f, e, Nat.le_succ_of_le hLe, hWalk⟩

theorem donationChainFrom_suffix_walk (st : SystemState) (scId : SeLe4n.SchedContextId) :
    ∀ (fuel : Nat) (rid? : Option SeLe4n.ReplyId) (pre : List SeLe4n.ReplyId)
      (rid : SeLe4n.ReplyId) (rest : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel rid? = some (pre ++ rid :: rest) →
      ∃ (f : Nat) (e : ReplyStackLink), f ≤ fuel ∧
        donationChainWalk st e f (some rid) = some (rid :: rest) :=
  fun fuel rid? pre rid rest h =>
    donationChainWalk_suffix_walk st fuel (.head scId) rid? pre rid rest h

/-- **Acyclicity is derived, not assumed.**  A frame never appears again below
itself: the walk from its second occurrence would return a proper suffix of the
walk from the first, and a walk from a frame is a function of the frame alone. -/
theorem donationChainWalk_head_not_mem_tail (st : SystemState)
    {fuel : Nat} {expect : ReplyStackLink} {rid : SeLe4n.ReplyId}
    {rest : List SeLe4n.ReplyId}
    (h : donationChainWalk st expect fuel (some rid) = some (rid :: rest)) :
    rid ∉ rest := by
  intro hMem
  obtain ⟨pre, post, hSplit⟩ := List.append_of_mem hMem
  have hFull : donationChainWalk st expect fuel (some rid)
      = some ((rid :: pre) ++ rid :: post) := by
    rw [h, hSplit]; rfl
  obtain ⟨f, e, _, hSuffix⟩ :=
    donationChainWalk_suffix_walk st fuel expect (some rid) (rid :: pre) rid post hFull
  have hEqChains : rid :: rest = rid :: post :=
    donationChainWalk_deterministic st fuel expect e f (some rid) _ _ h hSuffix
  have hRest : rest = post := (List.cons.inj hEqChains).2
  rw [hSplit] at hRest
  have hLen : (pre ++ rid :: post).length = post.length := congrArg List.length hRest
  simp only [List.length_append, List.length_cons] at hLen
  omega

theorem donationChainFrom_head_not_mem_tail (st : SystemState)
    (scId : SeLe4n.SchedContextId) {fuel : Nat} {rid : SeLe4n.ReplyId}
    {rest : List SeLe4n.ReplyId}
    (h : donationChainFrom st scId fuel (some rid) = some (rid :: rest)) :
    rid ∉ rest :=
  donationChainWalk_head_not_mem_tail st h

/-- **The walk reads only its own members.**  Two states that agree on the Reply
projection at every member of a chain walk it identically from the same start —
the congruence a step that rewrites keys *off* the chain needs, where
`donationChainWalk_congr` (agreement at every key) is false of it. -/
theorem donationChainWalk_congr_on_chain {st st' : SystemState} :
    ∀ (fuel : Nat) (expect : ReplyStackLink) (rid? : Option SeLe4n.ReplyId)
      (chain : List SeLe4n.ReplyId),
      donationChainWalk st expect fuel rid? = some chain →
      (∀ rid ∈ chain, replyStackLinksAt? st' rid = replyStackLinksAt? st rid) →
      donationChainWalk st' expect fuel rid? = some chain := by
  intro fuel
  induction fuel with
  | zero =>
    intro expect rid? chain h _
    cases rid? with
    | none => simpa using h
    | some _ => cases h
  | succ n ih =>
    intro expect rid? chain h hAgree
    cases rid? with
    | none => simpa using h
    | some rid =>
      obtain ⟨r, tail, hR, hNext, hRec, rfl⟩ := donationChainWalk_succ_some h
      rw [donationChainWalk_succ]
      have hLinks : replyStackLinksAt? st rid = some (r.prev, r.next) := by
        unfold replyStackLinksAt? SystemState.getObject?; rw [hR]; rfl
      rw [hAgree rid List.mem_cons_self, hLinks]
      simp only []
      rw [if_pos hNext,
        ih (.frame rid) r.prev tail hRec (fun x hx => hAgree x (List.mem_cons_of_mem _ hx))]
      rfl

theorem donationChainFrom_congr_on_chain {st st' : SystemState}
    (scId : SeLe4n.SchedContextId) :
    ∀ (fuel : Nat) (rid? : Option SeLe4n.ReplyId) (chain : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel rid? = some chain →
      (∀ rid ∈ chain, replyStackLinksAt? st' rid = replyStackLinksAt? st rid) →
      donationChainFrom st' scId fuel rid? = some chain :=
  fun fuel rid? chain h hAgree =>
    donationChainWalk_congr_on_chain fuel (.head scId) rid? chain h hAgree

/-- WS-OD OD2.4 / `v0.35.4`: **the SchedContext donation chain is well formed.**

Five fields, each a *relation* rather than the presence of a link, and each the
answer to one question a reader of the stack asks.

* `replyWellFormed` — every stored Reply satisfies `Reply.wellFormed`: a Reply
  whose caller is gone carries no stack link.  This is what makes `Reply.isFree`
  the exact test for "may be linked or retyped", and what rules a consumed frame
  out from below a head: a frame the pop reaches always has a blocked caller to
  hand the context back to.
* `headLinkReciprocal` — a context's head (`scReply = some rid`) resolves to a
  Reply that **heads this context** (`next = some (.head scId)`).  This is the
  fact `donationHeadOf?` validates, so the pop's head validation succeeds on
  every well-formed state (`donationHeadResolves_of_chainWellFormed`).
* `headLinkResolves` — the converse for heads: a Reply that says it heads a
  context names a context that exists and whose head it is.  Without it a stale
  `.head` link could survive a context's retype and be reused by the next
  context at that id.
* `prevLinkReciprocal` — every `prev` link is answered: the frame below resolves
  and links back up to the frame above (`next = some (.frame rid)`).  This is the
  fact the walk and `replyStackOuterCaller?` validate at every step, and the
  reason a stale `prev` over a reused Reply cannot redirect a context
  (plan §3.4).
* `headTerminates` — each context's stack, walked from its head, terminates:
  some fuel suffices.  With reciprocity in place the walk never fails a
  validation, so this clause is acyclicity — in principle derivable from
  `donationChainWalk_head_not_mem_tail` and the finiteness of the store, stated
  outright so every consumer has a walk to read the chain off.

**What is deliberately absent**: any converse for upward `.frame` links (a
cut-off part keeps stale ones, see the section docstring) and any completeness
clause over a per-frame context field — a frame below the head does not know its
context, which is exactly what makes the detach `O(1)`.

**Not a conjunct of `ipcInvariantFull`.**  That bundle has exactly twenty
conjuncts and a family of theorems whose size a Tier-0 gate holds equal to the
prose that quotes it; widening it is a change of a different size.  This
predicate joins `ipcReachable` and the two dispatch quiescence packs instead —
where, per the same discipline, it is *preserved* rather than assumed: the frame
family below is what every transition discharges it through. -/
structure donationChainWellFormed (st : SystemState) : Prop where
  /-- Every stored Reply is locally well formed: no stack link on a Reply whose
  caller is gone. -/
  replyWellFormed : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
    st.objects[rid.toObjId]? = some (.reply r) → r.wellFormed
  /-- A context's head resolves to a Reply heading that context. -/
  headLinkReciprocal : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∀ rid : SeLe4n.ReplyId, sc.scReply = some rid →
      ∃ r : Reply, st.objects[rid.toObjId]? = some (.reply r) ∧ r.next = some (.head scId)
  /-- A Reply heading a context is that context's head. -/
  headLinkResolves : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (scId : SeLe4n.SchedContextId),
    st.objects[rid.toObjId]? = some (.reply r) → r.next = some (.head scId) →
    ∃ sc : SchedContext, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      sc.scReply = some rid
  /-- Every `prev` link is answered by the frame it names. -/
  prevLinkReciprocal : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (below : SeLe4n.ReplyId),
    st.objects[rid.toObjId]? = some (.reply r) → r.prev = some below →
    ∃ b : Reply, st.objects[below.toObjId]? = some (.reply b) ∧ b.next = some (.frame rid)
  /-- Each context's stack, walked from its head, terminates. -/
  headTerminates : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∃ (fuel : Nat) (chain : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel sc.scReply = some chain

/-- **WS-RM (`v0.35.6`): the chain invariant with `Reply.wellFormed` relaxed at one
key** — the honest statement about the state a reply leg leaves when the frame it
answered is a stack **head**.

A head keeps its links when its caller is consumed, deliberately: the donation pop
that removes it runs in the same transition right after the reply leg and
validates the head by that very link (WS-OD plan §3.3).  So between the two the
frame at `rid` has `caller = none` and a live `.head` link, which
`Reply.wellFormed` forbids — and **only** that: the context still names the frame
and the frame still names the context, no `prev` names it (its `next` is a
`.head`, so `prevLinkReciprocal` in the pre-state admits none), and every walk is
over links nothing moved.

It stands to the reply leg as `ipcInvariantFullExceptDonationOwner` stands to the
bare reply: the composite that discharges it is where the pop runs
(`endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed`), and
`donationChainWellFormed_of_except` is the upgrade. -/
structure donationChainWellFormedExcept (st : SystemState) (rid : SeLe4n.ReplyId) : Prop where
  /-- Every stored Reply **other than `rid`** is locally well formed. -/
  replyWellFormedExcept : ∀ (q : SeLe4n.ReplyId) (r : Reply), q ≠ rid →
    st.objects[q.toObjId]? = some (.reply r) → r.wellFormed
  /-- A context's head resolves to a Reply heading that context. -/
  headLinkReciprocal : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∀ q : SeLe4n.ReplyId, sc.scReply = some q →
      ∃ r : Reply, st.objects[q.toObjId]? = some (.reply r) ∧ r.next = some (.head scId)
  /-- A Reply heading a context is that context's head. -/
  headLinkResolves : ∀ (q : SeLe4n.ReplyId) (r : Reply) (scId : SeLe4n.SchedContextId),
    st.objects[q.toObjId]? = some (.reply r) → r.next = some (.head scId) →
    ∃ sc : SchedContext, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      sc.scReply = some q
  /-- Every `prev` link is answered by the frame it names. -/
  prevLinkReciprocal : ∀ (q : SeLe4n.ReplyId) (r : Reply) (below : SeLe4n.ReplyId),
    st.objects[q.toObjId]? = some (.reply r) → r.prev = some below →
    ∃ b : Reply, st.objects[below.toObjId]? = some (.reply b) ∧ b.next = some (.frame q)
  /-- Each context's stack, walked from its head, terminates. -/
  headTerminates : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∃ (fuel : Nat) (chain : List SeLe4n.ReplyId),
      donationChainFrom st scId fuel sc.scReply = some chain

/-- The whole invariant is the relaxed one plus well-formedness at the one key it
relaxes — so a composite that later removes that frame discharges the transient
by supplying exactly that fact. -/
theorem donationChainWellFormed_of_except {st : SystemState} {rid : SeLe4n.ReplyId}
    (h : donationChainWellFormedExcept st rid)
    (hAt : ∀ r : Reply, st.objects[rid.toObjId]? = some (.reply r) → r.wellFormed) :
    donationChainWellFormed st where
  replyWellFormed := by
    intro q r hq
    by_cases hEq : q = rid
    · subst hEq; exact hAt r hq
    · exact h.replyWellFormedExcept q r hEq hq
  headLinkReciprocal := h.headLinkReciprocal
  headLinkResolves := h.headLinkResolves
  prevLinkReciprocal := h.prevLinkReciprocal
  headTerminates := h.headTerminates

/-- The relaxed form is weaker, at any key. -/
theorem donationChainWellFormedExcept_of_wellFormed {st : SystemState}
    (h : donationChainWellFormed st) (rid : SeLe4n.ReplyId) :
    donationChainWellFormedExcept st rid where
  replyWellFormedExcept := fun q r _ hq => h.replyWellFormed q r hq
  headLinkReciprocal := h.headLinkReciprocal
  headLinkResolves := h.headLinkResolves
  prevLinkReciprocal := h.prevLinkReciprocal
  headTerminates := h.headTerminates

/-- WS-OD OD3.2: **the pop's head validation succeeds.**

`returnDonatedSchedContext` refuses a scheduling context whose stack head does
not resolve to a Reply heading that very context — the fail-closed guard
`donationHeadOf?` applies.  This is the property that rules that arm out, named
so that a caller states the fact it has rather than the whole chain invariant,
and so that the two ways of establishing it (the invariant itself, or a frame
across a step that writes no chain object) are visible side by side. -/
def donationHeadResolves (st : SystemState) (scId : SeLe4n.SchedContextId) : Prop :=
  ∀ sc : SchedContext, st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∃ head?, donationHeadOf? st scId sc = .ok head? ∧
      ∀ (rid : SeLe4n.ReplyId) (r : Reply) (below : SeLe4n.ReplyId),
        head? = some (rid, r) → r.prev = some below →
        ∃ b : Reply, st.objects[below.toObjId]? = some (.reply b)

/-- The head validation, unfolded on a resolving head. -/
theorem donationHeadOf?_of_reciprocal (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (hHead : sc.scReply = some rid)
    (hR : st.objects[rid.toObjId]? = some (.reply r))
    (hNext : r.next = some (.head scId)) :
    donationHeadOf? st scId sc = .ok (some (rid, r)) := by
  unfold donationHeadOf?
  rw [hHead]
  have hGet : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hR
  simp only [hGet, hNext, bne_self_eq_false, Bool.false_eq_true, if_false]

/-- WS-OD OD3.2: the chain invariant establishes the pop's head validation —
`headLinkReciprocal` is exactly what `donationHeadOf?` checks. -/
theorem donationHeadResolves_of_chainWellFormed (st : SystemState)
    (scId : SeLe4n.SchedContextId) (hChain : donationChainWellFormed st) :
    donationHeadResolves st scId := by
  intro sc hSc
  cases hR : sc.scReply with
  | none => exact ⟨none, donationHeadOf?_of_no_stack st scId sc hR, fun _ _ _ h => by cases h⟩
  | some rid =>
    obtain ⟨r, hRObj, hNext⟩ := hChain.headLinkReciprocal scId sc hSc rid hR
    refine ⟨some (rid, r), donationHeadOf?_of_reciprocal st scId sc rid r hR hRObj hNext, ?_⟩
    intro rid' r' below hEq hPrev
    obtain ⟨hRid, hR'⟩ := Prod.mk.inj (Option.some.inj hEq)
    subst hRid; subst hR'
    obtain ⟨b, hB, _⟩ := hChain.prevLinkReciprocal rid r below hRObj hPrev
    exact ⟨b, hB⟩

/-- WS-OD OD3.4: **the outer-caller resolution succeeds** — the resolver walks one
frame past the head, so it needs the head to resolve, the frame below it to
answer its link, and that frame to still have a caller. -/
def replyStackOuterCallerResolves (st : SystemState) (scId : SeLe4n.SchedContextId) : Prop :=
  ∀ sc : SchedContext, st.objects[scId.toObjId]? = some (.schedContext sc) →
    ∃ outer?, replyStackOuterCaller? st scId = .ok outer?

/-- WS-OD OD3.4 / `v0.35.4`: the chain invariant establishes the outer-caller
resolution.  The head validation needs `headLinkReciprocal`; this needs one link
more — `prevLinkReciprocal` for the frame below the head — and `replyWellFormed`
for that frame's caller: a frame that answers a link is on a stack, and a Reply
on a stack has a caller, so the resolver never meets the consumed frame it
refuses. -/
theorem replyStackOuterCallerResolves_of_chainWellFormed (st : SystemState)
    (scId : SeLe4n.SchedContextId) (hChain : donationChainWellFormed st) :
    replyStackOuterCallerResolves st scId := by
  intro sc hSc
  have hGetSc : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  cases hR : sc.scReply with
  | none => exact ⟨none, replyStackOuterCaller?_of_no_stack st scId sc hGetSc hR⟩
  | some rid =>
    obtain ⟨r, hRObj, hNext⟩ := hChain.headLinkReciprocal scId sc hSc rid hR
    have hHead := donationHeadOf?_of_reciprocal st scId sc rid r hR hRObj hNext
    cases hPrev : r.prev with
    | none =>
      exact ⟨none, replyStackOuterCaller?_of_bottom_head st scId sc rid r hGetSc hHead hPrev⟩
    | some below =>
      obtain ⟨b, hBObj, hBNext⟩ := hChain.prevLinkReciprocal rid r below hRObj hPrev
      have hBGet : st.getReply? below = some b :=
        (SystemState.getReply?_eq_some_iff _ _ _).mpr hBObj
      have hBCaller : ∃ outer, b.caller = some outer := by
        cases hC : b.caller with
        | some outer => exact ⟨outer, rfl⟩
        | none =>
          have hWf := hChain.replyWellFormed below b hBObj hC
          rw [hWf.2] at hBNext; cases hBNext
      obtain ⟨outer, hOuter⟩ := hBCaller
      refine ⟨some outer, ?_⟩
      unfold replyStackOuterCaller?
      rw [hGetSc]
      simp only [hHead, hPrev, hBGet, hBNext, bne_self_eq_false, Bool.false_eq_true, if_false,
        hOuter]

/-- WS-OD OD2.6: the chain invariant holds of a store holding neither Replies nor
SchedContexts — the empty boot store. -/
theorem donationChainWellFormed_of_no_reply_or_schedContext
    (st : SystemState)
    (hNoReply : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      st.objects[rid.toObjId]? ≠ some (.reply r))
    (hNoSc : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[scId.toObjId]? ≠ some (.schedContext sc)) :
    donationChainWellFormed st :=
  ⟨fun rid r hR => absurd hR (hNoReply rid r),
   fun scId sc hSc => absurd hSc (hNoSc scId sc),
   fun rid r _ hR _ => absurd hR (hNoReply rid r),
   fun rid r _ hR _ => absurd hR (hNoReply rid r),
   fun scId sc hSc => absurd hSc (hNoSc scId sc)⟩

/-- WS-OD OD2.6: the chain invariant holds of a store in which no Reply carries a
link and no context heads a stack — the two dispatch-pack witnesses. -/
theorem donationChainWellFormed_of_no_donations
    (st : SystemState)
    (hReplies : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      st.objects[rid.toObjId]? = some (.reply r) → r.prev = none ∧ r.next = none)
    (hHeads : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[scId.toObjId]? = some (.schedContext sc) → sc.scReply = none) :
    donationChainWellFormed st := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro rid r hR _
    exact hReplies rid r hR
  · intro scId sc hSc rid hRid
    rw [hHeads scId sc hSc] at hRid; cases hRid
  · intro rid r scId hR hNext
    rw [(hReplies rid r hR).2] at hNext; cases hNext
  · intro rid r below hR hPrev
    rw [(hReplies rid r hR).1] at hPrev; cases hPrev
  · intro scId sc hSc
    exact ⟨0, [], by rw [hHeads scId sc hSc]; simp⟩

-- ----------------------------------------------------------------------------
-- OD2.5: the frame family
-- ----------------------------------------------------------------------------

/-- WS-OD OD2.5 / `v0.35.4`: **the data `donationChainWellFormed` reads.**

A step frames the donation chain when it leaves every key's `replyStackLinks?`
and `schedContextStackHead?` alone **and consumes no caller link on a Reply**:
the third field says a post-state Reply with no caller had none before.  The
first two projections are exactly what the walk and the four link fields
consult; the third is what `replyWellFormed` — a Reply whose caller is gone
carries no link — needs, since a step could otherwise consume the caller of a
linked frame while framing its links, which is the one shape that is not a frame
— a head frame's consumption on the reply path, since `Reply.consumed` keeps a
head's links deliberately.  It is a *transient*, not an exception: the reply leg
leaves `donationChainWellFormedExcept` at that one key and the donation pop that
follows it in the same transition discharges it
(`endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed`, WS-RM
`v0.35.6`).  A **non**-head consumption clears the links too, so it fails
`replyLinks` as well and is not a borderline case.  Every step that rewrites no Reply satisfies the
third field trivially (`of_no_chain_object_write`), and a step that *links* a
caller (`linkReply`) satisfies it vacuously.

Mirrors `passiveServerIdleFrame` and `replyLinkageFrame`: reflexive, transitive,
and trivially satisfied by any step that leaves the object store untouched, so a
folded transition's frame is the composition of its primitives'. -/
structure donationChainFrame (st st' : SystemState) : Prop where
  /-- No Reply is created, destroyed, or has either stack link rewritten. -/
  replyLinks : ∀ oid : SeLe4n.ObjId,
    replyStackLinks? st'.objects[oid]? = replyStackLinks? st.objects[oid]?
  /-- No SchedContext is created, destroyed, or has its stack head rewritten. -/
  stackHeads : ∀ oid : SeLe4n.ObjId,
    schedContextStackHead? st'.objects[oid]? = schedContextStackHead? st.objects[oid]?
  /-- No Reply's caller link is consumed: a post-state Reply with no caller had
  none before. -/
  callerKept : ∀ (oid : SeLe4n.ObjId) (r' : Reply),
    st'.objects[oid]? = some (.reply r') → r'.caller = none →
    ∃ r : Reply, st.objects[oid]? = some (.reply r) ∧ r.caller = none

namespace donationChainFrame

/-- Reflexivity: a state frames onto itself. -/
theorem refl (st : SystemState) : donationChainFrame st st :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ r' hR hC => ⟨r', hR, hC⟩⟩

/-- Transitivity: chain two donation-chain frames. -/
theorem trans {st st' st'' : SystemState}
    (h1 : donationChainFrame st st') (h2 : donationChainFrame st' st'') :
    donationChainFrame st st'' :=
  ⟨fun oid => (h2.replyLinks oid).trans (h1.replyLinks oid),
   fun oid => (h2.stackHeads oid).trans (h1.stackHeads oid),
   fun oid r'' hR hC =>
     let ⟨r', hR', hC'⟩ := h2.callerKept oid r'' hR hC
     h1.callerKept oid r' hR' hC'⟩

/-- WS-OD OD2.5: **the objects-equality frame.**  A scheduler-only or
machine-only step frames the chain, which reads the object store and nothing
else. -/
theorem of_objects_eq {st st' : SystemState} (hObjs : st'.objects = st.objects) :
    donationChainFrame st st' :=
  ⟨fun oid => by rw [hObjs], fun oid => by rw [hObjs],
   fun oid r' hR hC => ⟨r', by rw [← hObjs]; exact hR, hC⟩⟩

/-- WS-OD OD2.5: **the no-chain-object-write frame.**  A step that creates,
destroys or rewrites no Reply and no SchedContext frames the chain, however many
objects of other kinds it writes — which is the shape of every endpoint-queue
splice, every TCB rewrite and every scheduler write in the tree, so most
transitions reach `donationChainWellFormed_of_frame` through this. -/
theorem of_no_chain_object_write {st st' : SystemState}
    (hReply : ∀ (oid : SeLe4n.ObjId) (r : Reply),
      st'.objects[oid]? = some (.reply r) ↔ st.objects[oid]? = some (.reply r))
    (hSc : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st'.objects[oid]? = some (.schedContext sc) ↔ st.objects[oid]? = some (.schedContext sc)) :
    donationChainFrame st st' := by
  refine ⟨fun oid => ?_, fun oid => ?_, fun oid r' hR hC => ⟨r', (hReply oid r').mp hR, hC⟩⟩
  · cases hPost : replyStackLinks? st'.objects[oid]? with
    | none =>
      cases hPre : replyStackLinks? st.objects[oid]? with
      | none => rfl
      | some pair =>
        obtain ⟨below, up⟩ := pair
        obtain ⟨r, hR, _, _⟩ := replyStackLinks?_eq_some_iff.mp hPre
        rw [(hReply oid r).mpr hR] at hPost
        cases hPost
    | some pair =>
      obtain ⟨below, up⟩ := pair
      obtain ⟨r, hR, hB, hU⟩ := replyStackLinks?_eq_some_iff.mp hPost
      rw [(hReply oid r).mp hR]
      simp [hB, hU]
  · cases hPost : schedContextStackHead? st'.objects[oid]? with
    | none =>
      cases hPre : schedContextStackHead? st.objects[oid]? with
      | none => rfl
      | some head =>
        obtain ⟨sc, hSc', _⟩ := schedContextStackHead?_eq_some_iff.mp hPre
        rw [(hSc oid sc).mpr hSc'] at hPost
        cases hPost
    | some head =>
      obtain ⟨sc, hSc', hH⟩ := schedContextStackHead?_eq_some_iff.mp hPost
      rw [(hSc oid sc).mp hSc']
      simp [hH]

end donationChainFrame

/-- WS-OD OD3.2: the head validation is transported across a frame. -/
theorem donationHeadResolves_of_frame {st st' : SystemState}
    (hFrame : donationChainFrame st st') (scId : SeLe4n.SchedContextId)
    (hRes : donationHeadResolves st scId) :
    donationHeadResolves st' scId := by
  intro sc hSc
  have hHeadEq := hFrame.stackHeads scId.toObjId
  rw [hSc] at hHeadEq
  obtain ⟨sc0, hSc0, hSame⟩ := schedContextStackHead?_eq_some_iff.mp hHeadEq.symm
  obtain ⟨head?, hHead, hBelow⟩ := hRes sc0 hSc0
  cases hR : sc.scReply with
  | none => exact ⟨none, donationHeadOf?_of_no_stack st' scId sc hR, fun _ _ _ h => by cases h⟩
  | some rid =>
    rw [hR] at hSame
    obtain ⟨p, hp, hpFst⟩ : ∃ p, head? = some p ∧ p.1 = rid := by
      have hKey := donationHeadOf?_ok_key st scId sc0 head? hHead
      rw [hSame] at hKey
      cases head? with
      | none => cases hKey
      | some p => exact ⟨p, rfl, Option.some.inj hKey⟩
    subst hp
    obtain ⟨hObj, hNext⟩ := donationHeadOf?_ok_resolves st scId sc0 p.1 p.2 hHead
    have hLinksEq := hFrame.replyLinks p.1.toObjId
    rw [hObj] at hLinksEq
    obtain ⟨r', hR', hPrev', hNext'⟩ := replyStackLinks?_eq_some_iff.mp hLinksEq
    refine ⟨some (p.1, r'), donationHeadOf?_of_reciprocal st' scId sc p.1 r'
      (by rw [hR, hpFst]) hR' (by rw [hNext', hNext]), ?_⟩
    intro rid' r'' below hEq hPrev''
    obtain ⟨hRid, hR''⟩ := Prod.mk.inj (Option.some.inj hEq)
    subst hRid; subst hR''
    obtain ⟨b, hB⟩ := hBelow p.1 p.2 below rfl (by rw [← hPrev']; exact hPrev'')
    have hBLinks := hFrame.replyLinks below.toObjId
    rw [hB] at hBLinks
    obtain ⟨b', hB', _, _⟩ := replyStackLinks?_eq_some_iff.mp hBLinks
    exact ⟨b', hB'⟩

/-- WS-OD OD2.5: a single `storeObject` frames the chain when the stored object
carries the same reply-stack data as the object it replaces, and consumes no
caller. -/
theorem donationChainFrame_of_storeObject
    {st st' : SystemState} {oid : SeLe4n.ObjId} {obj : KernelObject}
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hLinks : replyStackLinks? (some obj) = replyStackLinks? st.objects[oid]?)
    (hHead : schedContextStackHead? (some obj) = schedContextStackHead? st.objects[oid]?)
    (hCaller : ∀ r' : Reply, obj = .reply r' → r'.caller = none →
      ∃ r : Reply, st.objects[oid]? = some (.reply r) ∧ r.caller = none) :
    donationChainFrame st st' := by
  refine ⟨fun k => ?_, fun k => ?_, fun k r' hR hC => ?_⟩
  · by_cases hk : k = oid
    · subst hk; rw [storeObject_objects_eq' st k obj _ hObjInv hStore]; exact hLinks
    · rw [storeObject_objects_ne st st' oid k obj hk hObjInv hStore]
  · by_cases hk : k = oid
    · subst hk; rw [storeObject_objects_eq' st k obj _ hObjInv hStore]; exact hHead
    · rw [storeObject_objects_ne st st' oid k obj hk hObjInv hStore]
  · by_cases hk : k = oid
    · subst hk
      rw [storeObject_objects_eq' st k obj _ hObjInv hStore] at hR
      exact hCaller r' (Option.some.inj hR) hC
    · rw [storeObject_objects_ne st st' oid k obj hk hObjInv hStore] at hR
      exact ⟨r', hR, hC⟩

/-- **WS-OD OD5.6**: a single object-store insert frames the donation chain when
the inserted object carries the same reply-stack data as the object it replaces
and consumes no caller.

The `storeObject`-free sibling of `donationChainFrame_of_storeObject`: several
transitions write the object store with a direct `RHTable.insert` rather than
through `storeObject`, and stating the frame once is what keeps each of them
from re-deriving the same two-case lookup split.

**WS-RM (`v0.35.6`)** re-homed it here, beside the predicate it is about.  It
was private to the cancellation shape module, and the fault-reply path needs the
same fact -- a second copy in a module the first does not import is the
one-question-two-answers shape this tree keeps paying for. -/
theorem donationChainFrame_of_objects_insert
    {st : SystemState} {k0 : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt)
    (hLinks : replyStackLinks? (some obj) = replyStackLinks? st.objects[k0]?)
    (hHead : schedContextStackHead? (some obj) = schedContextStackHead? st.objects[k0]?)
    (hCaller : ∀ r' : Reply, obj = .reply r' → r'.caller = none →
      ∃ r : Reply, st.objects[k0]? = some (.reply r) ∧ r.caller = none) :
    donationChainFrame st { st with objects := st.objects.insert k0 obj } := by
  have hPoint : ∀ k : SeLe4n.ObjId,
      (st.objects.insert k0 obj)[k]? = if k = k0 then some obj else st.objects[k]? := by
    intro k
    by_cases hk : k = k0
    · subst hk
      rw [if_pos rfl]
      exact RobinHood.RHTable.getElem?_insert_self st.objects k obj hInv
    · rw [if_neg hk]
      exact RobinHood.RHTable.getElem?_insert_ne st.objects k0 k obj
        (by simpa using fun h => hk h.symm) hInv
  refine ⟨fun k => ?_, fun k => ?_, fun k r' hR hC => ?_⟩
  · show replyStackLinks? ((st.objects.insert k0 obj)[k]?) = _
    rw [hPoint k]
    by_cases hk : k = k0
    · subst hk; rw [if_pos rfl]; exact hLinks
    · rw [if_neg hk]
  · show schedContextStackHead? ((st.objects.insert k0 obj)[k]?) = _
    rw [hPoint k]
    by_cases hk : k = k0
    · subst hk; rw [if_pos rfl]; exact hHead
    · rw [if_neg hk]
  · have hR' : (st.objects.insert k0 obj)[k]? = some (.reply r') := hR
    rw [hPoint k] at hR'
    by_cases hk : k = k0
    · subst hk
      rw [if_pos rfl] at hR'
      exact hCaller r' (Option.some.inj hR') hC
    · rw [if_neg hk] at hR'
      exact ⟨r', hR', hC⟩

/-- A TCB store at a key holding no Reply and no SchedContext frames the chain. -/
theorem donationChainFrame_of_storeObject_tcb
    {st st' : SystemState} {oid : SeLe4n.ObjId} {tcb : TCB}
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.tcb tcb) st = .ok ((), st'))
    (hNoLinks : replyStackLinks? st.objects[oid]? = none)
    (hNoHead : schedContextStackHead? st.objects[oid]? = none) :
    donationChainFrame st st' :=
  donationChainFrame_of_storeObject hObjInv hStore (by rw [hNoLinks]; rfl)
    (by rw [hNoHead]; rfl) (fun _ h => by cases h)

/-- A TCB rewrite frames the chain. -/
theorem donationChainFrame_of_tcb_rewrite
    {st st' : SystemState} {oid : SeLe4n.ObjId} {tcbOld tcb : TCB}
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[oid]? = some (.tcb tcbOld))
    (hStore : storeObject oid (.tcb tcb) st = .ok ((), st')) :
    donationChainFrame st st' :=
  donationChainFrame_of_storeObject_tcb hObjInv hStore (by rw [hOld]; rfl) (by rw [hOld]; rfl)

/-- A SchedContext rewrite that keeps the stack head frames the chain. -/
theorem donationChainFrame_of_storeObject_schedContext
    {st st' : SystemState} {scId : SeLe4n.SchedContextId} {scOld sc : SchedContext}
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[scId.toObjId]? = some (.schedContext scOld))
    (hHeadEq : sc.scReply = scOld.scReply)
    (hStore : storeObject scId.toObjId (.schedContext sc) st = .ok ((), st')) :
    donationChainFrame st st' :=
  donationChainFrame_of_storeObject hObjInv hStore (by rw [hOld]; rfl)
    (by rw [hOld]; simp [hHeadEq]) (fun _ h => by cases h)

/-- A Reply rewrite that keeps both stack links and consumes no caller frames the
chain. -/
theorem donationChainFrame_of_storeObject_reply
    {st st' : SystemState} {rid : SeLe4n.ReplyId} {rOld r : Reply}
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[rid.toObjId]? = some (.reply rOld))
    (hPrevEq : r.prev = rOld.prev)
    (hNextEq : r.next = rOld.next)
    (hCaller : r.caller = none → rOld.caller = none)
    (hStore : storeObject rid.toObjId (.reply r) st = .ok ((), st')) :
    donationChainFrame st st' :=
  donationChainFrame_of_storeObject hObjInv hStore (by rw [hOld]; simp [hPrevEq, hNextEq])
    (by rw [hOld]; rfl)
    (fun r' hEq hC => ⟨rOld, hOld, by
      have hr : r' = r := KernelObject.reply.inj hEq.symm
      subst hr; exact hCaller hC⟩)

/-- `linkReply` frames the chain: it rewrites one Reply's `caller` from `none` to
`some`, keeping both links, and consumes nothing. -/
theorem linkReply_donationChainFrame (st st' : SystemState)
    (rid : SeLe4n.ReplyId) (caller : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkReply rid caller st = .ok ((), st')) :
    donationChainFrame st st' := by
  unfold SystemState.linkReply at hStep
  revert hStep
  cases hGet : st.getReply? rid with
  | none => intro h; cases h
  | some r =>
    simp only []
    cases hFree : r.isFree with
    | false => simp only [Bool.false_eq_true, if_false]; intro h; cases h
    | true =>
      simp only [if_true]
      intro hStore
      exact donationChainFrame_of_storeObject_reply (r := { r with caller := some caller })
        hObjInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hGet) rfl rfl
        (fun h => by simp at h) hStore

/-- `linkCallerReply` frames the chain: `linkReply` then a TCB store. -/
theorem linkCallerReply_donationChainFrame (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    donationChainFrame st st' := by
  unfold SystemState.linkCallerReply at hStep
  revert hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error _ => intro h; cases h
  | ok p1 =>
    obtain ⟨u, st1⟩ := p1; cases u
    simp only []
    have hF1 := linkReply_donationChainFrame st st1 rid caller hObjInv hLink
    have hInv1 := SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    cases hT : st1.getTcb? caller with
    | none => intro h; cases h
    | some tcb =>
      simp only []
      cases hRO : tcb.replyObject.isNone with
      | false => simp only [Bool.false_eq_true, if_false]; intro h; cases h
      | true =>
        simp only [if_true]
        intro hStore
        exact hF1.trans (donationChainFrame_of_tcb_rewrite hInv1
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hStore)

/-- WS-OD OD2.5: **the frame transports the whole predicate.**  Every field is
stated over the two projections and the caller relation the frame preserves, so
no case analysis on the step is needed. -/
theorem donationChainWellFormed_of_frame {st st' : SystemState}
    (hFrame : donationChainFrame st st') (hInv : donationChainWellFormed st) :
    donationChainWellFormed st' := by
  -- The two projections at any key, read back to the pre-state.
  have hReplyPre : ∀ (oid : SeLe4n.ObjId) (r' : Reply),
      st'.objects[oid]? = some (.reply r') →
      ∃ r : Reply, st.objects[oid]? = some (.reply r) ∧ r.prev = r'.prev ∧ r.next = r'.next := by
    intro oid r' hR'
    have hEq := hFrame.replyLinks oid
    rw [hR'] at hEq
    obtain ⟨r, hR, hP, hN⟩ := replyStackLinks?_eq_some_iff.mp hEq.symm
    exact ⟨r, hR, hP, hN⟩
  have hReplyPost : ∀ (oid : SeLe4n.ObjId) (r : Reply),
      st.objects[oid]? = some (.reply r) →
      ∃ r' : Reply, st'.objects[oid]? = some (.reply r') ∧ r'.prev = r.prev ∧ r'.next = r.next := by
    intro oid r hR
    have hEq := hFrame.replyLinks oid
    rw [hR] at hEq
    obtain ⟨r', hR', hP, hN⟩ := replyStackLinks?_eq_some_iff.mp hEq
    exact ⟨r', hR', hP, hN⟩
  have hScPre : ∀ (oid : SeLe4n.ObjId) (sc' : SchedContext),
      st'.objects[oid]? = some (.schedContext sc') →
      ∃ sc : SchedContext, st.objects[oid]? = some (.schedContext sc) ∧ sc.scReply = sc'.scReply := by
    intro oid sc' hSc'
    have hEq := hFrame.stackHeads oid
    rw [hSc'] at hEq
    obtain ⟨sc, hSc, hH⟩ := schedContextStackHead?_eq_some_iff.mp hEq.symm
    exact ⟨sc, hSc, hH⟩
  have hScPost : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st.objects[oid]? = some (.schedContext sc) →
      ∃ sc' : SchedContext, st'.objects[oid]? = some (.schedContext sc') ∧ sc'.scReply = sc.scReply := by
    intro oid sc hSc
    have hEq := hFrame.stackHeads oid
    rw [hSc] at hEq
    obtain ⟨sc', hSc', hH⟩ := schedContextStackHead?_eq_some_iff.mp hEq
    exact ⟨sc', hSc', hH⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro rid r' hR' hC
    obtain ⟨r, hR, hCPre⟩ := hFrame.callerKept rid.toObjId r' hR' hC
    obtain ⟨r0, hR0, hP, hN⟩ := hReplyPre rid.toObjId r' hR'
    rw [hR] at hR0
    have hEq : r0 = r := KernelObject.reply.inj (Option.some.inj hR0).symm
    subst hEq
    have hWf := hInv.replyWellFormed rid r0 hR hCPre
    exact ⟨by rw [← hP]; exact hWf.1, by rw [← hN]; exact hWf.2⟩
  · intro scId sc' hSc' rid hRid
    obtain ⟨sc, hSc, hH⟩ := hScPre scId.toObjId sc' hSc'
    obtain ⟨r, hR, hNext⟩ := hInv.headLinkReciprocal scId sc hSc rid (by rw [hH]; exact hRid)
    obtain ⟨r', hR', _, hN⟩ := hReplyPost rid.toObjId r hR
    exact ⟨r', hR', by rw [hN]; exact hNext⟩
  · intro rid r' scId hR' hNext'
    obtain ⟨r, hR, _, hN⟩ := hReplyPre rid.toObjId r' hR'
    obtain ⟨sc, hSc, hHead⟩ := hInv.headLinkResolves rid r scId hR (by rw [hN]; exact hNext')
    obtain ⟨sc', hSc', hH⟩ := hScPost scId.toObjId sc hSc
    exact ⟨sc', hSc', by rw [hH]; exact hHead⟩
  · intro rid r' below hR' hPrev'
    obtain ⟨r, hR, hP, _⟩ := hReplyPre rid.toObjId r' hR'
    obtain ⟨b, hB, hBNext⟩ := hInv.prevLinkReciprocal rid r below hR (by rw [hP]; exact hPrev')
    obtain ⟨b', hB', _, hBN⟩ := hReplyPost below.toObjId b hB
    exact ⟨b', hB', by rw [hBN]; exact hBNext⟩
  · intro scId sc' hSc'
    obtain ⟨sc, hSc, hH⟩ := hScPre scId.toObjId sc' hSc'
    obtain ⟨fuel, chain, hChain⟩ := hInv.headTerminates scId sc hSc
    refine ⟨fuel, chain, ?_⟩
    rw [hH] at hChain
    unfold donationChainFrom at hChain ⊢
    rw [donationChainWalk_congr hFrame.replyLinks]
    exact hChain

/-- **WS-RM (`v0.35.6`): the frame transports the relaxed form too**, at the same
key — so a step that moves no chain data cannot turn the head transient into a
different one.  Every clause but the first is the unrelaxed clause verbatim; the
first is the unrelaxed argument with the exempt key carried through. -/
theorem donationChainWellFormedExcept_of_frame {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hFrame : donationChainFrame st st')
    (hInv : donationChainWellFormedExcept st rid) :
    donationChainWellFormedExcept st' rid := by
  have hReplyPre : ∀ (oid : SeLe4n.ObjId) (r' : Reply),
      st'.objects[oid]? = some (.reply r') →
      ∃ r : Reply, st.objects[oid]? = some (.reply r) ∧ r.prev = r'.prev ∧ r.next = r'.next := by
    intro oid r' hR'
    have hEq := hFrame.replyLinks oid
    rw [hR'] at hEq
    obtain ⟨r, hR, hP, hN⟩ := replyStackLinks?_eq_some_iff.mp hEq.symm
    exact ⟨r, hR, hP, hN⟩
  have hReplyPost : ∀ (oid : SeLe4n.ObjId) (r : Reply),
      st.objects[oid]? = some (.reply r) →
      ∃ r' : Reply, st'.objects[oid]? = some (.reply r') ∧ r'.prev = r.prev ∧ r'.next = r.next := by
    intro oid r hR
    have hEq := hFrame.replyLinks oid
    rw [hR] at hEq
    obtain ⟨r', hR', hP, hN⟩ := replyStackLinks?_eq_some_iff.mp hEq
    exact ⟨r', hR', hP, hN⟩
  have hScPre : ∀ (oid : SeLe4n.ObjId) (sc' : SchedContext),
      st'.objects[oid]? = some (.schedContext sc') →
      ∃ sc : SchedContext, st.objects[oid]? = some (.schedContext sc) ∧ sc.scReply = sc'.scReply := by
    intro oid sc' hSc'
    have hEq := hFrame.stackHeads oid
    rw [hSc'] at hEq
    obtain ⟨sc, hSc, hH⟩ := schedContextStackHead?_eq_some_iff.mp hEq.symm
    exact ⟨sc, hSc, hH⟩
  have hScPost : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st.objects[oid]? = some (.schedContext sc) →
      ∃ sc' : SchedContext, st'.objects[oid]? = some (.schedContext sc') ∧ sc'.scReply = sc.scReply := by
    intro oid sc hSc
    have hEq := hFrame.stackHeads oid
    rw [hSc] at hEq
    obtain ⟨sc', hSc', hH⟩ := schedContextStackHead?_eq_some_iff.mp hEq
    exact ⟨sc', hSc', hH⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q r' hNe hR' hC
    obtain ⟨r, hR, hCPre⟩ := hFrame.callerKept q.toObjId r' hR' hC
    obtain ⟨r0, hR0, hP, hN⟩ := hReplyPre q.toObjId r' hR'
    rw [hR] at hR0
    have hEq : r0 = r := KernelObject.reply.inj (Option.some.inj hR0).symm
    subst hEq
    have hWf := hInv.replyWellFormedExcept q r0 hNe hR hCPre
    exact ⟨by rw [← hP]; exact hWf.1, by rw [← hN]; exact hWf.2⟩
  · intro scId sc' hSc' q hRid
    obtain ⟨sc, hSc, hH⟩ := hScPre scId.toObjId sc' hSc'
    obtain ⟨r, hR, hNext⟩ := hInv.headLinkReciprocal scId sc hSc q (by rw [hH]; exact hRid)
    obtain ⟨r', hR', _, hN⟩ := hReplyPost q.toObjId r hR
    exact ⟨r', hR', by rw [hN]; exact hNext⟩
  · intro q r' scId hR' hNext'
    obtain ⟨r, hR, _, hN⟩ := hReplyPre q.toObjId r' hR'
    obtain ⟨sc, hSc, hHead⟩ := hInv.headLinkResolves q r scId hR (by rw [hN]; exact hNext')
    obtain ⟨sc', hSc', hH⟩ := hScPost scId.toObjId sc hSc
    exact ⟨sc', hSc', by rw [hH]; exact hHead⟩
  · intro q r' below hR' hPrev'
    obtain ⟨r, hR, hP, _⟩ := hReplyPre q.toObjId r' hR'
    obtain ⟨b, hB, hBNext⟩ := hInv.prevLinkReciprocal q r below hR (by rw [hP]; exact hPrev')
    obtain ⟨b', hB', _, hBN⟩ := hReplyPost below.toObjId b hB
    exact ⟨b', hB', by rw [hBN]; exact hBNext⟩
  · intro scId sc' hSc'
    obtain ⟨sc, hSc, hH⟩ := hScPre scId.toObjId sc' hSc'
    obtain ⟨fuel, chain, hChain⟩ := hInv.headTerminates scId sc hSc
    refine ⟨fuel, chain, ?_⟩
    rw [hH] at hChain
    unfold donationChainFrom at hChain ⊢
    rw [donationChainWalk_congr hFrame.replyLinks]
    exact hChain

/-- WS-OD OD3.4: the outer-caller resolution is transported across a frame. -/
theorem replyStackOuterCallerResolves_of_frame {st st' : SystemState}
    (hFrame : donationChainFrame st st') (scId : SeLe4n.SchedContextId)
    (hChain : donationChainWellFormed st) :
    replyStackOuterCallerResolves st' scId :=
  replyStackOuterCallerResolves_of_chainWellFormed st' scId
    (donationChainWellFormed_of_frame hFrame hChain)

/-- WS-OD OD2.3/OD2.4: **the bridge to `Reply.wellFormed`.**  The state-level
invariant carries the object-level predicate, so a reader that has one has the
other — which is what keeps `Reply.wellFormed` a consumed property rather than
an unwired decoration beside the structure it describes. -/
theorem donationChainWellFormed.replyWellFormedAt {st : SystemState}
    (h : donationChainWellFormed st) {rid : SeLe4n.ReplyId} {r : Reply}
    (hR : st.objects[rid.toObjId]? = some (.reply r)) :
    r.wellFormed :=
  h.replyWellFormed rid r hR

/-- WS-RR RR3.7: **a linked caller is always `.blockedOnReply`.**

Reading the two clauses of `replyCallerLinkageReciprocal` in sequence: a TCB with
`replyObject = some rid` has a Reply naming it (forward), and a Reply naming a
thread has that thread `.blockedOnReply` (backward).  The composite is the fact
every de-threading proof in this phase actually uses, because its contrapositive
— *a thread that is not `.blockedOnReply` carries no reply object* — turns the
`hSenderNotReply` / `hWaiterNotReply` / `hCallerNotReply` side conditions the
bundles already carry into the "unlinked" premise the linkage frames need. -/
theorem replyCallerLinkageReciprocal.linkedIsBlockedOnReply {st : SystemState}
    (h : replyCallerLinkageReciprocal st) {tid : SeLe4n.ThreadId} {tcb : TCB}
    {rid : SeLe4n.ReplyId}
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hRO : tcb.replyObject = some rid) :
    ∃ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), tcb.ipcState = .blockedOnReply ep rt := by
  obtain ⟨r, hReply, hCaller⟩ := h.1 tid tcb rid hTcb hRO
  obtain ⟨tcb2, hTcb2, _, hBlk⟩ := h.2 rid r tid hReply hCaller
  rw [hTcb2] at hTcb
  obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcb.symm)
  exact hBlk

/-- WS-RR RR3.7: the contrapositive, in the shape the bundles supply it — a thread
the transition is about to rewrite, known not to be awaiting a reply, carries no
reply object and so is invisible to `replyCallerLinkageReciprocal`. -/
theorem replyCallerLinkageReciprocal.unlinkedOfNotBlockedOnReply {st : SystemState}
    (h : replyCallerLinkageReciprocal st) {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hNotReply : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
      tcb.ipcState ≠ .blockedOnReply ep rt) :
    tcb.replyObject = none := by
  cases hRO : tcb.replyObject with
  | none => rfl
  | some rid =>
    obtain ⟨ep, rt, hBlk⟩ := h.linkedIsBlockedOnReply hTcb hRO
    exact absurd hBlk (hNotReply ep rt)

/-- WS-RR RR3.7: the reply-linkage data `replyCallerLinkageReciprocal` reads.

Three obligations, one per thing the conjunct looks at: every Reply object's
`caller` back-link, every TCB's `replyObject` forward link, and — for a TCB that
**is** linked — its `.blockedOnReply`-ness, which the backward clause demands.

An **unlinked** thread's `ipcState` is deliberately unconstrained.  That is what
makes the frame usable at all: a send blocks its sender, a wake readies its
receiver, a notification parks its waiter, and none of those touches the linkage
— provided the rewritten thread carries no reply object, which
`replyCallerLinkageReciprocal.unlinkedOfNotBlockedOnReply` derives from the
`hSenderNotReply`-shaped side conditions the bundles already have.

Mirrors `passiveServerIdleFrame`: reflexive, transitive, and trivially satisfied
by any step that leaves the object map untouched, so a folded transition's frame
is the composition of its primitives'. -/
structure replyLinkageFrame (st st' : SystemState) : Prop where
  /-- No Reply's caller back-link is created, destroyed or rewritten.

  WS-OD OD3.2: stated on the `caller` projection rather than on the whole
  object.  `replyCallerLinkageReciprocal` — the only conjunct this frame serves
  — reads exactly that field, and the donation return's reply-stack pop resets
  the popped Reply's `prev` and `next`, which makes whole-object agreement
  false of it.  Every other transition in the tree still has full identity and
  reaches this through `callerAgree_of_objectAgree`. -/
  replyCallerAgree : ∀ (rid : SeLe4n.ReplyId) (caller : Option SeLe4n.ThreadId),
    (∃ r : Reply, st'.objects[rid.toObjId]? = some (.reply r) ∧ r.caller = caller) ↔
    (∃ r : Reply, st.objects[rid.toObjId]? = some (.reply r) ∧ r.caller = caller)
  /-- Every post-state TCB came from a pre-state TCB with the same `replyObject`. -/
  pullback : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    st'.objects[tid.toObjId]? = some (.tcb tcb') →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb'.replyObject = tcb.replyObject
  /-- A **linked** pre-state TCB survives with the same `replyObject`, and stays
  `.blockedOnReply` if it was. -/
  pushLinked : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.replyObject = some rid →
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧
      tcb'.replyObject = tcb.replyObject ∧
      ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        tcb.ipcState = .blockedOnReply ep rt →
        ∃ (ep' : SeLe4n.ObjId) (rt' : Option SeLe4n.ThreadId),
          tcb'.ipcState = .blockedOnReply ep' rt'

namespace replyLinkageFrame

/-- WS-OD OD3.2: the caller-level agreement from **exact** Reply agreement — the
shape every transition but the donation return has, and the one this structure's
field asked for before the reply-stack pop existed.  Named so that a construction
site states the stronger fact it actually proves and this lemma does the
weakening once. -/
theorem callerAgree_of_objectAgree {st st' : SystemState}
    (h : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      st'.objects[rid.toObjId]? = some (.reply r) ↔ st.objects[rid.toObjId]? = some (.reply r)) :
    ∀ (rid : SeLe4n.ReplyId) (caller : Option SeLe4n.ThreadId),
      (∃ r : Reply, st'.objects[rid.toObjId]? = some (.reply r) ∧ r.caller = caller) ↔
      (∃ r : Reply, st.objects[rid.toObjId]? = some (.reply r) ∧ r.caller = caller) :=
  fun rid _ => ⟨fun ⟨r, hr, hc⟩ => ⟨r, (h rid r).mp hr, hc⟩,
                fun ⟨r, hr, hc⟩ => ⟨r, (h rid r).mpr hr, hc⟩⟩

/-- Reflexivity: a state frames onto itself. -/
theorem refl (st : SystemState) : replyLinkageFrame st st :=
  ⟨fun _ _ => Iff.rfl, fun _ tcb' h => ⟨tcb', h, rfl⟩,
   fun _ tcb _ h _ => ⟨tcb, h, rfl, fun ep rt hb => ⟨ep, rt, hb⟩⟩⟩

/-- Transitivity: chain two reply-linkage frames.  The middle state's TCB is
still linked (its `replyObject` is the pre-state's), which is what lets
`pushLinked` compose. -/
theorem trans {st st' st'' : SystemState}
    (h1 : replyLinkageFrame st st') (h2 : replyLinkageFrame st' st'') :
    replyLinkageFrame st st'' :=
  ⟨fun rid c => (h2.replyCallerAgree rid c).trans (h1.replyCallerAgree rid c),
   fun tid tcb'' h => by
     obtain ⟨tcb', h', hEq'⟩ := h2.pullback tid tcb'' h
     obtain ⟨tcb, hh, hEq⟩ := h1.pullback tid tcb' h'
     exact ⟨tcb, hh, hEq'.trans hEq⟩,
   fun tid tcb rid h hRO => by
     obtain ⟨tcb', h', hEq', hBlk'⟩ := h1.pushLinked tid tcb rid h hRO
     obtain ⟨tcb'', h'', hEq'', hBlk''⟩ :=
       h2.pushLinked tid tcb' rid h' (hEq'.trans hRO)
     refine ⟨tcb'', h'', hEq''.trans hEq', fun ep rt hb => ?_⟩
     obtain ⟨ep', rt', hb'⟩ := hBlk' ep rt hb
     exact hBlk'' ep' rt' hb'⟩

/-- A step that leaves the object map untouched frames trivially. -/
theorem of_objects_eq {st st' : SystemState} (hObjs : st'.objects = st.objects) :
    replyLinkageFrame st st' :=
  ⟨fun _ _ => by rw [hObjs], fun _ tcb' h => ⟨tcb', by rw [hObjs] at h; exact h, rfl⟩,
   fun _ tcb _ h _ => ⟨tcb, by rw [hObjs]; exact h, rfl, fun ep rt hb => ⟨ep, rt, hb⟩⟩⟩

/-- The pointwise form, for steps whose object map agrees key by key rather than
definitionally. -/
theorem of_getElem_eq {st st' : SystemState}
    (hObjs : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]?) :
    replyLinkageFrame st st' :=
  ⟨fun rid _ => by rw [hObjs], fun tid tcb' h => ⟨tcb', by rw [hObjs] at h; exact h, rfl⟩,
   fun tid tcb _ h _ => ⟨tcb, by rw [hObjs]; exact h, rfl, fun ep rt hb => ⟨ep, rt, hb⟩⟩⟩

/-- WS-RR RR3.7: unlinkedness transports forward across a frame — a slot whose
pre-state thread carried no reply object still carries none, because the frame
preserves `replyObject`.  The step every folded transition needs to state its
"the rewritten thread is unlinked" premise on the *intermediate* state. -/
theorem unlinked_forward {st st' : SystemState} (hF : replyLinkageFrame st st')
    {tid : SeLe4n.ThreadId}
    (hU : ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.replyObject = none) :
    ∀ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') → tcb'.replyObject = none := by
  intro tcb' hTcb'
  obtain ⟨tcb, hTcb, hEq⟩ := hF.pullback tid tcb' hTcb'
  rw [hEq]; exact hU tcb hTcb

end replyLinkageFrame

/-- WS-RR RR3.7: `replyCallerLinkageReciprocal` preservation from the reusable
frame — the de-threading lever for every transition that does not itself create
or consume a caller↔Reply edge. -/
theorem replyCallerLinkageReciprocal_of_frame {st st' : SystemState}
    (hFrame : replyLinkageFrame st st')
    (hInv : replyCallerLinkageReciprocal st) :
    replyCallerLinkageReciprocal st' := by
  refine ⟨fun tid tcb' rid hTcb' hRO' => ?_, fun rid r tid hReply' hCaller => ?_⟩
  · obtain ⟨tcb, hTcb, hEq⟩ := hFrame.pullback tid tcb' hTcb'
    obtain ⟨r, hReply, hCaller⟩ := hInv.1 tid tcb rid hTcb (hEq ▸ hRO')
    exact (hFrame.replyCallerAgree rid (some tid)).mpr ⟨r, hReply, hCaller⟩
  · obtain ⟨r0, hReply0, hCaller0⟩ :=
      (hFrame.replyCallerAgree rid (some tid)).mp ⟨r, hReply', hCaller⟩
    obtain ⟨tcb, hTcb, hRO, hBlk⟩ := hInv.2 rid r0 tid hReply0 hCaller0
    obtain ⟨tcb', hTcb', hEq, hBlk'⟩ := hFrame.pushLinked tid tcb rid hTcb hRO
    obtain ⟨ep, rt, hb⟩ := hBlk
    exact ⟨tcb', hTcb', hEq.trans hRO, hBlk' ep rt hb⟩

/-- IPC de-threading D6 (`passiveServerIdle`): preservation from the reusable frame. -/
theorem passiveServerIdle_of_frame {st st' : SystemState}
    (hFrame : passiveServerIdleFrame st st')
    (hInv : passiveServerIdle st) :
    passiveServerIdle st' := by
  intro tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent'
  by_cases hAllowed : passiveServerIdleAllowed tcb'.ipcState
  · exact hAllowed
  · obtain ⟨tcb, hTcb, hUnbound, hNotInQ, hNotCurrent, hIpc⟩ :=
      hFrame.pullback tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' hAllowed
    rw [← hIpc]
    exact hInv tid tcb hTcb hUnbound hNotInQ hNotCurrent

-- ============================================================================
-- Z7-I: Donation budget transfer consistency
-- ============================================================================

/-- Z7-I: At most one thread holds a given SchedContext at any time.

If a SchedContext is donated (some thread has `.donated(scId, _)` binding),
then no other thread has `.bound(scId)` or `.donated(scId, _)` binding for
the same SchedContext. This prevents double-spending of CPU budget. -/
def donationBudgetTransfer (st : SystemState) : Prop :=
  ∀ (tid1 tid2 : SeLe4n.ThreadId) (tcb1 tcb2 : TCB)
    (scId : SeLe4n.SchedContextId),
    st.objects[tid1.toObjId]? = some (.tcb tcb1) →
    st.objects[tid2.toObjId]? = some (.tcb tcb2) →
    tid1 ≠ tid2 →
    tcb1.schedContextBinding.scId? = some scId →
    tcb2.schedContextBinding.scId? = some scId →
    False

/-- WS-RR RR2.5: an object-store-preserving step frames `donationBudgetTransfer`. -/
theorem donationBudgetTransfer_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : donationBudgetTransfer st) :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2
  rw [hObjs] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2

-- ============================================================================
-- Z7: Default state proofs for donation invariants
-- ============================================================================

/-- Z7: donationChainAcyclic holds trivially when no TCBs have donated bindings. -/
theorem donationChainAcyclic_of_no_donated
    (st : SystemState)
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      ∀ scId owner, tcb.schedContextBinding ≠ .donated scId owner) :
    donationChainAcyclic st := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 _
  exact absurd hB1 (hNone tid1 tcb1 h1 scId1 tid2)

-- ============================================================================
-- AG8-F: Donation Chain Cycle Prevention (H3-PROOF-03)
-- ============================================================================

/-- AG8-F: `donationOwnerValid` subsumes `donationChainAcyclic`.

Proves that 2-cycles are structurally impossible when donation owners
have `.unbound` bindings (Finding F-3: the donor relinquishes its
SchedContext on donation). If thread `tid1` has `.donated scId1 tid2`, then
by `donationOwnerValid`, `tid2` has `.unbound`. Since `.unbound` and
`.donated` are distinct constructors of `SchedContextBinding`, `tid2` cannot
simultaneously have `.donated scId2 tid1`. Contradiction. -/
theorem donationOwnerValid_implies_donationChainAcyclic
    (st : SystemState)
    (hDOV : donationOwnerValid st) :
    donationChainAcyclic st := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 hTcb1 hTcb2 hDon1 hDon2
  -- tid1 has .donated scId1 tid2, so by donationOwnerValid:
  -- tid2 (the owner) has .unbound
  have ⟨_, hOwner⟩ := hDOV tid1 tcb1 scId1 tid2 hTcb1 hDon1
  obtain ⟨ownerTcb, hOwnerTcb, hBound, _⟩ := hOwner
  -- Equate ownerTcb with tcb2: both come from st.objects[tid2.toObjId]?
  rw [hTcb2] at hOwnerTcb
  cases hOwnerTcb -- ownerTcb = tcb2
  -- Now: hBound : tcb2.schedContextBinding = .unbound
  --      hDon2  : tcb2.schedContextBinding = .donated scId2 tid1
  -- .unbound ≠ .donated — constructor disjointness
  rw [hDon2] at hBound; cases hBound

/-- AG8-F: Donation chains cannot extend beyond length 1.

If thread `tid` has `.donated scId owner`, then by `donationOwnerValid`,
the `owner` has `schedContextBinding = .unbound` (Finding F-3: the donor
relinquishes its SchedContext on donation). Since `.unbound` and
`.donated` are distinct constructors of `SchedContextBinding`, the owner
cannot also have a `.donated` binding. This prevents donation chains of
length ≥ 2 entirely — not just cycles, but all extensions. -/
theorem donationChain_no_extension
    (st : SystemState)
    (hDOV : donationOwnerValid st)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hDonated : tcb.schedContextBinding = .donated scId owner) :
    ∀ (ownerTcb : TCB),
      st.objects[owner.toObjId]? = some (.tcb ownerTcb) →
      ∀ scId2 owner2, ownerTcb.schedContextBinding ≠ .donated scId2 owner2 := by
  intro ownerTcb hOwnerTcb scId2 owner2 hContra
  have ⟨_, hOwner⟩ := hDOV tid tcb scId owner hTcb hDonated
  obtain ⟨ownerTcb', hOwnerTcb', hBound, _⟩ := hOwner
  rw [hOwnerTcb] at hOwnerTcb'
  cases hOwnerTcb' -- ownerTcb' = ownerTcb
  -- hBound : ownerTcb.schedContextBinding = .unbound
  -- hContra : ownerTcb.schedContextBinding = .donated scId2 owner2
  rw [hContra] at hBound; cases hBound

/-- AG8-F: Blocked-on-reply threads cannot initiate calls.
A thread in `.blockedOnReply` state has `ipcState ≠ .ready`, so it
cannot enter `endpointCall` (which requires `.ready` state per the
`runnableThreadIpcReady` scheduler invariant — only `.ready` threads
are in the runnable queue and thus dispatched to execute). -/
theorem blockedOnReply_cannot_call
    (ipcState : ThreadIpcState)
    (epId : SeLe4n.ObjId) (replyTarget : Option SeLe4n.ThreadId)
    (h : ipcState = .blockedOnReply epId replyTarget) :
    ipcState ≠ .ready := by
  rw [h]; intro hContra; cases hContra

/-- Z7: donationOwnerValid holds vacuously when no TCBs have donated bindings. -/
theorem donationOwnerValid_of_no_donated
    (st : SystemState)
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      ∀ scId owner, tcb.schedContextBinding ≠ .donated scId owner) :
    donationOwnerValid st := by
  intro tid tcb scId owner hTcb hBinding
  exact absurd hBinding (hNone tid tcb hTcb scId owner)

/-- Z7: donationBudgetTransfer holds trivially when no two threads share a SchedContext. -/
theorem donationBudgetTransfer_of_no_shared
    (st : SystemState)
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding = .unbound) :
    donationBudgetTransfer st := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 _ hB1 _
  have := hNone tid1 tcb1 h1
  simp [this, SchedContextBinding.scId?] at hB1

-- ============================================================================
-- IPC de-threading D6: SchedContext-binding frame for `donationBudgetTransfer`
-- ============================================================================

/-- IPC de-threading D6: two states have **the same SchedContext bindings** when every
post-state TCB slot pulls back to a pre-state TCB carrying an equal `schedContextBinding`.
This is the exact frame `donationBudgetTransfer` (which reads only `schedContextBinding`)
needs: it is preserved by every core IPC transition that never writes a binding (all but
the donation primitives `donateSchedContext` / `returnDonatedSchedContext`).  Stated
backward (post ⟹ pre) so it composes directly with the store-frame style used throughout
the de-threading proofs. -/
def sameSchedContextBindings (st st' : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    st'.objects[tid.toObjId]? = some (.tcb tcb') →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.schedContextBinding = tcb'.schedContextBinding

namespace sameSchedContextBindings

/-- Reflexivity: a state has the same bindings as itself. -/
theorem refl (st : SystemState) : sameSchedContextBindings st st :=
  fun _ tcb' h => ⟨tcb', h, rfl⟩

/-- Transitivity: chain two binding-preserving steps. -/
theorem trans {st st' st'' : SystemState}
    (h1 : sameSchedContextBindings st st') (h2 : sameSchedContextBindings st' st'') :
    sameSchedContextBindings st st'' := by
  intro tid tcb'' hObj''
  obtain ⟨tc', hObj', hEq'⟩ := h2 tid tcb'' hObj''
  obtain ⟨tc, hObj, hEq⟩ := h1 tid tc' hObj'
  exact ⟨tc, hObj, hEq.trans hEq'⟩

/-- A transition that leaves the object store untouched (a scheduler-only step such
as `removeRunnable` / `ensureRunnable`) preserves all bindings. -/
theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    sameSchedContextBindings st st' :=
  fun _ tcb' hObj => ⟨tcb', h ▸ hObj, rfl⟩

end sameSchedContextBindings

/-- IPC de-threading D6: `donationBudgetTransfer` transfers across any transition that
preserves every TCB's `schedContextBinding`.  The frame reads the two witness TCBs'
bindings back into the pre-state, where `donationBudgetTransfer st` rules out the shared
SchedContext. -/
theorem donationBudgetTransfer_of_sameSchedContextBindings
    {st st' : SystemState}
    (hSame : sameSchedContextBindings st st')
    (hDBT : donationBudgetTransfer st) :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hB1 hB2
  obtain ⟨tc1, hP1, hEq1⟩ := hSame tid1 tcb1 h1
  obtain ⟨tc2, hP2, hEq2⟩ := hSame tid2 tcb2 h2
  exact hDBT tid1 tid2 tc1 tc2 scId hP1 hP2 hNe
    (by rw [hEq1]; exact hB1) (by rw [hEq2]; exact hB2)

/-- IPC de-threading D6 (`donationOwnerUnique`): every binding-frame transition preserves
donation-owner uniqueness.  `sameSchedContextBindings` pulls each post-state `.donated _ owner`
back to a pre-state `.donated _ owner` (same owner), so two post-state donations sharing an owner
pull back to two pre-state donations sharing it — equal by `donationOwnerUnique st`. -/
theorem donationOwnerUnique_of_sameSchedContextBindings
    {st st' : SystemState}
    (hSame : sameSchedContextBindings st st')
    (hInv : donationOwnerUnique st) :
    donationOwnerUnique st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  obtain ⟨tc1, hP1, hEq1⟩ := hSame tid1 tcb1 h1
  obtain ⟨tc2, hP2, hEq2⟩ := hSame tid2 tcb2 h2
  exact hInv tid1 tid2 tc1 tc2 scId1 scId2 owner hP1 hP2
    (by rw [hEq1]; exact hB1) (by rw [hEq2]; exact hB2)

/-- IPC de-threading D6 (`donationOwnerValid`): the **forward** half of the preservation
frame, packaged so it composes through a transition's store-op decomposition with
`.trans` exactly the way `sameSchedContextBindings` does for the backward binding half.

`donationOwnerValid` reads, about a donation `tid ↦ .donated scId owner`: the donated
SchedContext `scId` (clause 1's existence + `boundThread`) and the `owner`'s TCB
(clause 2's `.unbound` binding + `.blockedOnReply` state).  Both are read on the
**owner/SchedContext** side, so they must be carried **forward** (`st → st'`):

* `scForward` — every donated SchedContext object survives the step; and
* `ownerForward` — every thread that is `.unbound` and `.blockedOnReply` in the
  pre-state stays `.unbound` and `.blockedOnReply` in the post-state (so it is still a
  valid donation owner).

A transition's `tid`-side binding is pulled **backward** by `sameSchedContextBindings`;
the two together feed `donationOwnerValid_of_frames`. -/
structure donationOwnerFrame (st st' : SystemState) : Prop where
  scForward : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    st'.objects[scId.toObjId]? = some (.schedContext sc)
  ownerForward : ∀ (owner : SeLe4n.ThreadId) (ownerTcb : TCB),
    st.objects[owner.toObjId]? = some (.tcb ownerTcb) →
    ownerTcb.schedContextBinding = .unbound →
    (∃ epId replyTarget, ownerTcb.ipcState = .blockedOnReply epId replyTarget) →
    ∃ ownerTcb', st'.objects[owner.toObjId]? = some (.tcb ownerTcb') ∧
      ownerTcb'.schedContextBinding = .unbound ∧
      ∃ epId replyTarget, ownerTcb'.ipcState = .blockedOnReply epId replyTarget

namespace donationOwnerFrame

/-- Reflexivity: a state frames onto itself. -/
theorem refl (st : SystemState) : donationOwnerFrame st st :=
  ⟨fun _ _ h => h, fun _ ownerTcb h hU hR => ⟨ownerTcb, h, hU, hR⟩⟩

/-- Transitivity: chain two donation-owner frames. -/
theorem trans {st st' st'' : SystemState}
    (h1 : donationOwnerFrame st st') (h2 : donationOwnerFrame st' st'') :
    donationOwnerFrame st st'' :=
  ⟨fun scId sc h => h2.scForward scId sc (h1.scForward scId sc h),
   fun owner ownerTcb h hU hR => by
     obtain ⟨t', h', hU', hR'⟩ := h1.ownerForward owner ownerTcb h hU hR
     exact h2.ownerForward owner t' h' hU' hR'⟩

/-- A step that leaves the object map untouched frames trivially (scheduler-only
ops: `removeRunnable`, `ensureRunnable`, `removeRunnableOnCore`, …). -/
theorem of_objects_eq {st st' : SystemState}
    (hEq : st'.objects = st.objects) : donationOwnerFrame st st' :=
  ⟨fun scId sc h => by rw [hEq]; exact h,
   fun owner ownerTcb h hU hR => ⟨ownerTcb, by rw [hEq]; exact h, hU, hR⟩⟩

end donationOwnerFrame

/-- IPC de-threading D6 (`donationOwnerValid`): the reusable preservation frame.

A transition preserves `donationOwnerValid` whenever it preserves every TCB's
`schedContextBinding` **backward** (`hBind`, to pull a post-state `.donated` binding
back to the pre-state) and frames the SchedContext/owner side **forward**
(`hFrame : donationOwnerFrame`).

Binding-free, SchedContext-free, owner-non-waking transitions (the notification pair,
`endpointSendDual`) discharge `hBind` from the existing `sameSchedContextBindings`
frame and `hFrame` because the only TCBs they rewrite are the running caller / a
freshly-woken `.blockedOnReceive`|`.blockedOnNotification` thread — never a
`.blockedOnReply` donation owner — and they store no SchedContext object.  The
reply/call transitions that *do* wake the owner restore the witness through
`applyReplyDonation` / `applyCallDonation` at the donation-wrapper level, not the
bare transition. -/
theorem donationOwnerValid_of_frames
    {st st' : SystemState}
    (hBind : sameSchedContextBindings st st')
    (hFrame : donationOwnerFrame st st')
    (hInv : donationOwnerValid st) :
    donationOwnerValid st' := by
  intro tid tcb scId owner hTcb hBinding
  obtain ⟨tcbSt, hTcbSt, hBindEq⟩ := hBind tid tcb hTcb
  rw [hBinding] at hBindEq
  obtain ⟨⟨sc, hScSt, hBound⟩, ⟨ownerTcb, hOwnerSt, hUnbound, ep, rt, hReply⟩⟩ :=
    hInv tid tcbSt scId owner hTcbSt hBindEq
  exact ⟨⟨sc, hFrame.scForward scId sc hScSt, hBound⟩,
    hFrame.ownerForward owner ownerTcb hOwnerSt hUnbound ⟨ep, rt, hReply⟩⟩

-- ============================================================================
-- WS-RR RR3.12: `donationOwnerValid`, relaxed at the thread a reply has woken
-- ============================================================================

/-- WS-RR RR3.12: `donationOwnerValid`, **relaxed at one thread**.

`donationOwnerValid` requires every donation owner to be `.blockedOnReply`, which
is the state a donor sits in from its `Call` until the answer arrives.  The
kernel's reply is deliberately *not* atomic in that respect: `endpointReply` wakes
the answered caller `.ready` and the donated SchedContext is handed back
afterwards, by `applyReplyDonation` (`endpointReplyWithDonation`) or
`applyReplyDonationOnCore` (`endpointReplyCrossCoreDispatch`) — the AUD-3 ordering,
because the server needs the donated budget *while* it replies.  Between those two
steps `donationOwnerValid` is **false** of the state whenever the answered call
donated, which is the ordinary seL4-MCS path.

`donationOwnerValidExcept st woken` is what is true there: every clause of
`donationOwnerValid` except that an owner equal to `woken` need not be
`.blockedOnReply` (it is the thread the reply just woke).  Its `.unbound` clause is
kept, so `donationChainAcyclic` still follows — see
`donationOwnerValidExcept_implies_donationChainAcyclic`.

The pair `(donationOwnerValidExcept, donationOwnerValid)` is what lets the reply
chain state honest bundles: the bare reply **establishes** the relaxed form, and the
donation return **upgrades** it back to the full one
(`returnDonatedSchedContext_establishes_donationOwnerValid_of_except`).  Before
RR3.12 the reply bundles instead threaded `donationOwnerValid` on their own
post-state — a hypothesis no state on the donating path satisfies, so those bundles
asserted nothing exactly where the donation machinery runs. -/
def donationOwnerValidExcept (st : SystemState) (woken : SeLe4n.ThreadId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .donated scId owner →
    (∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      sc.boundThread = some tid) ∧
    (∃ ownerTcb, st.objects[owner.toObjId]? = some (.tcb ownerTcb) ∧
      ownerTcb.schedContextBinding = .unbound ∧
      (owner = woken ∨
        ∃ epId replyTarget, ownerTcb.ipcState = .blockedOnReply epId replyTarget))

/-- WS-RR RR3.12: the full invariant is the relaxed one at every `woken`. -/
theorem donationOwnerValidExcept_of_donationOwnerValid
    {st : SystemState} (woken : SeLe4n.ThreadId) (h : donationOwnerValid st) :
    donationOwnerValidExcept st woken := by
  intro tid tcb scId owner hTcb hBind
  obtain ⟨hSc, ownerTcb, hOwner, hUnbound, hReply⟩ := h tid tcb scId owner hTcb hBind
  exact ⟨hSc, ownerTcb, hOwner, hUnbound, Or.inr hReply⟩

/-- WS-RR RR3.12: the relaxed form is the full one once nothing is donated **by**
the relaxed thread — the state the donation return leaves behind, and the state a
reply that carried no donation was in all along. -/
theorem donationOwnerValid_of_except_of_no_donation_owned_by
    {st : SystemState} {woken : SeLe4n.ThreadId}
    (h : donationOwnerValidExcept st woken)
    (hNone : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId woken) :
    donationOwnerValid st := by
  intro tid tcb scId owner hTcb hBind
  obtain ⟨hSc, ownerTcb, hOwner, hUnbound, hCase⟩ := h tid tcb scId owner hTcb hBind
  refine ⟨hSc, ownerTcb, hOwner, hUnbound, ?_⟩
  cases hCase with
  | inl hEq => exact absurd hBind (hEq ▸ hNone tid tcb scId hTcb)
  | inr hReply => exact hReply

/-- WS-RR RR3.12: acyclicity survives the relaxation.  The argument reads only the
owner's `.unbound` binding — `.unbound` and `.donated` are distinct constructors —
and the relaxed form keeps that clause; only the `.blockedOnReply` clause is
dropped. -/
theorem donationOwnerValidExcept_implies_donationChainAcyclic
    (st : SystemState) (woken : SeLe4n.ThreadId)
    (hDOV : donationOwnerValidExcept st woken) :
    donationChainAcyclic st := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 hTcb1 hTcb2 hDon1 hDon2
  obtain ⟨_, ownerTcb, hOwnerTcb, hBound, _⟩ := hDOV tid1 tcb1 scId1 tid2 hTcb1 hDon1
  rw [hTcb2] at hOwnerTcb
  cases hOwnerTcb
  rw [hDon2] at hBound; cases hBound

/-- WS-RR RR3.12: the relaxed invariant depends only on the object store. -/
theorem donationOwnerValidExcept_of_objects_eq {st st' : SystemState}
    {woken : SeLe4n.ThreadId} (hObjs : st'.objects = st.objects)
    (h : donationOwnerValidExcept st woken) : donationOwnerValidExcept st' woken := by
  intro tid tcb scId owner hTcb hBind
  rw [hObjs] at hTcb ⊢
  exact h tid tcb scId owner hTcb hBind

/-- WS-RR RR3.12: the **forward** half of the relaxed preservation frame — the
counterpart of `donationOwnerFrame` for a transition that wakes one thread.

Both clauses `donationOwnerValidExcept` reads on the owner/SchedContext side are
carried forward: every donated SchedContext survives, and every TCB survives with
its `schedContextBinding` intact and — everywhere but at `woken` — its `ipcState`
too.  Stating `tcbForward` over *every* TCB rather than only over owners is what
makes it compose: the reply is three stores, and the thread that is an owner after
one of them need not have been one before it. -/
structure donationOwnerFrameExcept (st st' : SystemState) (woken : SeLe4n.ThreadId) :
    Prop where
  scForward : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
    st.objects[scId.toObjId]? = some (.schedContext sc) →
    st'.objects[scId.toObjId]? = some (.schedContext sc)
  tcbForward : ∀ (t : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[t.toObjId]? = some (.tcb tcb) →
    ∃ tcb', st'.objects[t.toObjId]? = some (.tcb tcb') ∧
      tcb'.schedContextBinding = tcb.schedContextBinding ∧
      (t = woken ∨ tcb'.ipcState = tcb.ipcState)

namespace donationOwnerFrameExcept

/-- Reflexivity: a state frames onto itself. -/
theorem refl (st : SystemState) (woken : SeLe4n.ThreadId) :
    donationOwnerFrameExcept st st woken :=
  ⟨fun _ _ h => h, fun _ tcb h => ⟨tcb, h, rfl, Or.inr rfl⟩⟩

/-- Transitivity: chain two relaxed frames sharing the same relaxed thread. -/
theorem trans {st st' st'' : SystemState} {woken : SeLe4n.ThreadId}
    (h1 : donationOwnerFrameExcept st st' woken)
    (h2 : donationOwnerFrameExcept st' st'' woken) :
    donationOwnerFrameExcept st st'' woken :=
  ⟨fun scId sc h => h2.scForward scId sc (h1.scForward scId sc h),
   fun t tcb h => by
     obtain ⟨tcb1, h1', hB1, hI1⟩ := h1.tcbForward t tcb h
     obtain ⟨tcb2, h2', hB2, hI2⟩ := h2.tcbForward t tcb1 h1'
     refine ⟨tcb2, h2', hB2.trans hB1, ?_⟩
     cases hI1 with
     | inl hw => exact Or.inl hw
     | inr hi1 => cases hI2 with
       | inl hw => exact Or.inl hw
       | inr hi2 => exact Or.inr (hi2.trans hi1)⟩

/-- A step that leaves the object map untouched frames trivially (scheduler-only
ops: `removeRunnable`, `ensureRunnable`, `removeRunnableOnCore`, …). -/
theorem of_objects_eq {st st' : SystemState} {woken : SeLe4n.ThreadId}
    (hEq : st'.objects = st.objects) : donationOwnerFrameExcept st st' woken :=
  ⟨fun _ _ h => by rw [hEq]; exact h,
   fun _ tcb h => ⟨tcb, by rw [hEq]; exact h, rfl, Or.inr rfl⟩⟩

/-- The pointwise form: object lookups that agree everywhere frame trivially.  This
is the shape a cross-core transition's `OffSchedulerAgrees` supplies. -/
theorem of_getElem_eq {st st' : SystemState} {woken : SeLe4n.ThreadId}
    (hEq : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]?) :
    donationOwnerFrameExcept st st' woken :=
  ⟨fun _ _ h => by rw [hEq]; exact h,
   fun _ tcb h => ⟨tcb, by rw [hEq]; exact h, rfl, Or.inr rfl⟩⟩

/-- Every plain donation-owner frame whose TCB side is a pointwise forward map is
also a relaxed frame — the shape a transition that touches no `ipcState` supplies
(`consumeCallerReply`, the queue-link stores). -/
theorem of_tcbForward {st st' : SystemState} {woken : SeLe4n.ThreadId}
    (hSc : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[scId.toObjId]? = some (.schedContext sc) →
      st'.objects[scId.toObjId]? = some (.schedContext sc))
    (hTcb : ∀ (t : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[t.toObjId]? = some (.tcb tcb) →
      ∃ tcb', st'.objects[t.toObjId]? = some (.tcb tcb') ∧
        tcb'.schedContextBinding = tcb.schedContextBinding ∧
        tcb'.ipcState = tcb.ipcState) :
    donationOwnerFrameExcept st st' woken :=
  ⟨hSc, fun t tcb h => by
    obtain ⟨tcb', h', hB, hI⟩ := hTcb t tcb h
    exact ⟨tcb', h', hB, Or.inr hI⟩⟩

end donationOwnerFrameExcept

/-- WS-RR RR3.12: the relaxed counterpart of `donationOwnerValid_of_frames` — the
`tid`-side binding is pulled **backward** by `sameSchedContextBindings`, the
SchedContext/owner side carried **forward** by the relaxed frame. -/
theorem donationOwnerValidExcept_of_frames
    {st st' : SystemState} {woken : SeLe4n.ThreadId}
    (hBind : sameSchedContextBindings st st')
    (hFrame : donationOwnerFrameExcept st st' woken)
    (hInv : donationOwnerValid st) :
    donationOwnerValidExcept st' woken := by
  intro tid tcb scId owner hTcb hBinding
  obtain ⟨tcbSt, hTcbSt, hBindEq⟩ := hBind tid tcb hTcb
  rw [hBinding] at hBindEq
  obtain ⟨⟨sc, hScSt, hBound⟩, ⟨ownerTcb, hOwnerSt, hUnbound, ep, rt, hReply⟩⟩ :=
    hInv tid tcbSt scId owner hTcbSt hBindEq
  obtain ⟨ownerTcb', hOwner', hBind', hCase⟩ := hFrame.tcbForward owner ownerTcb hOwnerSt
  refine ⟨⟨sc, hFrame.scForward scId sc hScSt, hBound⟩,
    ⟨ownerTcb', hOwner', hBind'.trans hUnbound, ?_⟩⟩
  cases hCase with
  | inl hw => exact Or.inl hw
  | inr hi => exact Or.inr ⟨ep, rt, hi.trans hReply⟩

-- ============================================================================
-- Full IPC invariant bundle (16 conjuncts)
-- ============================================================================

/-- Full IPC invariant: conjunction of all sixteen IPC sub-invariants.

Z7 extends the bundle with 4 donation invariants:
- `donationChainAcyclic`: no circular donation chains
- `donationOwnerValid`: donated bindings reference valid objects
- `passiveServerIdle`: unbound non-runnable threads are idle/receiving
- `donationBudgetTransfer`: at most one thread per SchedContext

WS-RC R4.C.7 (close-out C2): the `uniqueWaiters` conjunct previously
listed as the 15th slot was removed when `Notification.waitingThreads`
was promoted from `List ThreadId` to `SeLe4n.NoDupList ThreadId`.  The
per-Notification `List.Nodup` witness is now carried structurally at
construction time via `NoDupList.hNodup`; per-Notification discharge is
direct via `SeLe4n.Kernel.notification_waiters_nodup`.  The bundle now
has 15 conjuncts (was 16); `blockedOnReplyHasTarget` is the 15th.  The
historical `uniqueWaiters` state-level predicate (and its `_holds` /
`_trivial` discharge helpers) were deleted in the close-out. -/
def ipcInvariantCore (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ blockedThreadsPendingMessageConsistent st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValid st ∧
  passiveServerIdle st ∧ donationBudgetTransfer st ∧
  blockedOnReplyHasTarget st

/-- WS-SM SM6.D (PR #822 review): the full IPC invariant — **twenty conjuncts**:
the 15 structural conjuncts (`ipcInvariantCore`) **plus** the bidirectional
`replyCallerLinkage` (16th) tying every `TCB.replyObject` to a reciprocating
`Reply.caller`, **plus** the `pendingReceiveReplyWellFormed` server-first stash
conjunct (17th, PR #822 review 6J9Kjg/6J9Kp6) tying every
`TCB.pendingReceiveReply` to a still-`.blockedOnReceive` server holding a free
existing Reply, **plus** the reply-object hardening trio added during the
SM6.D deep audits (`donationOwnerUnique` 18th,
`endpointQueueTailBlockedConsistent` 19th, `queueNextTargetBlocked` 20th).
The core is split out so the reply-store building blocks (`storeObject_reply` /
`storeObject_tcb_replyObject`) — whose *intermediate* state legitimately breaks the
reciprocal link — can be sequenced through the core before `linkCallerReply` /
`consumeCallerReply` re-establish the linkage on the final state. -/
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ blockedThreadsPendingMessageConsistent st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValid st ∧
  passiveServerIdle st ∧ donationBudgetTransfer st ∧
  blockedOnReplyHasTarget st ∧ replyCallerLinkage st ∧
  pendingReceiveReplyWellFormed st ∧ donationOwnerUnique st ∧
  endpointQueueTailBlockedConsistent st ∧
  queueNextTargetBlocked st


-- ============================================================================
-- WS-OD OD1.3 — the object store, compared **pointwise**
-- ============================================================================

/-- WS-OD OD1.3: two states hold the same object at every key.

This is the pointwise reading of "the object store is unchanged", and it is
strictly weaker than `st'.objects = st.objects`.  The difference is
load-bearing rather than stylistic: the store is a Robin Hood hash table whose
*value* records the probe displacement its insertion order produced, so two
runs that write the same objects to the same keys in a different order agree
here and are **not** equal.  That is exactly the relation between this tree's
two endpoint-queue removals (`endpointQueueRemove_agrees_with_dual`), whose
head branches write the endpoint a different number of times in a different
order.

Nothing in `ipcInvariantFull` can tell the two apart: every one of its twenty
conjuncts reads the store through `getElem?` and nothing else — with the single
exception of `passiveServerIdle`, which also reads the boot core's run queue,
and whose frame therefore names the scheduler as well.

The family below is the pointwise counterpart of the `_of_objects_eq` frames.
Four of those (`endpointQueueNoDup`, `ipcStateQueueMembershipConsistent`,
`queueNextBlockingConsistent`, `queueNextTargetBlocked`) already took a
pointwise hypothesis under the equality name; the rest took the equality.  A
`_of_storeAgrees` wrapper exists for all twenty so a caller need not know which
was which. -/
def objectStoreAgrees (st st' : SystemState) : Prop :=
  ∀ k : SeLe4n.ObjId, st'.objects[k]? = st.objects[k]?

theorem objectStoreAgrees.refl (st : SystemState) : objectStoreAgrees st st :=
  fun _ => rfl

theorem objectStoreAgrees.symm {st st' : SystemState}
    (h : objectStoreAgrees st st') : objectStoreAgrees st' st :=
  fun k => (h k).symm

theorem objectStoreAgrees.trans {st st' st'' : SystemState}
    (h : objectStoreAgrees st st') (h' : objectStoreAgrees st' st'') :
    objectStoreAgrees st st'' :=
  fun k => (h' k).trans (h k)

/-- WS-OD OD1.3: literal store equality is the special case. -/
theorem objectStoreAgrees_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) : objectStoreAgrees st st' :=
  fun k => by rw [hObjs]

theorem ipcInvariant_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : ipcInvariant st) : ipcInvariant st' := by
  intro oid ntfn hL
  rw [hA] at hL
  exact h oid ntfn hL

theorem intrusiveQueueWellFormed_of_storeAgrees {st st' : SystemState}
    {q : IntrusiveQueue}
    (hA : objectStoreAgrees st st') (h : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hEmpty, hHead, hTail⟩ := h
  refine ⟨hEmpty, ?_, ?_⟩
  · intro hd hHd
    obtain ⟨tcb, hTcb, hPrev⟩ := hHead hd hHd
    exact ⟨tcb, by rw [hA]; exact hTcb, hPrev⟩
  · intro tl hTl
    obtain ⟨tcb, hTcb, hNext⟩ := hTail tl hTl
    exact ⟨tcb, by rw [hA]; exact hTcb, hNext⟩

theorem tcbQueueLinkIntegrity_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨hFwd, hRev⟩ := h
  constructor
  · intro a tcbA hAt b hNext
    rw [hA] at hAt
    obtain ⟨tcbB, hB, hPrev⟩ := hFwd a tcbA hAt b hNext
    exact ⟨tcbB, by rw [hA]; exact hB, hPrev⟩
  · intro b tcbB hB a hPrev
    rw [hA] at hB
    obtain ⟨tcbA, hAt, hNext⟩ := hRev b tcbB hB a hPrev
    exact ⟨tcbA, by rw [hA]; exact hAt, hNext⟩

theorem QueueNextPath_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath st' a b) : QueueNextPath st a b := by
  induction hp with
  | single x y tcbA hObj hNext =>
    exact .single x y tcbA (by rw [← hA]; exact hObj) hNext
  | cons x y z tcbA hObj hNext _ ih =>
    exact .cons x y z tcbA (by rw [← hA]; exact hObj) hNext ih

theorem tcbQueueChainAcyclic_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : tcbQueueChainAcyclic st) :
    tcbQueueChainAcyclic st' :=
  fun tid hp => h tid (QueueNextPath_of_storeAgrees hA hp)

theorem dualQueueSystemInvariant_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEp, hLinks, hAcyc⟩ := h
  refine ⟨?_, tcbQueueLinkIntegrity_of_storeAgrees hA hLinks,
    tcbQueueChainAcyclic_of_storeAgrees hA hAcyc⟩
  intro epId ep hLk
  have hLk0 : st.objects[epId]? = some (.endpoint ep) := by rw [← hA]; exact hLk
  have := hEp epId ep hLk0
  unfold dualQueueEndpointWellFormed at this ⊢
  rw [hLk]; rw [hLk0] at this
  exact ⟨intrusiveQueueWellFormed_of_storeAgrees hA this.1,
    intrusiveQueueWellFormed_of_storeAgrees hA this.2⟩

theorem allPendingMessagesBounded_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro tid tcb msg hTcb hMsg
  rw [hA] at hTcb
  exact h tid tcb msg hTcb hMsg

theorem badgeWellFormed_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : badgeWellFormed st) :
    badgeWellFormed st' :=
  ⟨fun oid ntfn badge hLk hP => h.1 oid ntfn badge (by rw [hA] at hLk; exact hLk) hP,
   fun oid cn slot cap badge hLk hS hB =>
     h.2 oid cn slot cap badge (by rw [hA] at hLk; exact hLk) hS hB⟩

theorem blockedThreadsPendingMessageConsistent_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st')
    (h : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent st' := by
  intro tid tcb hTcb
  rw [hA] at hTcb
  exact h tid tcb hTcb

theorem queueHeadBlockedConsistent_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent st' := by
  intro epId ep hd tcb hEp hTcb
  rw [hA] at hEp hTcb
  exact h epId ep hd tcb hEp hTcb

theorem blockedThreadTimeoutConsistent_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : blockedThreadTimeoutConsistent st) :
    blockedThreadTimeoutConsistent st' := by
  intro tid tcb scId hTcb hBudget
  rw [hA] at hTcb
  obtain ⟨⟨sc, hSc⟩, hBlocked⟩ := h tid tcb scId hTcb hBudget
  exact ⟨⟨sc, by rw [hA]; exact hSc⟩, hBlocked⟩

theorem donationChainAcyclic_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : donationChainAcyclic st) :
    donationChainAcyclic st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  rw [hA] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

theorem donationOwnerValid_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : donationOwnerValid st) :
    donationOwnerValid st' := by
  intro tid tcb scId owner hTcb hBind
  rw [hA] at hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ownerTcb, hOwner, hUnbound, hBlk⟩ :=
    h tid tcb scId owner hTcb hBind
  exact ⟨⟨sc, by rw [hA]; exact hSc, hBound⟩,
    ownerTcb, by rw [hA]; exact hOwner, hUnbound, hBlk⟩

/-- WS-OD OD1.3: the one bundle conjunct an object-store frame alone cannot
carry.  `passiveServerIdle`'s two guards read the boot core's run queue and
current slot, so a step that emptied the run queue would satisfy the
*hypothesis* at threads the pre-state never covered.  Naming the scheduler is
not a formality: a scheduler-writing step owes the conjunct its own proof. -/
theorem passiveServerIdle_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (hSched : st'.scheduler = st.scheduler)
    (h : passiveServerIdle st) : passiveServerIdle st' := by
  intro tid tcb hTcb hUnbound hNotQueued hNotCurrent
  rw [hA] at hTcb
  rw [hSched] at hNotQueued hNotCurrent
  exact h tid tcb hTcb hUnbound hNotQueued hNotCurrent

theorem donationBudgetTransfer_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : donationBudgetTransfer st) :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2
  rw [hA] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2

theorem blockedOnReplyHasTarget_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk
  rw [hA] at hTcb
  exact h tid tcb ep rt hTcb hBlk

theorem replyCallerLinkage_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : replyCallerLinkage st) :
    replyCallerLinkage st' := by
  obtain ⟨⟨hFwd, hBwd⟩, hHas⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro tid tcb rid hTcb hRep
    rw [hA] at hTcb
    obtain ⟨r, hR, hCaller⟩ := hFwd tid tcb rid hTcb hRep
    exact ⟨r, by rw [hA]; exact hR, hCaller⟩
  · intro rid r tid hR hCaller
    rw [hA] at hR
    obtain ⟨tcb, hTcb, hRep, ep, rt, hBlk⟩ := hBwd rid r tid hR hCaller
    exact ⟨tcb, by rw [hA]; exact hTcb, hRep, ep, rt, hBlk⟩
  · intro tid tcb ep rt hTcb hBlk
    rw [hA] at hTcb
    exact hHas tid tcb ep rt hTcb hBlk

theorem pendingReceiveReplyWellFormed_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed st' := by
  obtain ⟨hWf, hInj⟩ := h
  constructor
  · intro tid tcb rid hTcb hStash
    unfold SystemState.getTcb? at hTcb
    rw [hA] at hTcb
    obtain ⟨hRecv, r, hR, hCaller⟩ := hWf tid tcb rid hTcb hStash
    refine ⟨hRecv, r, ?_, hCaller⟩
    unfold SystemState.getReply? at hR ⊢
    rw [hA]; exact hR
  · intro tid1 tid2 tcb1 tcb2 rid hT1 hT2 hS1 hS2
    unfold SystemState.getTcb? at hT1 hT2
    rw [hA] at hT1 hT2
    exact hInj tid1 tid2 tcb1 tcb2 rid hT1 hT2 hS1 hS2

theorem donationOwnerUnique_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : donationOwnerUnique st) :
    donationOwnerUnique st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  rw [hA] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

theorem endpointQueueTailBlockedConsistent_of_storeAgrees {st st' : SystemState}
    (hA : objectStoreAgrees st st') (h : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent st' := by
  intro epId ep tl tcb hEp hTcb
  rw [hA] at hEp hTcb
  exact h epId ep tl tcb hEp hTcb

/-- WS-RR RR3.12: `ipcInvariantFull` with `donationOwnerValid` relaxed at one
thread — the honest post-state of a **bare** reply delivery.

The reply wakes the answered caller before the donated SchedContext is handed
back (see `donationOwnerValidExcept` for why that ordering is deliberate), so on
the donating path no state between the two steps satisfies `ipcInvariantFull`.
This is what such a state does satisfy: nineteen conjuncts unchanged, and
`donationOwnerValid` relaxed exactly at the woken caller.

`donationChainAcyclic` is kept at full strength — it follows from the relaxed form
too (`donationOwnerValidExcept_implies_donationChainAcyclic`), because the
relaxation drops only the owner's `.blockedOnReply` clause and acyclicity reads its
`.unbound` one.

Use `ipcInvariantFull_of_exceptDonationOwner` to recover the full bundle once the
donation return has run, or once it is known that nothing was donated by the woken
thread. -/
def ipcInvariantFullExceptDonationOwner (st : SystemState) (woken : SeLe4n.ThreadId) :
    Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ blockedThreadsPendingMessageConsistent st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValidExcept st woken ∧
  passiveServerIdle st ∧ donationBudgetTransfer st ∧
  blockedOnReplyHasTarget st ∧ replyCallerLinkage st ∧
  pendingReceiveReplyWellFormed st ∧ donationOwnerUnique st ∧
  endpointQueueTailBlockedConsistent st ∧
  queueNextTargetBlocked st

/-- WS-RR RR3.12: the full bundle relaxes at every thread. -/
theorem ipcInvariantFullExceptDonationOwner_of_full {st : SystemState}
    (woken : SeLe4n.ThreadId) (h : ipcInvariantFull st) :
    ipcInvariantFullExceptDonationOwner st woken :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
   donationOwnerValidExcept_of_donationOwnerValid woken h.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- WS-RR RR3.12: the relaxed bundle plus the full `donationOwnerValid` is the full
bundle.  The donation return supplies the second argument
(`returnDonatedSchedContext_establishes_donationOwnerValid_of_except`); so does
`donationOwnerValid_of_except_of_no_donation_owned_by` on a reply that carried no
donation. -/
theorem ipcInvariantFull_of_exceptDonationOwner {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken)
    (hDOV : donationOwnerValid st) :
    ipcInvariantFull st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, hDOV,
   h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- WS-RR RR3.12: the relaxed bundle's own `donationOwnerValidExcept` projection. -/
theorem ipcInvariantFullExceptDonationOwner.donationOwnerValidExcept
    {st : SystemState} {woken : SeLe4n.ThreadId}
    (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.donationOwnerValidExcept st woken :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- WS-RR RR3.12: the relaxed bundle's `donationOwnerUnique` projection — the
companion the donation return needs alongside the relaxed validity. -/
theorem ipcInvariantFullExceptDonationOwner.donationOwnerUnique
    {st : SystemState} {woken : SeLe4n.ThreadId}
    (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.donationOwnerUnique st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- WS-RR RR3.12: the relaxed bundle's remaining named projections — the same
surface `ipcInvariantFull` exposes, minus the one conjunct that is relaxed. -/
theorem ipcInvariantFullExceptDonationOwner.ipcInvariant {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.ipcInvariant st := h.1
theorem ipcInvariantFullExceptDonationOwner.dualQueueSystemInvariant {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.dualQueueSystemInvariant st := h.2.1
theorem ipcInvariantFullExceptDonationOwner.allPendingMessagesBounded {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.allPendingMessagesBounded st := h.2.2.1
theorem ipcInvariantFullExceptDonationOwner.badgeWellFormed {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.badgeWellFormed st := h.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.blockedThreadsPendingMessageConsistent {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st := h.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.endpointQueueNoDup {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.endpointQueueNoDup st := h.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.ipcStateQueueMembershipConsistent {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.ipcStateQueueMembershipConsistent st := h.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.queueNextBlockingConsistent {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.queueNextBlockingConsistent st := h.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.queueHeadBlockedConsistent {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.queueHeadBlockedConsistent st := h.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.blockedThreadTimeoutConsistent {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.blockedThreadTimeoutConsistent st := h.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.donationChainAcyclic {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.donationChainAcyclic st := h.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.passiveServerIdle {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.passiveServerIdle st := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.donationBudgetTransfer {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.donationBudgetTransfer st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.blockedOnReplyHasTarget {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.blockedOnReplyHasTarget st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.replyCallerLinkage {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.replyCallerLinkage st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.pendingReceiveReplyWellFormed {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.pendingReceiveReplyWellFormed st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.endpointQueueTailBlockedConsistent {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.endpointQueueTailBlockedConsistent st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ipcInvariantFullExceptDonationOwner.queueNextTargetBlocked {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    _root_.SeLe4n.Kernel.queueNextTargetBlocked st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- WS-SM SM6.D (PR #822 review): the structural core is exactly the first 15
conjuncts of `ipcInvariantFull`. -/
theorem ipcInvariantFull.toCore {st : SystemState} (h : ipcInvariantFull st) :
    ipcInvariantCore st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- WS-SM SM6.D (PR #822 review): assemble `ipcInvariantFull` from its structural
core plus the reply linkage and the server-first stash well-formedness — the seam
the reply mutators use (core preserved by the object stores, `replyCallerLinkage`
re-established by `linkCallerReply` / `consumeCallerReply`, and
`pendingReceiveReplyWellFormed` framed/established on the final state). -/
theorem ipcInvariantFull_of_core_replyCallerLinkage {st : SystemState}
    (hCore : ipcInvariantCore st) (hLink : replyCallerLinkage st)
    (hPRR : pendingReceiveReplyWellFormed st) (hUnique : donationOwnerUnique st)
    (hTail : endpointQueueTailBlockedConsistent st)
    (hQNTB : queueNextTargetBlocked st) :
    ipcInvariantFull st :=
  ⟨hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2.1, hCore.2.2.2.2.1,
   hCore.2.2.2.2.2.1, hCore.2.2.2.2.2.2.1, hCore.2.2.2.2.2.2.2.1,
   hCore.2.2.2.2.2.2.2.2.1, hCore.2.2.2.2.2.2.2.2.2.1,
   hCore.2.2.2.2.2.2.2.2.2.2.1, hCore.2.2.2.2.2.2.2.2.2.2.2.1,
   hCore.2.2.2.2.2.2.2.2.2.2.2.2.1, hCore.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hCore.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hLink, hPRR, hUnique, hTail, hQNTB⟩

-- ============================================================================
-- AN3-B (IPC-M01 / Theme 4.2): Named-projection refactor for ipcInvariantFull.
--
-- The legacy tuple form above is preserved as the primary definition so
-- every existing consumer that destructures `ipcInvariantFull` via tuple
-- projections continues to typecheck.  The block below layers a named
-- `structure IpcInvariantFull` over the same conjuncts (twenty at
-- v0.32.58: 15 structural post-R4.C.7 — `uniqueWaiters` retired — plus
-- the reply-linkage/stash/hardening quintet added through the SM6.D
-- reply-object audits), a
-- bidirectional `ipcInvariantFull_iff_IpcInvariantFull` bridge, and
-- per-field projection theorems (installed as `@[simp]`) so callers
-- can write `hInv.donationOwnerValid` (or any other conjunct name) in
-- place of the fragile `hInv.2.2.2.2.2.2.2.2.2.2.2.1` chain.
--
-- The projection theorems live in the `SeLe4n.Kernel.ipcInvariantFull`
-- namespace so that Lean 4 dot notation (`h.foo` elaborates to
-- `SeLe4n.Kernel.ipcInvariantFull.foo h` when `h : ipcInvariantFull st`)
-- dispatches through the named accessor without any caller-visible type
-- change. AN3-B.3 (swap primary type to `IpcInvariantFull`) and AN3-B.6
-- (delete the tuple form) are separate follow-up commits; landing the
-- named-projection layer first keeps the cascade shallow.
-- ============================================================================

/-- AN3-B.1: Named-field counterpart of `ipcInvariantFull`.

All 15 fields mirror the conjuncts of the legacy tuple form, one-for-one
in declaration order (the 15th-slot `uniqueWaiters` conjunct was retired
in the WS-RC R4.C.7 close-out, leaving `blockedOnReplyHasTarget` as the
final field). The bidirectional bridge
`ipcInvariantFull_iff_IpcInvariantFull` establishes that the two Prop-level
forms are interchangeable; new theorems should prefer this structure because
adding or removing a conjunct (a frequent audit-remediation operation) only
requires editing the field list here rather than every `.2.2...2.1`
projection site across the codebase. -/
structure IpcInvariantFull (st : SystemState) : Prop where
  ipcInvariant : ipcInvariant st
  dualQueueSystemInvariant : dualQueueSystemInvariant st
  allPendingMessagesBounded : allPendingMessagesBounded st
  badgeWellFormed : badgeWellFormed st
  blockedThreadsPendingMessageConsistent : blockedThreadsPendingMessageConsistent st
  endpointQueueNoDup : endpointQueueNoDup st
  ipcStateQueueMembershipConsistent : ipcStateQueueMembershipConsistent st
  queueNextBlockingConsistent : queueNextBlockingConsistent st
  queueHeadBlockedConsistent : queueHeadBlockedConsistent st
  blockedThreadTimeoutConsistent : blockedThreadTimeoutConsistent st
  donationChainAcyclic : donationChainAcyclic st
  donationOwnerValid : donationOwnerValid st
  passiveServerIdle : passiveServerIdle st
  donationBudgetTransfer : donationBudgetTransfer st
  blockedOnReplyHasTarget : blockedOnReplyHasTarget st
  replyCallerLinkage : replyCallerLinkage st
  pendingReceiveReplyWellFormed : pendingReceiveReplyWellFormed st
  donationOwnerUnique : donationOwnerUnique st
  endpointQueueTailBlockedConsistent : endpointQueueTailBlockedConsistent st
  queueNextTargetBlocked : queueNextTargetBlocked st

namespace ipcInvariantFull

/-! ### AN3-B.2: `@[simp]` projection abbrevs for the tuple form.

Each theorem projects one conjunct from a proof of `ipcInvariantFull st`.
The `@[simp]` attribute lets `simp_all` collapse long projection chains to
the named form automatically.  Dot notation on a hypothesis `hInv :
ipcInvariantFull st` resolves to these via `SeLe4n.Kernel.ipcInvariantFull`
namespace lookup, so `hInv.donationOwnerValid` is accepted by the
elaborator. -/

@[simp] theorem ipcInvariant {st : SystemState}
    (h : ipcInvariantFull st) : _root_.SeLe4n.Kernel.ipcInvariant st :=
  h.1

@[simp] theorem dualQueueSystemInvariant {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.dualQueueSystemInvariant st :=
  h.2.1

@[simp] theorem allPendingMessagesBounded {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.allPendingMessagesBounded st :=
  h.2.2.1

@[simp] theorem badgeWellFormed {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.badgeWellFormed st :=
  h.2.2.2.1

@[simp] theorem blockedThreadsPendingMessageConsistent {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st :=
  h.2.2.2.2.1

@[simp] theorem endpointQueueNoDup {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.endpointQueueNoDup st :=
  h.2.2.2.2.2.1

@[simp] theorem ipcStateQueueMembershipConsistent {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.ipcStateQueueMembershipConsistent st :=
  h.2.2.2.2.2.2.1

@[simp] theorem queueNextBlockingConsistent {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.queueNextBlockingConsistent st :=
  h.2.2.2.2.2.2.2.1

@[simp] theorem queueHeadBlockedConsistent {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.queueHeadBlockedConsistent st :=
  h.2.2.2.2.2.2.2.2.1

@[simp] theorem blockedThreadTimeoutConsistent {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.blockedThreadTimeoutConsistent st :=
  h.2.2.2.2.2.2.2.2.2.1

@[simp] theorem donationChainAcyclic {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.donationChainAcyclic st :=
  h.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem donationOwnerValid {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.donationOwnerValid st :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem passiveServerIdle {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.passiveServerIdle st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem donationBudgetTransfer {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.donationBudgetTransfer st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem blockedOnReplyHasTarget {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.blockedOnReplyHasTarget st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem replyCallerLinkage {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.replyCallerLinkage st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem pendingReceiveReplyWellFormed {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.pendingReceiveReplyWellFormed st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem donationOwnerUnique {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.donationOwnerUnique st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem endpointQueueTailBlockedConsistent {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.endpointQueueTailBlockedConsistent st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem queueNextTargetBlocked {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.queueNextTargetBlocked st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ipcInvariantFull

/- WS-SM SM6.D (PR #822 review): named projections for the structural core
(`ipcInvariantCore` = the first 15 conjuncts of `ipcInvariantFull`), so the
reply-store building blocks can read `hInv.ipcInvariant` etc. on a core hypothesis. -/
namespace ipcInvariantCore

theorem ipcInvariant {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.ipcInvariant st := h.1
theorem dualQueueSystemInvariant {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.dualQueueSystemInvariant st := h.2.1
theorem allPendingMessagesBounded {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.allPendingMessagesBounded st := h.2.2.1
theorem badgeWellFormed {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.badgeWellFormed st := h.2.2.2.1
theorem blockedThreadsPendingMessageConsistent {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st := h.2.2.2.2.1
theorem endpointQueueNoDup {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.endpointQueueNoDup st := h.2.2.2.2.2.1
theorem ipcStateQueueMembershipConsistent {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.ipcStateQueueMembershipConsistent st := h.2.2.2.2.2.2.1
theorem queueNextBlockingConsistent {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.queueNextBlockingConsistent st := h.2.2.2.2.2.2.2.1
theorem queueHeadBlockedConsistent {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.queueHeadBlockedConsistent st := h.2.2.2.2.2.2.2.2.1
theorem blockedThreadTimeoutConsistent {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.blockedThreadTimeoutConsistent st := h.2.2.2.2.2.2.2.2.2.1
theorem donationChainAcyclic {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.donationChainAcyclic st := h.2.2.2.2.2.2.2.2.2.2.1
theorem donationOwnerValid {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.donationOwnerValid st := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem passiveServerIdle {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.passiveServerIdle st := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem donationBudgetTransfer {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.donationBudgetTransfer st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem blockedOnReplyHasTarget {st : SystemState} (h : ipcInvariantCore st) :
    _root_.SeLe4n.Kernel.blockedOnReplyHasTarget st := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ipcInvariantCore

/-- WS-RR RR3.12: `ipcInvariantCore` **minus the four donation conjuncts** —
exactly what `ipcInvariantCore_of_nonBindingAgreements` reads of its pre-state.

That transport carries the eleven binding-free conjuncts across a
donation-read agreement and takes the four donation ones (`donationChainAcyclic`,
`donationOwnerValid`, `passiveServerIdle`, `donationBudgetTransfer`) at the
**post**-state, so it never touches their pre-state versions.  Naming the eleven
it does read lets the donation return run from a pre-state whose
`donationOwnerValid` is relaxed — which is the state a reply leaves behind, and
therefore the state the reply chain's composite bundles have to start from. -/
def ipcInvariantCoreNonDonation (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ blockedThreadsPendingMessageConsistent st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  blockedOnReplyHasTarget st

namespace ipcInvariantCoreNonDonation

theorem ipcInvariant {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.ipcInvariant st := h.1
theorem dualQueueSystemInvariant {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.dualQueueSystemInvariant st := h.2.1
theorem allPendingMessagesBounded {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.allPendingMessagesBounded st := h.2.2.1
theorem badgeWellFormed {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.badgeWellFormed st := h.2.2.2.1
theorem blockedThreadsPendingMessageConsistent {st : SystemState}
    (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st := h.2.2.2.2.1
theorem endpointQueueNoDup {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.endpointQueueNoDup st := h.2.2.2.2.2.1
theorem ipcStateQueueMembershipConsistent {st : SystemState}
    (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.ipcStateQueueMembershipConsistent st := h.2.2.2.2.2.2.1
theorem queueNextBlockingConsistent {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.queueNextBlockingConsistent st := h.2.2.2.2.2.2.2.1
theorem queueHeadBlockedConsistent {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.queueHeadBlockedConsistent st := h.2.2.2.2.2.2.2.2.1
theorem blockedThreadTimeoutConsistent {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.blockedThreadTimeoutConsistent st := h.2.2.2.2.2.2.2.2.2.1
theorem blockedOnReplyHasTarget {st : SystemState} (h : ipcInvariantCoreNonDonation st) :
    _root_.SeLe4n.Kernel.blockedOnReplyHasTarget st := h.2.2.2.2.2.2.2.2.2.2

end ipcInvariantCoreNonDonation

/-- WS-RR RR3.12: the structural core drops its donation conjuncts. -/
theorem ipcInvariantCoreNonDonation_of_core {st : SystemState} (h : ipcInvariantCore st) :
    ipcInvariantCoreNonDonation st :=
  ⟨h.ipcInvariant, h.dualQueueSystemInvariant, h.allPendingMessagesBounded,
   h.badgeWellFormed, h.blockedThreadsPendingMessageConsistent, h.endpointQueueNoDup,
   h.ipcStateQueueMembershipConsistent, h.queueNextBlockingConsistent,
   h.queueHeadBlockedConsistent, h.blockedThreadTimeoutConsistent,
   h.blockedOnReplyHasTarget⟩

/-- WS-RR RR3.12: the relaxed bundle contains the eleven binding-free conjuncts
outright — the relaxation touches only `donationOwnerValid`. -/
theorem ipcInvariantCoreNonDonation_of_exceptDonationOwner {st : SystemState}
    {woken : SeLe4n.ThreadId} (h : ipcInvariantFullExceptDonationOwner st woken) :
    ipcInvariantCoreNonDonation st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- AN3-B.1 bridge: `ipcInvariantFull` (tuple form) and `IpcInvariantFull`
(named-field form) are logically equivalent.  Proven by constructor-then-
cases so adding or removing a conjunct in both forms keeps the bridge
mechanical. -/
theorem ipcInvariantFull_iff_IpcInvariantFull (st : SystemState) :
    ipcInvariantFull st ↔ IpcInvariantFull st := by
  constructor
  · intro h
    exact ⟨h.ipcInvariant, h.dualQueueSystemInvariant,
           h.allPendingMessagesBounded, h.badgeWellFormed,
           h.blockedThreadsPendingMessageConsistent, h.endpointQueueNoDup,
           h.ipcStateQueueMembershipConsistent,
           h.queueNextBlockingConsistent, h.queueHeadBlockedConsistent,
           h.blockedThreadTimeoutConsistent, h.donationChainAcyclic,
           h.donationOwnerValid, h.passiveServerIdle,
           h.donationBudgetTransfer,
           h.blockedOnReplyHasTarget, h.replyCallerLinkage,
           h.pendingReceiveReplyWellFormed, h.donationOwnerUnique,
           h.endpointQueueTailBlockedConsistent, h.queueNextTargetBlocked⟩
  · intro h
    exact ⟨h.ipcInvariant, h.dualQueueSystemInvariant,
           h.allPendingMessagesBounded, h.badgeWellFormed,
           h.blockedThreadsPendingMessageConsistent, h.endpointQueueNoDup,
           h.ipcStateQueueMembershipConsistent,
           h.queueNextBlockingConsistent, h.queueHeadBlockedConsistent,
           h.blockedThreadTimeoutConsistent, h.donationChainAcyclic,
           h.donationOwnerValid, h.passiveServerIdle,
           h.donationBudgetTransfer,
           h.blockedOnReplyHasTarget, h.replyCallerLinkage,
           h.pendingReceiveReplyWellFormed, h.donationOwnerUnique,
           h.endpointQueueTailBlockedConsistent, h.queueNextTargetBlocked⟩

/-- AN3-B.1: forward direction of the bridge, as a convenience coercion.
Used by callers that prefer the named-field form. -/
theorem ipcInvariantFull.toStruct {st : SystemState}
    (h : ipcInvariantFull st) : IpcInvariantFull st :=
  (ipcInvariantFull_iff_IpcInvariantFull st).mp h

/-- AN3-B.1: backward direction of the bridge. -/
theorem IpcInvariantFull.toTuple {st : SystemState}
    (h : IpcInvariantFull st) : ipcInvariantFull st :=
  (ipcInvariantFull_iff_IpcInvariantFull st).mpr h

-- ============================================================================
-- AI4-A (M-01): Frame lemmas for cleanupPreReceiveDonation
--
-- cleanupPreReceiveDonation only modifies schedContextBinding on TCBs and
-- boundThread on a SchedContext, via returnDonatedSchedContext. In 3 of 4
-- branches it returns st unchanged. These frame lemmas establish that the
-- cleanup is transparent to all IPC and scheduler invariants.
-- ============================================================================

/-- AI4-A: cleanupPreReceiveDonation preserves scheduler state. -/
theorem cleanupPreReceiveDonation_scheduler_eq
    (st : SystemState) (receiver : SeLe4n.ThreadId) :
    (cleanupPreReceiveDonation st receiver).scheduler = st.scheduler := by
  unfold cleanupPreReceiveDonation
  cases hTcb : lookupTcb st receiver with
  | none => rfl
  | some recvTcb =>
    simp only []
    cases recvTcb.schedContextBinding with
    | unbound => rfl
    | bound _ => rfl
    | donated scId originalOwner =>
      simp only []
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => rfl
      | ok st' =>
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        exact returnDonatedSchedContext_scheduler_eq st st' receiver scId originalOwner n hPop

/-- AI4-A: cleanupPreReceiveDonation preserves objects.invExt. -/
theorem cleanupPreReceiveDonation_preserves_objects_invExt
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    (cleanupPreReceiveDonation st receiver).objects.invExt := by
  unfold cleanupPreReceiveDonation
  cases hTcb : lookupTcb st receiver with
  | none => exact hObjInv
  | some recvTcb =>
    simp only []
    cases recvTcb.schedContextBinding with
    | unbound => exact hObjInv
    | bound _ => exact hObjInv
    | donated scId originalOwner =>
      simp only []
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => exact hObjInv
      | ok st' =>
        -- WS-OD OD3.2: delegate rather than re-run the operation's case analysis,
        -- which the pop's fourth store made non-compiling here.
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        exact returnDonatedSchedContext_preserves_objects_invExt' st st' receiver scId
          originalOwner n hObjInv hPop

-- Helper: common proof pattern for cleanupPreReceiveDonation frame lemmas.
-- 3 of 4 branches return st unchanged. The donated+ok branch delegates to
-- returnDonatedSchedContext which only modifies TCB schedContextBinding and
-- SchedContext boundThread — transparent to all IPC/scheduler invariants.
theorem cleanupPreReceiveDonation_frame_helper
    {P : SystemState → Prop}
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hInv : P st)
    (hReturn : ∀ (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
      (newOwner? : Option SeLe4n.ThreadId) (st' : SystemState),
      returnDonatedSchedContext st receiver scId originalOwner newOwner? = .ok st' → P st') :
    P (cleanupPreReceiveDonation st receiver) := by
  unfold cleanupPreReceiveDonation
  cases lookupTcb st receiver with
  | none => exact hInv
  | some recvTcb =>
    simp only []
    cases recvTcb.schedContextBinding with
    | unbound => exact hInv
    | bound _ => exact hInv
    | donated scId originalOwner =>
      simp only []
      cases hRet : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => exact hInv
      | ok st' =>
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact hReturn scId originalOwner n st' hPop

-- Helper: returnDonatedSchedContext only stores TCB/SchedContext objects.
-- For any invariant quantified over non-TCB/non-SchedContext objects (endpoints,
-- notifications), the invariant is trivially preserved because those objects
-- are unchanged by storeObject on different-typed ObjIds.
-- This is proven via storeObject's insert semantics on the RHTable.

/-- AI4-A: returnDonatedSchedContext preserves objects.invExt.
(WS-SM SM6.E: promoted from `private` — the cancellation invariant surface
consumes it for `cancelDonatedDonation_preserves_objects_invExt`, via
`cleanupDonatedSchedContext_preserves_objects_invExt`.) -/
theorem returnDonatedSchedContext_preserves_objects_invExt
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.objects.invExt :=
  -- WS-OD OD3.2: the pop's fourth store made a fifth copy of the operation's
  -- case analysis non-compiling; this is the shared derivation instead.
  returnDonatedSchedContext_preserves_objects_invExt'
    st st' serverTid scId originalOwner newOwner? hObjInv h

/-- AI4-A: Backward transport — notifications are unchanged by returnDonatedSchedContext.
returnDonatedSchedContext stores 1 SchedContext + 2 TCBs. A notification in the
post-state must have been in the pre-state because storeObject on non-notification
ObjIds cannot create notification objects. -/
theorem returnDonatedSchedContext_notification_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) :=
  -- WS-OD OD3.2: an instance of the shared kind frame — the donation return
  -- writes a SchedContext, a Reply and two TCBs, so a notification in the
  -- post-state was never one of its targets.
  returnDonatedSchedContext_objects_backward_of_kind st st' serverTid scId originalOwner
    newOwner? hObjInv h oid _ (donationReturnWritesKind_notification ntfn) hNtfn

/-- AI4-A: TCB forward transport through cleanupPreReceiveDonation.
If a TCB exists at `tid.toObjId` in `st`, some TCB still exists there after cleanup.
The cleanup stores TCBs at receiver/owner ObjIds (preserving TCB-ness) and a
SchedContext at scId.toObjId. For any `tid` whose ObjId is distinct from all three
(or equals a TCB-stored target), a TCB still exists. -/
theorem cleanupPreReceiveDonation_tcb_forward
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ∃ tcb', (cleanupPreReceiveDonation st receiver).objects[tid.toObjId]? = some (.tcb tcb') := by
  unfold cleanupPreReceiveDonation
  cases hLookup : lookupTcb st receiver with
  | none => exact hTcb
  | some recvTcb =>
    simp only []
    cases recvTcb.schedContextBinding with
    | unbound => exact hTcb
    | bound _ => exact hTcb
    | donated scId originalOwner =>
      simp only []
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => exact hTcb
      | ok st' =>
        -- WS-OD OD3.2: a TCB stays a TCB because the donation return rewrites one
        -- binding field and never changes an object's kind — the shared rewrite,
        -- rather than a per-store case analysis that a fourth store invalidates.
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        obtain ⟨tcb, hPre⟩ := hTcb
        obtain ⟨tcb', hPost, _⟩ :=
          returnDonatedSchedContext_tcb_rewrite st st' receiver scId originalOwner
            hObjInv n hPop tid.toObjId tcb hPre
        exact ⟨tcb', hPost⟩

/-- AI4-A: TCB ipcState backward transport through cleanupPreReceiveDonation.
If a TCB exists in the cleaned state, there's a TCB in the original state with
the same ipcState. This holds because cleanupPreReceiveDonation only modifies
schedContextBinding, not ipcState. -/
theorem cleanupPreReceiveDonation_tcb_ipcState_backward
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (tid : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : (cleanupPreReceiveDonation st receiver).objects[tid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  unfold cleanupPreReceiveDonation at hTcb'
  cases hLookup : lookupTcb st receiver with
  | none => simp only [hLookup] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
  | some recvTcb =>
    simp only [hLookup] at hTcb'
    cases hBinding : recvTcb.schedContextBinding with
    | unbound => simp only [hBinding] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
    | bound _ => simp only [hBinding] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
    | donated scId originalOwner =>
      simp only [hBinding] at hTcb'
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => simp only [hReturn] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
      | ok st' =>
        simp only [hReturn] at hTcb'
        -- WS-OD OD3.2: the shared TCB rewrite backward, rather than a copy of the
        -- operation's per-store case analysis.
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        obtain ⟨tcb, hPre, sb, rfl⟩ :=
          returnDonatedSchedContext_tcb_rewrite_backward st st' receiver scId originalOwner
            n hObjInv hPop tid.toObjId tcb' hTcb'
        exact ⟨tcb, hPre, rfl⟩

/-- AI4-A: Backward transport — endpoints are unchanged by returnDonatedSchedContext.
returnDonatedSchedContext stores 1 SchedContext + 2 TCBs. An endpoint in the
post-state must have been in the pre-state because storeObject on non-endpoint
ObjIds cannot create endpoint objects. -/
theorem returnDonatedSchedContext_endpoint_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) :=
  -- WS-OD OD3.2: an instance of the shared kind frame.
  returnDonatedSchedContext_objects_backward_of_kind st st' serverTid scId originalOwner
    newOwner? hObjInv h oid _ (donationReturnWritesKind_endpoint ep) hEp

/-- AI4-A: Endpoint backward transport through cleanupPreReceiveDonation.
If an endpoint exists at oid in the cleaned state, it existed identically in
the original state. This holds because cleanupPreReceiveDonation only stores
TCB and SchedContext objects. -/
theorem cleanupPreReceiveDonation_endpoint_backward
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : (cleanupPreReceiveDonation st receiver).objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  exact cleanupPreReceiveDonation_frame_helper (P := fun s => s.objects[oid]? = some (.endpoint ep) → st.objects[oid]? = some (.endpoint ep))
    st receiver (fun h => h)
    (fun scId originalOwner newOwner? st' hRet hEp' =>
      returnDonatedSchedContext_endpoint_backward st st' receiver scId originalOwner hObjInv
        newOwner? hRet oid ep hEp')
    hEp

/-- AI4-A: Backward transport — CNodes are unchanged by returnDonatedSchedContext.
returnDonatedSchedContext stores 1 SchedContext + 2 TCBs. A CNode in the
post-state must have been in the pre-state. -/
theorem returnDonatedSchedContext_cnode_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCn : st'.objects[oid]? = some (.cnode cn)) :
    st.objects[oid]? = some (.cnode cn) :=
  -- WS-OD OD3.2: an instance of the shared kind frame.
  returnDonatedSchedContext_objects_backward_of_kind st st' serverTid scId originalOwner
    newOwner? hObjInv h oid _ (donationReturnWritesKind_cnode cn) hCn

/-- AI4-A: Forward transport — endpoints in pre-state exist identically in post-state
of returnDonatedSchedContext. Since the function only stores TCB/SchedContext objects,
endpoint objects at any ObjId are unchanged. -/
theorem returnDonatedSchedContext_endpoint_forward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    st'.objects[oid]? = some (.endpoint ep) :=
  -- WS-OD OD3.2: the forward half of the same shared kind frame.
  returnDonatedSchedContext_objects_forward_of_kind st st' serverTid scId originalOwner
    newOwner? hObjInv h oid _ (donationReturnWritesKind_endpoint ep) hEp

/-- AI4-A: Forward transport — endpoints in pre-state exist identically in the
cleaned state after cleanupPreReceiveDonation. -/
theorem cleanupPreReceiveDonation_endpoint_forward
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    (cleanupPreReceiveDonation st receiver).objects[oid]? = some (.endpoint ep) := by
  exact cleanupPreReceiveDonation_frame_helper
    (P := fun s => s.objects[oid]? = some (.endpoint ep))
    st receiver hEp
    (fun scId originalOwner newOwner? st' hRet =>
      returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet oid ep hEp)

/-- AI4-A: TCB backward transport through returnDonatedSchedContext for queue fields.
If a TCB exists in the post-state, there's a TCB in the pre-state with the same
queueNext, queuePrev, ipcState, and pendingMessage. Only schedContextBinding may differ. -/
theorem returnDonatedSchedContext_tcb_queue_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st'.objects[tid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid]? = some (.tcb tcb) ∧
      tcb.queueNext = tcb'.queueNext ∧ tcb.queuePrev = tcb'.queuePrev ∧
      tcb.ipcState = tcb'.ipcState ∧ tcb.pendingMessage = tcb'.pendingMessage := by
  -- WS-OD OD3.2: an instance of the shared TCB binding rewrite — the donation
  -- return moves one field, so every other field agrees by `rfl` on the record
  -- update rather than by a copy of the operation's case analysis.
  obtain ⟨tcb, hPre, sb, rfl⟩ :=
    returnDonatedSchedContext_tcb_rewrite_backward st st' serverTid scId originalOwner
      newOwner? hObjInv h tid tcb' hTcb'
  exact ⟨tcb, hPre, rfl, rfl, rfl, rfl⟩

/-- IPC de-threading D2: `returnDonatedSchedContext` preserves each TCB's
`(ipcState, replyObject)` pair backward — its three stores rewrite only a
`SchedContext`'s `boundThread` and two TCBs' `schedContextBinding`, never `ipcState`
or `replyObject`, so each store frames the pair (`rfl`).  Mirrors
`returnDonatedSchedContext_tcb_queue_backward`; feeds the
`blockedOnReplyHasReplyObject` frame for the receive-block path. -/
theorem returnDonatedSchedContext_tcb_ipcState_replyObject_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st'.objects[tid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid]? = some (.tcb tcb) ∧
      tcb.ipcState = tcb'.ipcState ∧ tcb.replyObject = tcb'.replyObject := by
  -- WS-OD OD3.2: an instance of the shared TCB binding rewrite.
  obtain ⟨tcb, hPre, sb, rfl⟩ :=
    returnDonatedSchedContext_tcb_rewrite_backward st st' serverTid scId originalOwner
      newOwner? hObjInv h tid tcb' hTcb'
  exact ⟨tcb, hPre, rfl, rfl⟩

/-- IPC de-threading D5: `returnDonatedSchedContext` preserves each TCB's `timeoutBudget` backward —
its three stores rewrite only a `SchedContext`'s `boundThread` and two TCBs' `schedContextBinding`,
never `timeoutBudget`, so each store frames the field (`rfl`).  Mirrors
`returnDonatedSchedContext_tcb_ipcState_replyObject_backward`; feeds the donation-return leg of the
receive family's `timeoutBudgetFrame`. -/
theorem returnDonatedSchedContext_tcb_timeoutBudget_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st'.objects[tid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid]? = some (.tcb tcb) ∧
      tcb.timeoutBudget = tcb'.timeoutBudget := by
  -- WS-OD OD3.2: an instance of the shared TCB binding rewrite.
  obtain ⟨tcb, hPre, sb, rfl⟩ :=
    returnDonatedSchedContext_tcb_rewrite_backward st st' serverTid scId originalOwner
      newOwner? hObjInv h tid tcb' hTcb'
  exact ⟨tcb, hPre, rfl⟩

/-- IPC de-threading D6: characterise each TCB's `schedContextBinding` after
`returnDonatedSchedContext`.  Unlike `ipcState`/`replyObject` (preserved), the binding *changes*
at the two written TCB slots: the thread the context goes back to gets
`donationReturnBinding scId newOwner?` and the server becomes `.unbound`; every other slot frames
from the pre-state.

WS-OD OD3.2: the middle clause reads `donationReturnBinding scId newOwner?` rather than
`.bound scId`, which is the same statement at `newOwner? = none` — every call site in the tree
today — and the widening the reply stack needs one level up, where the target is itself a donor
and must come back `.donated scId outer`. -/
theorem returnDonatedSchedContext_tcb_schedContextBinding_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st'.objects[tid]? = some (.tcb tcb')) :
    (tid = serverTid.toObjId → tcb'.schedContextBinding = .unbound) ∧
    (tid ≠ serverTid.toObjId → tid = originalOwner.toObjId →
      tcb'.schedContextBinding = donationReturnBinding scId newOwner?) ∧
    (tid ≠ serverTid.toObjId → tid ≠ originalOwner.toObjId →
      ∃ tcb, st.objects[tid]? = some (.tcb tcb) ∧
        tcb.schedContextBinding = tcb'.schedContextBinding) :=
  -- WS-OD OD3.2: **the binding trichotomy, widened at the target.**  The thread
  -- the context goes back to now carries `donationReturnBinding scId newOwner?`
  -- — `.bound scId` at the bottom of the stack, `.donated scId outer` one level
  -- up — which is the statement change the chain needs and the reason this row
  -- re-bases rather than re-proves.
  returnDonatedSchedContext_tcb_binding_cases st st' serverTid scId originalOwner
    newOwner? hObjInv h tid tcb' hTcb'

/-- IPC de-threading D6: `returnDonatedSchedContext` preserves `donationBudgetTransfer`.  Given
the server held the SchedContext in the pre-state (`hServerScId`), the return moves it from the
server (now `.unbound`) to the owner (`.bound scId`).  A post-state pair sharing some `scId''`
must therefore both pull back into the pre-state (the server cannot be one of them — it is now
`.unbound`), where `donationBudgetTransfer st` rules the share out — using the server's pre-state
`scId` reference for the owner-vs-framed case. -/
theorem returnDonatedSchedContext_preserves_donationBudgetTransfer
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (stcb : TCB)
    (hServerObj : st.objects[serverTid.toObjId]? = some (.tcb stcb))
    (hServerScId : stcb.schedContextBinding.scId? = some scId)
    (hInv : donationBudgetTransfer st)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId'' h1 h2 hNe hB1 hB2
  -- The server's post-binding is `.unbound`, so neither witness is the server.
  have hNS : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st'.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding.scId? = some scId'' → tid.toObjId ≠ serverTid.toObjId := by
    intro tid tcb hObj hB hEq
    rw [(returnDonatedSchedContext_tcb_schedContextBinding_backward st st' serverTid scId originalOwner
      hObjInv newOwner? h tid.toObjId tcb hObj).1 hEq] at hB
    simp [SchedContextBinding.scId?] at hB
  have hNS1 := hNS tid1 tcb1 h1 hB1
  have hNS2 := hNS tid2 tcb2 h2 hB2
  -- A non-server, non-owner slot frames to a pre-state TCB carrying the same `scId''`.
  have hPre : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st'.objects[tid.toObjId]? = some (.tcb tcb) →
      tid.toObjId ≠ serverTid.toObjId → tid.toObjId ≠ originalOwner.toObjId →
      tcb.schedContextBinding.scId? = some scId'' →
      ∃ ptcb, st.objects[tid.toObjId]? = some (.tcb ptcb) ∧
        ptcb.schedContextBinding.scId? = some scId'' := by
    intro tid tcb hObj hNeS hNeO hB
    obtain ⟨ptcb, hPreObj, hPbind⟩ := (returnDonatedSchedContext_tcb_schedContextBinding_backward
      st st' serverTid scId originalOwner hObjInv newOwner? h tid.toObjId tcb hObj).2.2 hNeS hNeO
    exact ⟨ptcb, hPreObj, by rw [hPbind]; exact hB⟩
  -- WS-OD OD3.2: the target's post-binding names `scId` on **both** arms of
  -- `donationReturnBinding`, so this step is insensitive to the stack depth.
  have hOwnerScId : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st'.objects[tid.toObjId]? = some (.tcb tcb) →
      tid.toObjId ≠ serverTid.toObjId → tid.toObjId = originalOwner.toObjId →
      tcb.schedContextBinding.scId? = some scId'' → scId'' = scId := by
    intro tid tcb hObj hNeS hEqO hB
    rw [(returnDonatedSchedContext_tcb_schedContextBinding_backward st st' serverTid scId originalOwner
      hObjInv newOwner? h tid.toObjId tcb hObj).2.1 hNeS hEqO, donationReturnBinding_scId?] at hB
    exact (Option.some.inj hB).symm
  by_cases hO1 : tid1.toObjId = originalOwner.toObjId
  · have hEqScId := hOwnerScId tid1 tcb1 h1 hNS1 hO1 hB1
    have hO2 : tid2.toObjId ≠ originalOwner.toObjId := fun hEq =>
      hNe (ThreadId.toObjId_injective tid1 tid2 (hO1.trans hEq.symm))
    obtain ⟨ptcb2, hPre2, hPbind2⟩ := hPre tid2 tcb2 h2 hNS2 hO2 hB2
    refine hInv tid2 serverTid ptcb2 stcb scId hPre2 hServerObj (fun hEq => hNS2 (by rw [hEq])) ?_ hServerScId
    rw [← hEqScId]; exact hPbind2
  · by_cases hO2 : tid2.toObjId = originalOwner.toObjId
    · have hEqScId := hOwnerScId tid2 tcb2 h2 hNS2 hO2 hB2
      obtain ⟨ptcb1, hPre1, hPbind1⟩ := hPre tid1 tcb1 h1 hNS1 hO1 hB1
      refine hInv tid1 serverTid ptcb1 stcb scId hPre1 hServerObj (fun hEq => hNS1 (by rw [hEq])) ?_ hServerScId
      rw [← hEqScId]; exact hPbind1
    · obtain ⟨ptcb1, hPre1, hPbind1⟩ := hPre tid1 tcb1 h1 hNS1 hO1 hB1
      obtain ⟨ptcb2, hPre2, hPbind2⟩ := hPre tid2 tcb2 h2 hNS2 hO2 hB2
      exact hInv tid1 tid2 ptcb1 ptcb2 scId'' hPre1 hPre2 hNe hPbind1 hPbind2

/-- IPC de-threading D6: `returnDonatedSchedContext` preserves the object map at every key other
than the three it writes (`scId` SchedContext, `originalOwner` TCB, `serverTid` TCB). -/
theorem returnDonatedSchedContext_objects_ne
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId)
    (hNeSc : oid ≠ scId.toObjId) (hNeO : oid ≠ originalOwner.toObjId)
    (hNeS : oid ≠ serverTid.toObjId)
    (hNotReply : ∀ r : Reply, st.objects[oid]? ≠ some (.reply r)) :
    st'.objects[oid]? = st.objects[oid]? :=
  -- WS-OD OD3.2: the pop also clears the context's stack head, which is a
  -- **Reply** — so "not one of the three keys" is no longer enough and the
  -- caller states what it knows about the key's contents.  Every consumer in the
  -- tree reads a key it has already resolved to a SchedContext or a TCB, so the
  -- new hypothesis is discharged by the witness it already holds.
  returnDonatedSchedContext_objects_ne_of_not_reply st st' serverTid scId originalOwner
    newOwner? hObjInv h oid hNeSc hNeO hNeS hNotReply

/-- IPC de-threading D6: `cleanupPreReceiveDonation` preserves `donationBudgetTransfer` — it is
either a no-op (no donated binding) or a single `returnDonatedSchedContext` of the receiver's own
donation (`scId? = some scId`), which preserves the conjunct. -/
theorem cleanupPreReceiveDonation_preserves_donationBudgetTransfer
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : donationBudgetTransfer st) :
    donationBudgetTransfer (cleanupPreReceiveDonation st receiver) := by
  unfold cleanupPreReceiveDonation
  cases hL : lookupTcb st receiver with
  | none => exact hInv
  | some recvTcb =>
    simp only []
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact hInv
    | bound scId => exact hInv
    | donated scId originalOwner =>
      simp only []
      cases hRet : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => exact hInv
      | ok st' =>
        simp only []
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_preserves_donationBudgetTransfer st st' receiver scId
          originalOwner hObjInv recvTcb (lookupTcb_some_objects st receiver recvTcb hL)
          (by rw [hBind]; rfl) hInv n hPop

/-- WS-OD OD3.2: **`donationOwnerValid` at the thread the pop hands the context
back to, when that thread is itself a donor.**

The depth-≥ 2 half of `returnDonatedSchedContext_establishes_donationOwnerValid_of_except`,
split out because it is the one case that is *not* a pull-back to the pre-state:
the donation it must justify did not exist before the step.  Both clauses come
from what the pop itself writes and from `donationReturnOuterValid`:

* the context's `boundThread` is the rebound thread, which is
  `returnDonatedSchedContext_post_schedContext`; and
* the outer caller is `.unbound` and `.blockedOnReply`, which is the obligation's
  own first clause, carried across the step because the pop writes neither the
  outer caller's TCB (its two distinctness clauses) nor a Reply at that key.

At `newOwner? = none` the hypothesis `hTarget` is `.bound scId`, which is not a
`.donated`, so the lemma is vacuously discharged and the tree's behaviour today
never reaches it. -/
theorem returnDonatedSchedContext_donationOwnerValid_at_target
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (hOuter : donationReturnOuterValid st serverTid originalOwner newOwner?)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId' : SeLe4n.SchedContextId) (owner' : SeLe4n.ThreadId)
    (_hTcb : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hTarget : tcb.schedContextBinding = donationReturnBinding scId newOwner?)
    (hBinding : tcb.schedContextBinding = .donated scId' owner')
    (hTidO : tid.toObjId = originalOwner.toObjId) :
    (∃ sc, st'.objects[scId'.toObjId]? = some (.schedContext sc) ∧
      sc.boundThread = some tid) ∧
    (∃ ownerTcb, st'.objects[owner'.toObjId]? = some (.tcb ownerTcb) ∧
      ownerTcb.schedContextBinding = .unbound ∧
      ∃ epId replyTarget, ownerTcb.ipcState = .blockedOnReply epId replyTarget) := by
  have hTidEq : tid = originalOwner := SeLe4n.ThreadId.toObjId_injective tid originalOwner hTidO
  -- The written binding is a donation, so the return is one level up the stack.
  obtain ⟨outer, hOuterEq⟩ : ∃ outer, newOwner? = some outer := by
    cases hN : newOwner? with
    | none => rw [hN] at hTarget; rw [hTarget] at hBinding; cases hBinding
    | some outer => exact ⟨outer, rfl⟩
  have hDon : SchedContextBinding.donated scId outer = .donated scId' owner' := by
    rw [← hBinding, hTarget, hOuterEq]; rfl
  have hScEq : scId' = scId := (SchedContextBinding.donated.inj hDon).1.symm
  have hOwnerEq2 : owner' = outer := (SchedContextBinding.donated.inj hDon).2.symm
  subst hScEq; subst hOwnerEq2; subst hTidEq
  -- Clause 1: the pop points the context at the thread it rebound.
  obtain ⟨sc0, head?, hPre, hPost⟩ :=
    returnDonatedSchedContext_post_schedContext st st' serverTid scId' tid hObjInv newOwner? h
  -- Clause 2: the outer caller's own TCB, carried across the pop's writes.
  obtain ⟨outerTcb, hOuterObj, hOuterUnbound, ep, rt, hOuterBlocked⟩ :=
    hOuter.outerIsDonor owner' hOuterEq
  have hNeTarget : owner'.toObjId ≠ tid.toObjId := fun hEq =>
    hOuter.outerNeTarget owner' hOuterEq (SeLe4n.ThreadId.toObjId_injective _ _ hEq)
  have hNeServer : owner'.toObjId ≠ serverTid.toObjId := fun hEq =>
    hOuter.outerNeServer owner' hOuterEq (SeLe4n.ThreadId.toObjId_injective _ _ hEq)
  have hNeSc : owner'.toObjId ≠ scId'.toObjId := by
    intro hEq; rw [hEq, hPre] at hOuterObj; cases hOuterObj
  refine ⟨⟨_, hPost, rfl⟩, ⟨outerTcb, ?_, hOuterUnbound, ep, rt, hOuterBlocked⟩⟩
  rw [returnDonatedSchedContext_objects_ne st st' serverTid scId' tid hObjInv newOwner? h
    owner'.toObjId hNeSc hNeTarget hNeServer
    (fun r hr => by rw [hOuterObj] at hr; cases hr)]
  exact hOuterObj

/-- IPC de-threading D6 / WS-RR RR3.12: `returnDonatedSchedContext` **establishes**
`donationOwnerValid` from the form relaxed at the owner it is handing the SchedContext back to.
The return hands `scId` back to `originalOwner` (server `.donated scId originalOwner` → server
`.unbound`, owner `.unbound` → `.bound scId`, `sc.boundThread := originalOwner`).  For every
*remaining* donation `tid ↦ .donated scId' owner'` (`tid` is neither the server — now `.unbound`
— nor the owner — now `.bound`): its SchedContext clause survives because `scId' ≠ scId` (else
`tid` and the server would both bind `scId`, forcing `tid = serverTid`); and its owner clause
survives because `owner' ≠ originalOwner` — **the one place donation-owner uniqueness is
needed**: were `owner'` the just-rebound `originalOwner`, both `tid` and the server would name
it, forcing `tid = serverTid` again.

That last step is also what makes the *relaxed* hypothesis enough, and hence what closes the
reply chain: the relaxation is exactly at `originalOwner`, and the remaining donations provably
do not name it.  The pre-state here is the one `endpointReply` leaves behind — the answered
caller already woken `.ready` while the server still holds the donation — where the unrelaxed
`donationOwnerValid` is false. -/
theorem returnDonatedSchedContext_establishes_donationOwnerValid_of_except
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (stcb : TCB)
    (hServerObj : st.objects[serverTid.toObjId]? = some (.tcb stcb))
    (hServerBind : stcb.schedContextBinding = .donated scId originalOwner)
    (hUnique : donationOwnerUnique st)
    (hInv : donationOwnerValidExcept st originalOwner)
    (newOwner? : Option SeLe4n.ThreadId)
    (hOuter : donationReturnOuterValid st serverTid originalOwner newOwner?)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationOwnerValid st' := by
  intro tid tcb scId' owner' hTcb hBinding
  have hBack := returnDonatedSchedContext_tcb_schedContextBinding_backward st st' serverTid scId
    originalOwner hObjInv newOwner? h tid.toObjId tcb hTcb
  have hTidNS : tid.toObjId ≠ serverTid.toObjId := by
    intro hEq; rw [hBack.1 hEq] at hBinding; cases hBinding
  -- WS-OD OD3.2: at the bottom of the reply stack the rebound thread carries
  -- `.bound scId` and cannot be a donation at all; one level up it carries
  -- `.donated scId outer`, and the conjunct is discharged there from the
  -- outer-caller obligation rather than being excluded.
  by_cases hTidO : tid.toObjId = originalOwner.toObjId
  · exact returnDonatedSchedContext_donationOwnerValid_at_target st st' serverTid scId
      originalOwner hObjInv newOwner? hOuter h tid tcb scId' owner' hTcb
      (hBack.2.1 hTidNS hTidO) hBinding hTidO
  have hTidNO : tid.toObjId ≠ originalOwner.toObjId := hTidO
  obtain ⟨tcb0, hTcb0, hBind0⟩ := hBack.2.2 hTidNS hTidNO
  have hBind0' : tcb0.schedContextBinding = .donated scId' owner' := hBind0.trans hBinding
  -- Pre-state witnesses for `tid`'s donation and for the server's donation.
  obtain ⟨⟨sc', hSc', hBound'⟩, ⟨ownerTcb, hOwner0, hUnbound0, hCase0⟩⟩ :=
    hInv tid tcb0 scId' owner' hTcb0 hBind0'
  obtain ⟨⟨scS, hScS, hBoundS⟩, ⟨oOwnerTcb, hOOwner, _, _⟩⟩ :=
    hInv serverTid stcb scId originalOwner hServerObj hServerBind
  -- `scId' ≠ scId`: else `sc' = scS` ⇒ `boundThread` is both `tid` and `serverTid`.
  have hScIdNe : scId'.toObjId ≠ scId.toObjId := by
    intro hEq; rw [hEq, hScS] at hSc'
    obtain rfl := KernelObject.schedContext.inj (Option.some.inj hSc')
    rw [hBoundS] at hBound'
    exact hTidNS (by rw [(Option.some.inj hBound').symm])
  -- `tid`'s SchedContext slot is not a TCB slot the return rewrote.
  have hScNeO : scId'.toObjId ≠ originalOwner.toObjId := by
    intro hEq; rw [hEq, hOOwner] at hSc'; cases hSc'
  have hScNeS : scId'.toObjId ≠ serverTid.toObjId := by
    intro hEq; rw [hEq, hServerObj] at hSc'; cases hSc'
  -- `owner' ≠ serverTid` (server is `.donated`, owner is `.unbound`) and `owner' ≠ originalOwner`
  -- (uniqueness).
  have hOwnerNS : owner'.toObjId ≠ serverTid.toObjId := by
    intro hEq; rw [hEq, hServerObj] at hOwner0
    obtain rfl := KernelObject.tcb.inj (Option.some.inj hOwner0)
    rw [hServerBind] at hUnbound0; cases hUnbound0
  have hOwnerNO : owner'.toObjId ≠ originalOwner.toObjId := by
    intro hEq
    have hOwnerEq : owner' = originalOwner := ThreadId.toObjId_injective owner' originalOwner hEq
    have := hUnique tid serverTid tcb0 stcb scId' scId originalOwner hTcb0 hServerObj
      (hOwnerEq ▸ hBind0') hServerBind
    exact hTidNS (by rw [this])
  have hOwnerNSc : owner'.toObjId ≠ scId.toObjId := by
    intro hEq; rw [hEq, hScS] at hOwner0; cases hOwner0
  -- WS-RR RR3.12: the relaxed disjunct is `owner' = originalOwner`, which `hOwnerNO`
  -- has just excluded -- so the relaxed hypothesis yields the full `.blockedOnReply`
  -- clause for every donation that survives the return.
  obtain ⟨ep, rt, hReply0⟩ : ∃ epId replyTarget,
      ownerTcb.ipcState = .blockedOnReply epId replyTarget :=
    hCase0.resolve_left (fun hEq => hOwnerNO (by rw [hEq]))
  refine ⟨⟨sc', ?_, hBound'⟩, ⟨ownerTcb, ?_, hUnbound0, ep, rt, hReply0⟩⟩
  · rw [returnDonatedSchedContext_objects_ne st st' serverTid scId originalOwner hObjInv newOwner? h
      scId'.toObjId hScIdNe hScNeO hScNeS
      (fun r hr => by rw [hSc'] at hr; cases hr)]; exact hSc'
  · rw [returnDonatedSchedContext_objects_ne st st' serverTid scId originalOwner hObjInv newOwner? h
      owner'.toObjId hOwnerNSc hOwnerNO hOwnerNS
      (fun r hr => by rw [hOwner0] at hr; cases hr)]; exact hOwner0

/-- IPC de-threading D6: `returnDonatedSchedContext` preserves `donationOwnerValid` — the
unrelaxed instance of the establisher above (the full invariant implies the relaxed one at
every thread). -/
theorem returnDonatedSchedContext_preserves_donationOwnerValid
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (stcb : TCB)
    (hServerObj : st.objects[serverTid.toObjId]? = some (.tcb stcb))
    (hServerBind : stcb.schedContextBinding = .donated scId originalOwner)
    (hUnique : donationOwnerUnique st)
    (hInv : donationOwnerValid st)
    (newOwner? : Option SeLe4n.ThreadId)
    (hOuter : donationReturnOuterValid st serverTid originalOwner newOwner?)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationOwnerValid st' :=
  returnDonatedSchedContext_establishes_donationOwnerValid_of_except st st' serverTid scId
    originalOwner hObjInv stcb hServerObj hServerBind hUnique
    (donationOwnerValidExcept_of_donationOwnerValid originalOwner hInv) newOwner? hOuter h

/-- IPC de-threading D6: `cleanupPreReceiveDonation` preserves `donationOwnerValid` — a no-op
unless the receiver holds a donated SchedContext, in which case the single
`returnDonatedSchedContext` preserves the invariant (donation-owner uniqueness in hand). -/
theorem cleanupPreReceiveDonation_preserves_donationOwnerValid
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hUnique : donationOwnerUnique st)
    (hUnowned : cleanupDonationStackValid st receiver)
    (hInv : donationOwnerValid st) :
    donationOwnerValid (cleanupPreReceiveDonation st receiver) := by
  unfold cleanupPreReceiveDonation
  cases hL : lookupTcb st receiver with
  | none => exact hInv
  | some recvTcb =>
    simp only []
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact hInv
    | bound scId => exact hInv
    | donated scId originalOwner =>
      simp only []
      cases hRet : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => exact hInv
      | ok st' =>
        simp only []
        obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_preserves_donationOwnerValid st st' receiver scId
          originalOwner hObjInv recvTcb (lookupTcb_some_objects st receiver recvTcb hL) hBind
          hUnique hInv n
          (donationReturnOuterValid_of_ok hPop ((hUnowned recvTcb scId originalOwner hL hBind) n hRes).2)
          hPop

/-- IPC de-threading D6: `returnDonatedSchedContext` preserves `donationOwnerUnique`.  The return
only *removes* a donation (the server's `.donated`), so every post-state donation injects backward
to a pre-state donation at the same `tid` with the same `owner` — uniqueness is inherited. -/
theorem returnDonatedSchedContext_preserves_donationOwnerUnique
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : donationOwnerUnique st)
    (newOwner? : Option SeLe4n.ThreadId)
    (hOuter : donationReturnOuterValid st serverTid originalOwner newOwner?)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationOwnerUnique st' := by
  -- WS-OD OD3.2: a post-state donation is either a pre-state one at the same key
  -- (`.inl`) or the one the pop **creates** at the rebound thread (`.inr`), which
  -- at the bottom of the stack does not exist.
  have hPull : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scIdx : SeLe4n.SchedContextId)
      (owner : SeLe4n.ThreadId),
      st'.objects[tid.toObjId]? = some (.tcb tcb) → tcb.schedContextBinding = .donated scIdx owner →
      (∃ tcb0, st.objects[tid.toObjId]? = some (.tcb tcb0) ∧
        tcb0.schedContextBinding = .donated scIdx owner) ∨
      (tid = originalOwner ∧ newOwner? = some owner) := by
    intro tid tcb scIdx owner hTcb hB
    have hBack := returnDonatedSchedContext_tcb_schedContextBinding_backward st st' serverTid scId
      originalOwner hObjInv newOwner? h tid.toObjId tcb hTcb
    have hNS : tid.toObjId ≠ serverTid.toObjId := by intro hEq; rw [hBack.1 hEq] at hB; cases hB
    by_cases hO : tid.toObjId = originalOwner.toObjId
    · refine Or.inr ⟨SeLe4n.ThreadId.toObjId_injective tid originalOwner hO, ?_⟩
      have hT := hBack.2.1 hNS hO
      cases hN : newOwner? with
      | none => rw [hN, donationReturnBinding_none] at hT; rw [hT] at hB; cases hB
      | some outer =>
        rw [hN, donationReturnBinding_some] at hT
        rw [hT] at hB
        rw [(SchedContextBinding.donated.inj hB).2]
    · obtain ⟨tcb0, hTcb0, hBind0⟩ := hBack.2.2 hNS hO
      exact Or.inl ⟨tcb0, hTcb0, hBind0.trans hB⟩
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  rcases hPull tid1 tcb1 scId1 owner h1 hB1 with ⟨tc1, hP1, hPB1⟩ | ⟨hT1, hN1⟩
  · rcases hPull tid2 tcb2 scId2 owner h2 hB2 with ⟨tc2, hP2, hPB2⟩ | ⟨hT2, hN2⟩
    · exact hInv tid1 tid2 tc1 tc2 scId1 scId2 owner hP1 hP2 hPB1 hPB2
    · exact absurd hPB1 (hOuter.outerUnowned owner hN2 tid1 tc1 scId1 hP1)
  · rcases hPull tid2 tcb2 scId2 owner h2 hB2 with ⟨tc2, hP2, hPB2⟩ | ⟨hT2, _⟩
    · exact absurd hPB2 (hOuter.outerUnowned owner hN1 tid2 tc2 scId2 hP2)
    · rw [hT1, hT2]

/-- IPC de-threading D6: `cleanupPreReceiveDonation` preserves `donationOwnerUnique`. -/
theorem cleanupPreReceiveDonation_preserves_donationOwnerUnique
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hUnowned : cleanupDonationStackValid st receiver)
    (hInv : donationOwnerUnique st) :
    donationOwnerUnique (cleanupPreReceiveDonation st receiver) := by
  unfold cleanupPreReceiveDonation
  cases hL : lookupTcb st receiver with
  | none => exact hInv
  | some recvTcb =>
    simp only []
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact hInv
    | bound scId => exact hInv
    | donated scId originalOwner =>
      simp only []
      cases hRet : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => exact hInv
      | ok st' =>
        simp only []
        obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_preserves_donationOwnerUnique st st' receiver scId
          originalOwner hObjInv hInv n
          (donationReturnOuterValid_of_ok hPop
            ((hUnowned recvTcb scId originalOwner hL hBind) n hRes).2) hPop

/-- IPC de-threading D2: `cleanupPreReceiveDonation` preserves each TCB's
`(ipcState, replyObject)` pair backward — it is either a no-op (no donated binding) or a
single `returnDonatedSchedContext`, which frames the pair.  Lift of
`returnDonatedSchedContext_tcb_ipcState_replyObject_backward`. -/
theorem cleanupPreReceiveDonation_tcb_ipcState_replyObject_backward
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (tid : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : (cleanupPreReceiveDonation st receiver).objects[tid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.ipcState = tcb'.ipcState ∧ tcb.replyObject = tcb'.replyObject := by
  unfold cleanupPreReceiveDonation at hTcb'
  cases hLookup : lookupTcb st receiver with
  | none => simp only [hLookup] at hTcb'; exact ⟨tcb', hTcb', rfl, rfl⟩
  | some recvTcb =>
    simp only [hLookup] at hTcb'
    cases hBinding : recvTcb.schedContextBinding with
    | unbound => simp only [hBinding] at hTcb'; exact ⟨tcb', hTcb', rfl, rfl⟩
    | bound _ => simp only [hBinding] at hTcb'; exact ⟨tcb', hTcb', rfl, rfl⟩
    | donated scId originalOwner =>
      simp only [hBinding] at hTcb'
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => simp only [hReturn] at hTcb'; exact ⟨tcb', hTcb', rfl, rfl⟩
      | ok st' =>
        simp only [hReturn] at hTcb'
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        exact returnDonatedSchedContext_tcb_ipcState_replyObject_backward st st' receiver scId
          originalOwner hObjInv n hPop tid.toObjId tcb' hTcb'

/-- IPC de-threading D3: `returnDonatedSchedContext` preserves each TCB's
`pendingReceiveReply` backward — its three stores rewrite only a `SchedContext`'s
`boundThread` and two TCBs' `schedContextBinding`, never the stash, so each store
frames it (`rfl`).  Mirrors `returnDonatedSchedContext_tcb_ipcState_replyObject_backward`;
feeds the `pendingReceiveReplyWellFormed` freshness transport for the receive-block
path. -/
theorem returnDonatedSchedContext_tcb_pendingReceiveReply_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st'.objects[tid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid]? = some (.tcb tcb) ∧
      tcb.pendingReceiveReply = tcb'.pendingReceiveReply := by
  -- WS-OD OD3.2: an instance of the shared TCB binding rewrite.
  obtain ⟨tcb, hPre, sb, rfl⟩ :=
    returnDonatedSchedContext_tcb_rewrite_backward st st' serverTid scId originalOwner
      newOwner? hObjInv h tid tcb' hTcb'
  exact ⟨tcb, hPre, rfl⟩

/-- WS-OD OD3.2 (was IPC de-threading D3): **`returnDonatedSchedContext`'s Reply
frame.**

Before the pop existed this asserted exact preservation, on the reasoning that
the return's three stores wrote a SchedContext and two TCBs and never a Reply.
The pop clears the context's stack head, which *is* a Reply, so the honest
statement is the frame: every Reply survives with at most its stack links reset,
and every other field — `caller` included, which is what the reply-freshness and
stash invariants read — agrees exactly.  Forward direction. -/
theorem returnDonatedSchedContext_reply_frame
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply)
    (hReply : st.objects[oid]? = some (.reply r))
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ r', st'.objects[oid]? = some (.reply r') ∧ replyStackRewrite r' r :=
  returnDonatedSchedContext_reply_rewrite st st' serverTid scId originalOwner newOwner?
    hObjInv h oid r hReply

/-- IPC de-threading D3: `cleanupPreReceiveDonation` preserves `pendingReceiveReply`
backward (no-op or a single `returnDonatedSchedContext`).  Lift of
`returnDonatedSchedContext_tcb_pendingReceiveReply_backward`. -/
theorem cleanupPreReceiveDonation_tcb_pendingReceiveReply_backward
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (tid : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : (cleanupPreReceiveDonation st receiver).objects[tid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.pendingReceiveReply = tcb'.pendingReceiveReply := by
  unfold cleanupPreReceiveDonation at hTcb'
  cases hLookup : lookupTcb st receiver with
  | none => simp only [hLookup] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
  | some recvTcb =>
    simp only [hLookup] at hTcb'
    cases hBinding : recvTcb.schedContextBinding with
    | unbound => simp only [hBinding] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
    | bound _ => simp only [hBinding] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
    | donated scId originalOwner =>
      simp only [hBinding] at hTcb'
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => simp only [hReturn] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
      | ok st' =>
        simp only [hReturn] at hTcb'
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        exact returnDonatedSchedContext_tcb_pendingReceiveReply_backward st st' receiver scId
          originalOwner hObjInv n hPop tid.toObjId tcb' hTcb'

set_option linter.unusedSimpArgs false in
/-- WS-OD OD3.2 (was IPC de-threading D3): `cleanupPreReceiveDonation`'s Reply
frame — a no-op, or a single `returnDonatedSchedContext`.  Lift of
`returnDonatedSchedContext_reply_frame`. -/
theorem cleanupPreReceiveDonation_reply_frame
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply)
    (hReply : st.objects[oid]? = some (.reply r))
    (hObjInv : st.objects.invExt) :
    ∃ r', (cleanupPreReceiveDonation st receiver).objects[oid]? = some (.reply r') ∧
      replyStackRewrite r' r := by
  unfold cleanupPreReceiveDonation
  cases hLookup : lookupTcb st receiver with
  | none => simp only [hLookup]; exact ⟨r, hReply, replyStackRewrite.refl r⟩
  | some recvTcb =>
    simp only [hLookup]
    cases hBinding : recvTcb.schedContextBinding with
    | unbound => simp only [hBinding]; exact ⟨r, hReply, replyStackRewrite.refl r⟩
    | bound _ => simp only [hBinding]; exact ⟨r, hReply, replyStackRewrite.refl r⟩
    | donated scId originalOwner =>
      simp only [hBinding]
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => simp only [hReturn]; exact ⟨r, hReply, replyStackRewrite.refl r⟩
      | ok st' =>
        simp only [hReturn]
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        exact returnDonatedSchedContext_reply_frame st st' receiver scId originalOwner
          oid r hReply hObjInv n hPop

/-- IPC de-threading D2: `cleanupPreReceiveDonation` **preserves** the third clause of
`replyCallerLinkage`.  Cleanup never alters any TCB's `ipcState` or `replyObject`
(`cleanupPreReceiveDonation_tcb_ipcState_replyObject_backward`), so a `.blockedOnReply`
TCB in the cleaned state maps back to one already carrying a reply.  Frames the receive
no-sender (block) path. -/
theorem cleanupPreReceiveDonation_preserves_blockedOnReplyHasReplyObject
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st) :
    blockedOnReplyHasReplyObject (cleanupPreReceiveDonation st receiver) := by
  intro tid tcb ep rt hTcb hBlk
  obtain ⟨tcb0, hTcb0, hIpc, hRepl⟩ :=
    cleanupPreReceiveDonation_tcb_ipcState_replyObject_backward st receiver hObjInv tid tcb hTcb
  obtain ⟨rid, hRid⟩ := hInv tid tcb0 ep rt hTcb0 (by rw [hIpc]; exact hBlk)
  exact ⟨rid, hRepl ▸ hRid⟩

/-- AI4-A: TCB forward transport through returnDonatedSchedContext for queue fields.
If a TCB exists in the pre-state, there's a TCB in the post-state with the same
queueNext, queuePrev, ipcState, and pendingMessage. -/
theorem returnDonatedSchedContext_tcb_queue_forward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[tid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[tid]? = some (.tcb tcb') ∧
      tcb'.queueNext = tcb.queueNext ∧ tcb'.queuePrev = tcb.queuePrev ∧
      tcb'.ipcState = tcb.ipcState ∧ tcb'.pendingMessage = tcb.pendingMessage := by
  -- WS-OD OD3.2: the forward half of the same shared rewrite.
  obtain ⟨tcb', hPost, sb, rfl⟩ :=
    returnDonatedSchedContext_tcb_rewrite st st' serverTid scId originalOwner
      hObjInv newOwner? h tid tcb hTcb
  exact ⟨_, hPost, rfl, rfl, rfl, rfl⟩

/-- AI4-A (WS-RR RR3.11, generic in the message property): cleanupPreReceiveDonation
preserves `pendingMessagesSatisfy`.  The family quantifies over TCBs and their
`pendingMessage` field, which is unchanged by returnDonatedSchedContext (only
schedContextBinding is modified) — so the transport never reads the message and
holds for every `P`. -/
theorem cleanupPreReceiveDonation_preserves_pendingMessagesSatisfy
    {P : IpcMessage → Prop}
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : pendingMessagesSatisfy P st) :
    pendingMessagesSatisfy P (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      intro tid tcb' msg hTcb' hMsg'
      obtain ⟨tcb, hTcb, _, _, _, hMsgEq⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
          tid.toObjId tcb' hTcb'
      rw [← hMsgEq] at hMsg'
      exact hInv tid tcb msg hTcb hMsg'

/-- AI4-A: cleanupPreReceiveDonation preserves allPendingMessagesBounded — the
boundedness instance of the generic in-flight transport above. -/
theorem cleanupPreReceiveDonation_preserves_allPendingMessagesBounded
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded (cleanupPreReceiveDonation st receiver) :=
  cleanupPreReceiveDonation_preserves_pendingMessagesSatisfy st receiver hObjInv hInv

/-- WS-RR RR3.11: cleanupPreReceiveDonation preserves the in-flight badge invariant. -/
theorem cleanupPreReceiveDonation_preserves_pendingMessageCapBadgesWellFormed
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : pendingMessageCapBadgesWellFormed st) :
    pendingMessageCapBadgesWellFormed (cleanupPreReceiveDonation st receiver) :=
  cleanupPreReceiveDonation_preserves_pendingMessagesSatisfy st receiver hObjInv hInv

/-- AI4-A: cleanupPreReceiveDonation preserves badgeWellFormed.
The invariant quantifies over notifications and CNodes, neither of which is
modified by returnDonatedSchedContext. -/
theorem cleanupPreReceiveDonation_preserves_badgeWellFormed
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : badgeWellFormed st) :
    badgeWellFormed (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      constructor
      · -- notificationBadgesWellFormed: notifications are unchanged
        intro oid ntfn badge hNtfn hBadge
        have hNtfnPre := returnDonatedSchedContext_notification_backward st st' receiver scId originalOwner hObjInv newOwner? hRet oid ntfn hNtfn
        exact hInv.1 oid ntfn badge hNtfnPre hBadge
      · -- capabilityBadgesWellFormed: CNodes are unchanged
        intro oid cn slot cap badge hCn hLookup hBadge
        -- CNodes are neither TCBs nor SchedContexts, so unchanged through storeObject
        -- We need backward transport for CNode objects — identical pattern to endpoint
        -- Since returnDonatedSchedContext only stores TCBs and SchedContexts,
        -- CNode objects are unchanged. Use the notification backward pattern.
        -- Actually, we can use the general backward fact: any non-TCB non-SchedContext
        -- object in st' was in st.
        exact hInv.2 oid cn slot cap badge
          (returnDonatedSchedContext_cnode_backward st st' receiver scId originalOwner hObjInv newOwner? hRet oid cn hCn)
          hLookup hBadge

/-- AI4-A: cleanupPreReceiveDonation preserves blockedThreadsPendingMessageConsistent.
The invariant quantifies over TCBs checking ipcState and pendingMessage, both
unchanged by returnDonatedSchedContext (only schedContextBinding is modified). -/
theorem cleanupPreReceiveDonation_preserves_blockedThreadsPendingMessageConsistent
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      intro tid tcb' hTcb'
      obtain ⟨tcb, hTcb, _, _, hIpcEq, hMsgEq⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
          tid.toObjId tcb' hTcb'
      have hPre := hInv tid tcb hTcb
      rw [← hIpcEq, ← hMsgEq]; exact hPre

/-- AI4-A: cleanupPreReceiveDonation preserves ipcStateQueueConsistent.
The invariant quantifies over TCBs (checking ipcState) and requires endpoint
existence. Both TCB ipcState and endpoint objects are unchanged. -/
theorem cleanupPreReceiveDonation_preserves_ipcStateQueueConsistent
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      intro tid tcb' hTcb'
      obtain ⟨tcb, hTcb, _, _, hIpcEq, _⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
          tid.toObjId tcb' hTcb'
      have hPre := hInv tid tcb hTcb
      rw [← hIpcEq]
      -- For each blocking ipcState case, transport the endpoint existence forward
      cases hIpc : tcb.ipcState with
      | blockedOnSend epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp⟩ := hPre
        exact ⟨ep, returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp⟩
      | blockedOnReceive epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp⟩ := hPre
        exact ⟨ep, returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp⟩
      | blockedOnCall epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp⟩ := hPre
        exact ⟨ep, returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp⟩
      | _ => trivial

/-- AI4-A: QueueNextPath transfer: a QueueNextPath in st' implies one in st,
when st' comes from returnDonatedSchedContext (TCB queueNext is preserved). -/
private theorem QueueNextPath_backward_of_returnDonatedSchedContext
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (hRet : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (a b : SeLe4n.ThreadId)
    (hPath : QueueNextPath st' a b) :
    QueueNextPath st a b := by
  induction hPath with
  | single src dst tcb' hObj' hNext' =>
    obtain ⟨tcb, hObj, hQN, _, _, _⟩ :=
      returnDonatedSchedContext_tcb_queue_backward st st' serverTid scId originalOwner hObjInv newOwner? hRet
        src.toObjId tcb' hObj'
    exact .single src dst tcb hObj (hQN ▸ hNext')
  | cons src mid tgt tcb' hObj' hNext' _ ih =>
    obtain ⟨tcb, hObj, hQN, _, _, _⟩ :=
      returnDonatedSchedContext_tcb_queue_backward st st' serverTid scId originalOwner hObjInv newOwner? hRet
        src.toObjId tcb' hObj'
    exact .cons src mid tgt tcb hObj (hQN ▸ hNext') ih

/-- AI4-A: cleanupPreReceiveDonation preserves dualQueueSystemInvariant.
Endpoint objects and TCB queue fields (queueNext, queuePrev) are unchanged. -/
theorem cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      obtain ⟨hDQWF, hLink, hAcyc⟩ := hInv
      refine ⟨?_, ?_, ?_⟩
      · -- dualQueueEndpointWellFormed for all endpoints in st'
        intro epId ep hEp'
        have hEpPre := returnDonatedSchedContext_endpoint_backward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp'
        have hDQ := hDQWF epId ep hEpPre
        unfold dualQueueEndpointWellFormed at hDQ ⊢
        simp only [hEp'] at ⊢
        simp only [hEpPre] at hDQ
        -- hDQ : intrusiveQueueWellFormed ep.sendQ st ∧ intrusiveQueueWellFormed ep.receiveQ st
        -- Goal: intrusiveQueueWellFormed ep.sendQ st' ∧ intrusiveQueueWellFormed ep.receiveQ st'
        -- Transport each via TCB queue forward
        have transportQ : ∀ (q : IntrusiveQueue),
            intrusiveQueueWellFormed q st → intrusiveQueueWellFormed q st' := by
          intro q ⟨hEmpty, hHead, hTail⟩
          refine ⟨hEmpty, ?_, ?_⟩
          · intro hd hHd
            obtain ⟨tcb, hTcb, hPrev⟩ := hHead hd hHd
            obtain ⟨tcb', hTcb', _, hQP', _, _⟩ :=
              returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
                hd.toObjId tcb hTcb
            exact ⟨tcb', hTcb', hQP' ▸ hPrev⟩
          · intro tl hTl
            obtain ⟨tcb, hTcb, hNext⟩ := hTail tl hTl
            obtain ⟨tcb', hTcb', hQN', _, _, _⟩ :=
              returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
                tl.toObjId tcb hTcb
            exact ⟨tcb', hTcb', hQN' ▸ hNext⟩
        exact ⟨transportQ _ hDQ.1, transportQ _ hDQ.2⟩
      · -- tcbQueueLinkIntegrity in st'
        obtain ⟨hFwd, hRev⟩ := hLink
        constructor
        · -- Forward: a.queueNext = some b ⟹ b exists ∧ b.queuePrev = some a
          intro a tcbA' hTcbA' b hNext'
          obtain ⟨tcbA, hTcbA, hQNA, _, _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
              a.toObjId tcbA' hTcbA'
          obtain ⟨tcbB, hTcbB, hPrev⟩ := hFwd a tcbA hTcbA b (hQNA ▸ hNext')
          obtain ⟨tcbB', hTcbB', _, hQPB', _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
              b.toObjId tcbB hTcbB
          exact ⟨tcbB', hTcbB', hQPB' ▸ hPrev⟩
        · -- Reverse: b.queuePrev = some a ⟹ a exists ∧ a.queueNext = some b
          intro b tcbB' hTcbB' a hPrev'
          obtain ⟨tcbB, hTcbB, _, hQPB, _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
              b.toObjId tcbB' hTcbB'
          obtain ⟨tcbA, hTcbA, hNext⟩ := hRev b tcbB hTcbB a (hQPB ▸ hPrev')
          obtain ⟨tcbA', hTcbA', hQNA', _, _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
              a.toObjId tcbA hTcbA
          exact ⟨tcbA', hTcbA', hQNA' ▸ hNext⟩
      · -- tcbQueueChainAcyclic in st'
        intro tid hPath'
        exact hAcyc tid
          (QueueNextPath_backward_of_returnDonatedSchedContext st st' receiver scId originalOwner hObjInv newOwner? hRet tid tid hPath')

/-- AI4-A: cleanupPreReceiveDonation preserves endpointQueueNoDup. -/
theorem cleanupPreReceiveDonation_preserves_endpointQueueNoDup
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : endpointQueueNoDup st) :
    endpointQueueNoDup (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      intro oid ep hEp'
      have hEpPre := returnDonatedSchedContext_endpoint_backward st st' receiver scId originalOwner hObjInv newOwner? hRet oid ep hEp'
      obtain ⟨hNoSelf, hDisjoint⟩ := hInv oid ep hEpPre
      constructor
      · -- No self-loops: for all TCBs in st', queueNext ≠ some tid
        intro tid tcb' hTcb'
        obtain ⟨tcb, hTcb, hQN, _, _, _⟩ :=
          returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
            tid.toObjId tcb' hTcb'
        rw [← hQN]; exact hNoSelf tid tcb hTcb
      · -- Disjointness unchanged since endpoint queues are unchanged
        exact hDisjoint

/-- AI4-A: cleanupPreReceiveDonation preserves ipcStateQueueMembershipConsistent. -/
theorem cleanupPreReceiveDonation_preserves_ipcStateQueueMembershipConsistent
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner newOwner? st' hRet => by
      intro tid tcb' hTcb'
      obtain ⟨tcb, hTcb, hQN, _, hIpc, _⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv newOwner? hRet
          tid.toObjId tcb' hTcb'
      have hPre := hInv tid tcb hTcb
      rw [← hIpc]
      cases hIpcCase : tcb.ipcState with
      | blockedOnSend epId =>
        simp only [hIpcCase] at hPre
        obtain ⟨ep, hEp, hReach⟩ := hPre
        exact ⟨ep,
          returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp,
          hReach.elim
            (fun hHead => .inl hHead)
            (fun ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ =>
              .inr ⟨prev, by
                obtain ⟨prevTcb', hPrevTcb', hQN', _, _, _⟩ :=
                  returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
                    prev.toObjId prevTcb hPrevTcb
                exact ⟨prevTcb', hPrevTcb', hQN' ▸ hPrevNext⟩⟩)⟩
      | blockedOnReceive epId =>
        simp only [hIpcCase] at hPre
        obtain ⟨ep, hEp, hReach⟩ := hPre
        exact ⟨ep,
          returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp,
          hReach.elim
            (fun hHead => .inl hHead)
            (fun ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ =>
              .inr ⟨prev, by
                obtain ⟨prevTcb', hPrevTcb', hQN', _, _, _⟩ :=
                  returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
                    prev.toObjId prevTcb hPrevTcb
                exact ⟨prevTcb', hPrevTcb', hQN' ▸ hPrevNext⟩⟩)⟩
      | blockedOnCall epId =>
        simp only [hIpcCase] at hPre
        obtain ⟨ep, hEp, hReach⟩ := hPre
        exact ⟨ep,
          returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv newOwner? hRet epId ep hEp,
          hReach.elim
            (fun hHead => .inl hHead)
            (fun ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ =>
              .inr ⟨prev, by
                obtain ⟨prevTcb', hPrevTcb', hQN', _, _, _⟩ :=
                  returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv newOwner? hRet
                    prev.toObjId prevTcb hPrevTcb
                exact ⟨prevTcb', hPrevTcb', hQN' ▸ hPrevNext⟩⟩)⟩
      | _ => trivial

/-- AI4-A: cleanupPreReceiveDonation preserves dualQueueEndpointWellFormed. -/
theorem cleanupPreReceiveDonation_preserves_dualQueueEndpointWellFormed
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hDQSI : dualQueueSystemInvariant st)
    (epId : SeLe4n.ObjId)
    (ep : Endpoint)
    (hEp : (cleanupPreReceiveDonation st receiver).objects[epId]? = some (.endpoint ep)) :
    dualQueueEndpointWellFormed epId (cleanupPreReceiveDonation st receiver) :=
  (cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hDQSI).1 epId ep hEp

-- ============================================================================
-- AK1-A (I-H01): Unreachability of the error branch — non-donated path
-- ============================================================================
--
-- The `Checked` variant's `.error` arm is unreachable when the receiver is
-- not currently holding a donated SchedContext. This is the common case:
-- the cleanup path only does real work if the receiver has a stale donated
-- binding from an unanswered call, which is an abnormal flow. For the
-- `.unbound` / `.bound _` paths, the Checked variant returns `.ok st`
-- unconditionally and so never errors.
--
-- The full unreachability proof on the donated path requires threading
-- `donationOwnerValid` (which guarantees SchedContext + owner TCB presence)
-- together with typed-ID disjointness + reserved-ID absence invariants. This
-- is a separate proof obligation tracked in the AK1-J batch and discharged
-- incrementally as the donation invariant suite evolves. For this phase, the
-- code-level error propagation is the primary deliverable; the donated-path
-- unreachability is a proof-engineering refinement that does not affect
-- operational correctness (the fail-closed behavior is preserved in either
-- case).

/-- AK1-A (I-H01): `cleanupPreReceiveDonationChecked` never errors when the
    receiver's binding is `.unbound` or `.bound _` (the common paths). The
    donated-path case is handled by the broader invariant chain. -/
theorem cleanupPreReceiveDonationChecked_ok_of_non_donated
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hNonDonated : ∀ recvTcb, lookupTcb st receiver = some recvTcb →
      ∀ scId owner, recvTcb.schedContextBinding ≠ .donated scId owner) :
    ∃ st', cleanupPreReceiveDonationChecked st receiver = .ok st' := by
  unfold cleanupPreReceiveDonationChecked
  cases hLk : lookupTcb st receiver with
  | none => exact ⟨st, rfl⟩
  | some recvTcb =>
    show ∃ st', (match recvTcb.schedContextBinding with
      | .donated scId owner => returnDonatedSchedContextResolved st receiver scId owner
      | _ => .ok st) = .ok st'
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact ⟨st, rfl⟩
    | bound _ => exact ⟨st, rfl⟩
    | donated scId owner =>
      exact absurd hBind (hNonDonated recvTcb hLk scId owner)

/-- AK1-A (I-H01): Self-donation is precluded by `donationOwnerValid`.
    A receiver with `.donated scId owner` binding cannot have `owner = receiver`
    because `donationOwnerValid` requires the owner's TCB to have
    `.bound scId` binding, which is incompatible with `.donated`. -/
theorem donationOwnerValid_excludes_self_donation
    (st : SystemState) (receiver : SeLe4n.ThreadId) (recvTcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hDOV : donationOwnerValid st)
    (hRecvObj : st.objects[receiver.toObjId]? = some (.tcb recvTcb))
    (hBind : recvTcb.schedContextBinding = .donated scId owner) :
    owner ≠ receiver := by
  intro hEq
  -- Apply donationOwnerValid at the (receiver, recvTcb, scId, owner) witness.
  obtain ⟨_, ownerTcb, hOwnerObj, hOwnerBind, _⟩ :=
    hDOV receiver recvTcb scId owner hRecvObj hBind
  -- Rewrite owner = receiver so owner.toObjId = receiver.toObjId.
  rw [hEq] at hOwnerObj
  -- Both lookups at receiver.toObjId give some TCB; they must coincide.
  have hSameObj : some (KernelObject.tcb recvTcb) = some (KernelObject.tcb ownerTcb) :=
    hRecvObj.symm.trans hOwnerObj
  have hTcbEq : recvTcb = ownerTcb := by
    have := Option.some.inj hSameObj
    exact KernelObject.tcb.inj this
  -- recvTcb's binding is `.donated scId owner`, ownerTcb's is `.bound scId`.
  rw [hTcbEq] at hBind
  rw [hOwnerBind] at hBind
  cases hBind

/-- AK1-A (I-H01): Type-disjointness — `SchedContext` at scId cannot alias
    any TCB object. If `donationOwnerValid` yields a SchedContext at scId
    and a TCB at tid, then `scId.toObjId ≠ tid.toObjId` (different
    `KernelObject` constructors at the same ObjId would contradict
    `Option.some.inj`). Used by `returnDonatedSchedContext_ok_under_invariants`
    to thread TCB lookups through the SchedContext store. -/
theorem schedContext_ne_tcb_at_objId
    (st : SystemState) (scId : SeLe4n.SchedContextId) (tid : SeLe4n.ThreadId)
    (sc : SchedContext) (tcb : TCB)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    scId.toObjId ≠ tid.toObjId := by
  intro heq
  rw [heq] at hSc
  rw [hSc] at hTcb
  cases hTcb

/-- AK1-A (I-H01): `returnDonatedSchedContext` succeeds under
    `donationOwnerValid` combined with non-reservation of the participant
    thread IDs and the pop's head validation.  This is the structural
    unreachability proof for the internal error branches in
    `returnDonatedSchedContext`:

    (1) Missing SchedContext at `scId.toObjId` — excluded by
        `donationOwnerValid`'s SchedContext witness.
    (2) The `boundThread` guard — excluded by the same witness's
        "the donated SchedContext is bound to the server" clause.
    (3) WS-OD OD3.2: the **head validation** — excluded by
        `donationHeadResolves`, which `donationChainWellFormed` establishes
        (`donationHeadResolves_of_chainWellFormed`) and which any step writing no
        chain object carries (`donationHeadResolves_of_frame`).  This arm has no
        pre-OD3 counterpart: it is the guard the pop added, and it is a
        hypothesis rather than a derived fact because a scheduling context whose
        stack head dangles is exactly what the chain invariant forbids and
        nothing weaker rules out.
    (4) The **head clear** — excluded by the same hypothesis, since the head the
        guard resolved is still a Reply after the SchedContext store, which
        lands on a different key.
    (5) Missing owner TCB (`lookupTcb`) — excluded by the owner TCB witness +
        SchedContext/TCB type-disjointness + owner non-reservation.
    (6) Missing server TCB (`lookupTcb`) — excluded by the receiver TCB witness
        + the chain of stores preserving TCB existence at distinct ObjIds +
        receiver non-reservation.

    All four `storeObject` calls are unconditional `.ok` (see
    `Model/State.lean`). -/
theorem returnDonatedSchedContext_ok_under_invariants
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (recvTcb : TCB) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hDOV : donationOwnerValid st)
    (hHeadRes : donationHeadResolves st scId)
    (hLk : lookupTcb st receiver = some recvTcb)
    (hBind : recvTcb.schedContextBinding = .donated scId owner)
    (hRecvNotRes : ¬receiver.isReserved = true)
    (hOwnerNotRes : ¬owner.isReserved = true)
    (newOwner? : Option SeLe4n.ThreadId)
    -- WS-OD OD4.4: the pop refuses an outer caller it cannot validate, so a claim
    -- that it *succeeds* has to say the outer caller is acceptable.  At the bottom
    -- of the reply stack this is `rfl` (`outerCallerAcceptable_none`), which is
    -- every call site in the tree today; one level up it is a decidable check on
    -- the pre-state rather than the four-clause obligation consumers used to carry.
    (hOuterOk : outerCallerAcceptable st receiver owner newOwner? = true) :
    ∃ st', returnDonatedSchedContext st receiver scId owner newOwner? = .ok st' := by
  -- Recover hypotheses from donationOwnerValid.
  have hRecvObj : st.objects[receiver.toObjId]? = some (.tcb recvTcb) :=
    lookupTcb_some_objects st receiver recvTcb hLk
  obtain ⟨⟨sc, hScObj, hScBound⟩, ownerTcb, hOwnerObj, _, _⟩ :=
    hDOV receiver recvTcb scId owner hRecvObj hBind
  -- Type-disjointness of SchedContext vs TCB objIds.
  have hScNeOwner : scId.toObjId ≠ owner.toObjId :=
    schedContext_ne_tcb_at_objId st scId owner sc ownerTcb hScObj hOwnerObj
  have hScNeRecv : scId.toObjId ≠ receiver.toObjId :=
    schedContext_ne_tcb_at_objId st scId receiver sc recvTcb hScObj hRecvObj
  -- owner ≠ receiver (self-donation excluded).
  have hOwnerNeRecv : owner ≠ receiver :=
    donationOwnerValid_excludes_self_donation st receiver recvTcb scId owner
      hDOV hRecvObj hBind
  have hOwnerObjIdNeRecv : owner.toObjId ≠ receiver.toObjId := by
    intro heq; exact hOwnerNeRecv (SeLe4n.ThreadId.toObjId_injective _ _ heq)
  -- WS-OD OD3.2: the pop's head validation, and the Reply it resolved.
  obtain ⟨head?, hHead, hBelow⟩ := hHeadRes sc hScObj
  unfold returnDonatedSchedContext SystemState.getSchedContext?
  rw [hScObj]
  simp only []
  -- WS-RR RR2.8: the `sc.boundThread = some serverTid` guard is a
  -- structurally-unreachable error arm, discharged by the same
  -- `donationOwnerValid` witness that discharges the others — it is exactly
  -- that invariant's "the donated SchedContext is bound to the server" clause.
  rw [if_neg (by simp [hScBound])]
  -- WS-OD OD4.4: ...and then the outer-caller guard, discharged from the
  -- hypothesis — the pop refuses an outer caller it cannot validate, so a claim
  -- that it succeeds owes that fact.  The order is the operation's own.
  rw [if_neg (by simp [hOuterOk])]
  rw [hHead]
  simp only []
  generalize hS1 : storeObject scId.toObjId
      (.schedContext { sc with boundThread := some owner,
                               scReply := head?.bind (fun p => p.2.prev) }) st = result1
  match result1, hS1 with
  | .ok pair1, hS1 =>
    have hInv1 : pair1.2.objects.invExt :=
      storeObject_preserves_objects_invExt st pair1.2 scId.toObjId _ hObjInv hS1
    -- WS-OD OD3.2 / `v0.35.4`: the head pop.  The head Reply the guard resolved
    -- and the frame below it are both at keys the SchedContext store did not
    -- touch, so they are still Replies here — the two objects the pop writes.
    obtain ⟨s2, hClear⟩ : ∃ s2, storeDonationHeadPop scId head? pair1.2 = .ok s2 := by
      refine storeDonationHeadPop_ok_of_reply scId pair1.2 head? hInv1 ?_ ?_
      · intro rid r hPr
        obtain ⟨hObjR, _⟩ := donationHeadOf?_ok_resolves st scId sc rid r (by rw [hHead, hPr])
        have hNeSc : rid.toObjId ≠ scId.toObjId := by
          intro hEq; rw [hEq, hScObj] at hObjR; cases hObjR
        rw [storeObject_objects_ne st pair1.2 scId.toObjId rid.toObjId _ hNeSc hObjInv hS1]
        exact hObjR
      · intro rid r below hPr hPrev
        obtain ⟨b, hB⟩ := hBelow rid r below hPr hPrev
        have hNeSc : below.toObjId ≠ scId.toObjId := by
          intro hEq; rw [hEq, hScObj] at hB; cases hB
        refine ⟨b, ?_⟩
        rw [storeObject_objects_ne st pair1.2 scId.toObjId below.toObjId _ hNeSc hObjInv hS1]
        exact hB
    simp only []
    rw [hClear]
    simp only []
    have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
    have hOwnerObj2 : s2.objects[owner.toObjId]? = some (.tcb ownerTcb) :=
      storeDonationHeadPop_tcb_eq hInv1 hClear owner.toObjId ownerTcb (by
        rw [storeObject_objects_ne st pair1.2 scId.toObjId owner.toObjId _ hScNeOwner.symm
          hObjInv hS1]
        exact hOwnerObj)
    have hRecvObj2 : s2.objects[receiver.toObjId]? = some (.tcb recvTcb) :=
      storeDonationHeadPop_tcb_eq hInv1 hClear receiver.toObjId recvTcb (by
        rw [storeObject_objects_ne st pair1.2 scId.toObjId receiver.toObjId _ hScNeRecv.symm
          hObjInv hS1]
        exact hRecvObj)
    have hOwnerNotResEq : owner.isReserved = false := Bool.eq_false_iff.mpr hOwnerNotRes
    have hLkOwner2 : lookupTcb s2 owner = some ownerTcb := by
      unfold lookupTcb SystemState.getTcb?
      rw [hOwnerNotResEq]
      simp only [Bool.false_eq_true, if_false]
      rw [hOwnerObj2]
    simp only [hLkOwner2]
    generalize hS3 : storeObject owner.toObjId
        (.tcb { ownerTcb with schedContextBinding := donationReturnBinding scId newOwner? }) s2
          = result3
    match result3, hS3 with
    | .ok pair3, hS3 =>
      have hInv3 : pair3.2.objects.invExt :=
        storeObject_preserves_objects_invExt s2 pair3.2 owner.toObjId _ hInv2 hS3
      have hRecvObj3 : pair3.2.objects[receiver.toObjId]? = some (.tcb recvTcb) := by
        rw [storeObject_objects_ne s2 pair3.2 owner.toObjId receiver.toObjId _
          hOwnerObjIdNeRecv.symm hInv2 hS3]
        exact hRecvObj2
      have hRecvNotResEq : receiver.isReserved = false := Bool.eq_false_iff.mpr hRecvNotRes
      have hLkRecv3 : lookupTcb pair3.2 receiver = some recvTcb := by
        unfold lookupTcb SystemState.getTcb?
        rw [hRecvNotResEq]
        simp only [Bool.false_eq_true, if_false]
        rw [hRecvObj3]
      simp only [hLkRecv3]
      generalize hS4 : storeObject receiver.toObjId
          (.tcb { recvTcb with schedContextBinding := .unbound }) pair3.2 = result4
      match result4, hS4 with
      | .ok pair4, hS4 =>
        simp only []
        exact ⟨_, rfl⟩

/-- AK1-A (I-H01): `cleanupPreReceiveDonationChecked` never errors under
    `ipcInvariantFull` combined with non-reservation of the participant
    thread IDs.

    This is the formal discharge of the "unreachable under invariants" claim
    cited at the `cleanupPreReceiveDonationChecked` call site in
    `endpointReceiveDual` (`IPC/DualQueue/Transport.lean`). The lemma
    dispatches by receiver binding:

    - `none` / `.unbound` / `.bound _`: structurally `.ok st` (discharged
      by unfolding the Checked function).
    - `.donated scId owner`: the operation invokes
      `returnDonatedSchedContext`, which under `donationOwnerValid` +
      non-reservation is fully machine-verified by
      `returnDonatedSchedContext_ok_under_invariants` above (four sequential
      object writes + two `lookupTcb` steps threaded via SchedContext/TCB
      type-disjointness — `schedContext_ne_tcb_at_objId` — and
      `donationOwnerValid_excludes_self_donation`; WS-OD OD3.2 added the
      reply-stack head clear and the head validation it needs).

    The only remaining hypotheses are `hObjInv` (witness that
    `st.objects.invExt` holds — already a cross-subsystem invariant),
    `hInv` (the full IPC invariant from which `donationOwnerValid` is
    extracted via `.2.2.2.2.2.2.2.2.2.2.2.1`), and non-reservation of the
    participant thread IDs, which is enforced kernel-wide by the retype
    pipeline (`Lifecycle/Operations.lean:retypeFromUntyped` rejects
    sentinel/reserved IDs). All production call paths satisfy these
    preconditions. -/
theorem cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hChain : donationChainWellFormed st)
    (hStack : cleanupDonationStackValid st receiver)
    (hRecvNotRes : ¬receiver.isReserved = true)
    (hOwnerNotRes : ∀ recvTcb scId owner,
      lookupTcb st receiver = some recvTcb →
      recvTcb.schedContextBinding = .donated scId owner →
      ¬owner.isReserved = true) :
    ∃ st', cleanupPreReceiveDonationChecked st receiver = .ok st' := by
  -- AN3-B.2: Named projection replaces the legacy `.2.2.2.2.2.2.2.2.2.2.2.1`
  -- deep tuple chain.  `hInv.donationOwnerValid` dispatches through the
  -- `ipcInvariantFull.donationOwnerValid` simp projection.  The arity of
  -- `ipcInvariantFull` has grown over time (AG1-C added `uniqueWaiters` as
  -- the 15th conjunct; AJ1-B added `blockedOnReplyHasTarget` as the 16th),
  -- so this migration insulates the theorem from any further arity changes.
  have hDOV : donationOwnerValid st := hInv.donationOwnerValid
  unfold cleanupPreReceiveDonationChecked
  cases hLk : lookupTcb st receiver with
  | none => exact ⟨st, rfl⟩
  | some recvTcb =>
    show ∃ st', (match recvTcb.schedContextBinding with
      | .donated scId owner => returnDonatedSchedContextResolved st receiver scId owner
      | _ => .ok st) = .ok st'
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact ⟨st, rfl⟩
    | bound _ => exact ⟨st, rfl⟩
    | donated scId owner =>
      -- Derive donated-path success from donationOwnerValid + non-reservation.
      -- WS-OD OD3.2: the pop's head validation comes from the chain invariant,
      -- which is what says a context's stack head resolves to a Reply donating
      -- that context.  It is a conjunct of `ipcReachable` rather than of
      -- `ipcInvariantFull`, so it is stated here rather than projected.
      -- WS-OD OD4.4: the resolved return succeeds when *both* halves do — the
      -- resolver, which the chain invariant makes total
      -- (`replyStackOuterCallerResolves_of_chainWellFormed`), and the pop at the
      -- answer it gives, whose outer-caller guard is the first clause of the
      -- stack obligation.  Reading the resolver's `.error` as an empty stack
      -- here would be the conflation `replyStackOuterCaller?`'s docstring
      -- forbids, so it is ruled out rather than absorbed.
      obtain ⟨scObj, hScObj⟩ : ∃ sc, st.getSchedContext? scId = some sc := by
        obtain ⟨⟨sc, hSc, _⟩, _⟩ := hDOV receiver recvTcb scId owner
          (lookupTcb_some_objects st receiver recvTcb hLk) hBind
        exact ⟨sc, (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hSc⟩
      obtain ⟨newOwner?, hRes⟩ :=
        replyStackOuterCallerResolves_of_chainWellFormed st scId hChain scObj
          ((SystemState.getSchedContext?_eq_some_iff st scId scObj).mp hScObj)
      show ∃ st', returnDonatedSchedContextResolved st receiver scId owner = .ok st'
      rw [returnDonatedSchedContextResolved_of_resolved hRes]
      exact returnDonatedSchedContext_ok_under_invariants
        st receiver recvTcb scId owner hObjInv hDOV
        (donationHeadResolves_of_chainWellFormed st scId hChain) hLk hBind hRecvNotRes
        (hOwnerNotRes recvTcb scId owner hLk hBind) newOwner?
        ((hStack recvTcb scId owner hLk hBind) newOwner? hRes).1

/-- AK1-A (I-H01): Plan-compliant alias. The plan specifies the lemma name
    `cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull` at the
    top-level function's naming scope. Since we retain two functions
    (`cleanupPreReceiveDonation` for the defensive frame-lemma
    infrastructure and `cleanupPreReceiveDonationChecked` for production
    use), this alias provides the plan-named entry point. -/
abbrev cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull :=
  @cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull

end SeLe4n.Kernel
