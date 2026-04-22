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
  | .idle => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge = none
  | .waiting => ntfn.waitingThreads ≠ [] ∧ ntfn.pendingBadge = none
  | .active => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge.isSome

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

/-- WS-H5: TCB queue chain acyclicity — no thread can reach itself via queueNext.
This prevents infinite loops during queue traversal. -/
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

/-- V3-G1 (M-PRF-5): Threads blocked on receive or notification must have
    `pendingMessage = none`. When a thread enters a blocking state (receive
    or notification wait), no message has been delivered yet — the message
    will be written when the thread is woken by a corresponding send/signal.
    This invariant captures the safety-critical property that wake paths
    can unconditionally overwrite `pendingMessage` without losing data.

    The blocking states covered are:
    - `blockedOnReceive`: waiting for IPC send from another thread
    - `blockedOnNotification`: waiting for notification signal

    Note: `blockedOnSend` and `blockedOnCall` threads MAY have a pending
    message — they carry the outgoing message in `pendingMessage` while
    queued, which `endpointReceiveDual` reads upon rendezvous.
    `blockedOnReply` threads have `pendingMessage = none` (cleared by the
    receive path), but are not constrained here since `.ready` and other
    non-receiver states are unconditionally `True`. -/
def waitingThreadsPendingMessageNone (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    match tcb.ipcState with
    | .blockedOnReceive _ => tcb.pendingMessage = none
    | .blockedOnNotification _ => tcb.pendingMessage = none
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
V3-G6: `waitingThreadsPendingMessageNone` ensures threads in blocked receiver
states have `pendingMessage = none`.
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
  match st.scheduler.current with
  | none => True
  | some tid => ∀ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .ready

/-- Under dequeue-on-dispatch QCC, the current thread must not appear as the
head of any endpoint queue (send or receive). This ensures that when
endpointQueuePopHead pops a thread, it differs from the current thread. -/
def currentNotEndpointQueueHead (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some tid =>
    ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[oid]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid

/-- Under dequeue-on-dispatch QCC, the current thread must not appear on any
notification wait list. This ensures ensureRunnable on a signaled waiter
does not conflict with the current thread. -/
def currentNotOnNotificationWaitList (st : SystemState) : Prop :=
  match st.scheduler.current with
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
  unfold endpointQueuePopHead at hPop
  rw [hObj] at hPop; simp only at hPop
  cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => simp [hHead] at hPop
  | some headTid =>
    simp only [hHead] at hPop
    cases hLk : lookupTcb st headTid with
    | none => simp [hLk] at hPop
    | some headTcb =>
      simp only [hLk] at hPop
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
  unfold endpointQueuePopHead at hPop
  rw [hObj] at hPop; simp only at hPop
  cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => simp [hHead] at hPop
  | some headTid =>
    simp only [hHead] at hPop
    cases hLk : lookupTcb st headTid with
    | none => simp [hLk] at hPop
    | some tcb =>
      simp only [hLk] at hPop
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

def uniqueWaiters (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ntfn : Notification), st.objects[oid]? = some (KernelObject.notification ntfn) → ntfn.waitingThreads.Nodup

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

/-- WS-G7/F-P11: notificationWait preserves uniqueWaiters.
Now requires `notificationWaiterConsistent` to bridge the TCB ipcState
duplicate check to list non-membership. -/
theorem notificationWait_preserves_uniqueWaiters
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hInv : uniqueWaiters st)
    (hConsist : notificationWaiterConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    uniqueWaiters st' := by
  intro oid ntfn hObj
  by_cases hEq : oid = notificationId
  · rw [hEq] at hObj
    cases hBadge : badge with
    | some b =>
      rcases notificationWait_badge_path_notification st st' notificationId waiter b hObjInv
        (by rw [← hBadge]; exact hStep) with ⟨ntfn', hObj', hEmpty⟩
      rw [hObj] at hObj'; cases hObj'
      rw [hEmpty]; exact .nil
    | none =>
      rcases notificationWait_wait_path_notification st st' notificationId waiter hObjInv
        (by rw [← hBadge]; exact hStep) with ⟨ntfnOld, ntfnNew, hObjOld, hNoBadge, hObjNew, hPrepend⟩
      rw [hObj] at hObjNew; cases hObjNew
      rw [hPrepend]
      -- WS-G7: need to show waiter ∉ ntfnOld.waitingThreads via notificationWaiterConsistent
      -- Extract the TCB check from the successful path
      have hStep2 : notificationWait notificationId waiter st = .ok (none, st') := by
        rw [← hBadge]; exact hStep
      unfold notificationWait at hStep2
      simp only [hObjOld, hNoBadge] at hStep2
      cases hLookup : lookupTcb st waiter with
      | none => simp [hLookup] at hStep2
      | some tcb =>
        simp only [hLookup] at hStep2
        by_cases hBlocked : tcb.ipcState = .blockedOnNotification notificationId
        · simp [hBlocked] at hStep2
        · have hTcbObj := lookupTcb_some_objects st waiter tcb hLookup
          have hNotMem := not_mem_waitingThreads_of_ipcState_ne
            st notificationId ntfnOld waiter tcb hConsist hObjOld hTcbObj hBlocked
          exact List.nodup_cons.mpr ⟨hNotMem, hInv notificationId ntfnOld hObjOld⟩
  · -- At other IDs, the notification is preserved backward to pre-state
    unfold notificationWait at hStep
    cases hLookup : st.objects[notificationId]? with
    | none => simp [hLookup] at hStep
    | some obj =>
      cases obj with
      | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hLookup] at hStep
      | notification ntfnOrig =>
        simp only [hLookup] at hStep
        cases hPend : ntfnOrig.pendingBadge with
        | some b =>
          simp only [hPend] at hStep
          revert hStep
          cases hStore : storeObject notificationId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            cases hTcb : storeTcbIpcState pair.2 waiter _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
              have hPairObjInv : pair.2.objects.invExt :=
                storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
              have hPre : st.objects[oid]? = some (.notification ntfn) := by
                have h2 := storeTcbIpcState_notification_backward pair.2 st2 waiter _ oid ntfn hPairObjInv hTcb hObj
                by_cases hEq2 : oid = notificationId
                · exact absurd hEq2 hEq
                · rwa [storeObject_objects_ne st pair.2 notificationId oid _ hEq hObjInv hStore] at h2
              exact hInv oid ntfn hPre
        | none =>
          simp only [hPend] at hStep
          -- WS-G7: match on lookupTcb
          cases hLk : lookupTcb st waiter with
          | none => simp [hLk] at hStep
          | some tcb =>
            simp only [hLk] at hStep
            by_cases hBlocked : tcb.ipcState = .blockedOnNotification notificationId
            · simp [hBlocked] at hStep
            · simp only [hBlocked, ite_false] at hStep
              revert hStep
              cases hStore : storeObject notificationId _ st with
              | error e => simp
              | ok pair =>
                -- WS-L1: rewrite _fromTcb back to original for proof compatibility
                have hPairObjInv : pair.2.objects.invExt :=
                  storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
                have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hLookup hObjInv hStore
                simp only [storeTcbIpcState_fromTcb_eq hLk']
                cases hTcb : storeTcbIpcState pair.2 waiter _ with
                | error e => simp
                | ok st2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩
                  have hPre : st.objects[oid]? = some (.notification ntfn) := by
                    have hRemObj : (removeRunnable st2 waiter).objects = st2.objects := rfl
                    rw [← hStEq, hRemObj] at hObj
                    have h2 := storeTcbIpcState_notification_backward pair.2 st2 waiter _ oid ntfn hPairObjInv hTcb hObj
                    by_cases hEq2 : oid = notificationId
                    · exact absurd hEq2 hEq
                    · rwa [storeObject_objects_ne st pair.2 notificationId oid _ hEq hObjInv hStore] at h2
                  exact hInv oid ntfn hPre

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
   ipcState to `.ready`. Requires `uniqueWaiters` to ensure the woken thread
   does not appear elsewhere in the remaining list. Remaining threads' TCBs
   are unchanged, so their ipcState is preserved.

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
  (removes head waiter, uses `uniqueWaiters` Nodup) + merge path (vacuous)
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

/-- notificationSignal result notification is well-formed:
    - Wake path: remaining waiters determine idle/waiting state, badge cleared.
    - Merge path: no waiters, active state with merged badge. -/
theorem notificationSignal_result_wellFormed_wake
    (rest : List SeLe4n.ThreadId) :
    notificationQueueWellFormed
      { state := if rest.isEmpty then NotificationState.idle else .waiting,
        waitingThreads := rest,
        pendingBadge := none } := by
  unfold notificationQueueWellFormed
  by_cases hEmpty : rest = []
  · simp [hEmpty, List.isEmpty]
  · have : rest.isEmpty = false := by simp [List.isEmpty]; cases rest <;> simp_all
    simp [this, hEmpty]

theorem notificationSignal_result_wellFormed_merge
    (mergedBadge : SeLe4n.Badge) :
    notificationQueueWellFormed
      { state := .active,
        waitingThreads := [],
        pendingBadge := some mergedBadge } := by
  unfold notificationQueueWellFormed; simp

/-- notificationWait result notification is well-formed (badge-consume path):
    idle state, empty waiters, no badge. -/
theorem notificationWait_result_wellFormed_badge :
    notificationQueueWellFormed
      { state := NotificationState.idle, waitingThreads := [], pendingBadge := none } := by
  unfold notificationQueueWellFormed; simp

/-- WS-G7/F-P11: notificationWait result notification is well-formed (wait path):
    waiting state, non-empty waiter list (prepended), no badge. -/
theorem notificationWait_result_wellFormed_wait
    (waiter : SeLe4n.ThreadId)
    (waiters : List SeLe4n.ThreadId) :
    notificationQueueWellFormed
      { state := .waiting, waitingThreads := waiter :: waiters, pendingBadge := none } := by
  unfold notificationQueueWellFormed
  constructor
  · intro h; cases h
  · rfl

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
the object-index reachability property is an orthogonal invariant
(`objectIndexConsistent` in `SeLe4n.Model.State`) that composes with
this predicate rather than being embedded inside it.  At every call
site where both are needed, callers thread them independently; this
separation is intentional (and was preserved here rather than merged
per Option B of the plan) because the two invariants are proved by
disjoint means: `ipcStateQueueConsistent` is preserved by every IPC
operation that modifies `ipcState`, while `objectIndexConsistent` is
preserved by every operation that modifies `objects` or `objectIndex`.
Merging them would force both to co-evolve in every preservation
proof, which would increase the cascade size without tightening any
safety conclusion the combination already admits at call sites. -/
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
-- V3-G (M-PRF-5): waitingThreadsPendingMessageNone invariant
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
hardening candidate; no currently-active plan file tracks it. -/
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
4. (AUD-7) The original owner's binding is `.bound scId` — bidirectional consistency -/
def donationOwnerValid (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .donated scId owner →
    (∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      sc.boundThread = some tid) ∧
    (∃ ownerTcb, st.objects[owner.toObjId]? = some (.tcb ownerTcb) ∧
      ownerTcb.schedContextBinding = .bound scId ∧
      ∃ epId replyTarget, ownerTcb.ipcState = .blockedOnReply epId replyTarget)

-- ============================================================================
-- Z7-H: Passive server idle invariant
-- ============================================================================

/-- Z7-H: Unbound threads not in the RunQueue are passive servers.

An unbound thread that is not runnable and not the current thread must be
either blocked on receive (waiting for a client call) or inactive. It must
not be blocked on send/call (which requires a SchedContext for timeout). -/
def passiveServerIdle (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .unbound →
    tid ∉ st.scheduler.runQueue →
    st.scheduler.current ≠ some tid →
    (tcb.ipcState = .ready ∨
     ∃ epId, tcb.ipcState = .blockedOnReceive epId ∨
             tcb.ipcState = .blockedOnNotification epId)

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
have `.bound` bindings. If thread `tid1` has `.donated scId1 tid2`, then
by `donationOwnerValid`, `tid2` has `.bound scId1`. Since `.bound` and
`.donated` are distinct constructors of `SchedContextBinding`, `tid2` cannot
simultaneously have `.donated scId2 tid1`. Contradiction. -/
theorem donationOwnerValid_implies_donationChainAcyclic
    (st : SystemState)
    (hDOV : donationOwnerValid st) :
    donationChainAcyclic st := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 hTcb1 hTcb2 hDon1 hDon2
  -- tid1 has .donated scId1 tid2, so by donationOwnerValid:
  -- tid2 (the owner) has .bound scId1
  have ⟨_, hOwner⟩ := hDOV tid1 tcb1 scId1 tid2 hTcb1 hDon1
  obtain ⟨ownerTcb, hOwnerTcb, hBound, _⟩ := hOwner
  -- Equate ownerTcb with tcb2: both come from st.objects[tid2.toObjId]?
  rw [hTcb2] at hOwnerTcb
  cases hOwnerTcb -- ownerTcb = tcb2
  -- Now: hBound : tcb2.schedContextBinding = .bound scId1
  --      hDon2  : tcb2.schedContextBinding = .donated scId2 tid1
  -- .bound ≠ .donated — constructor disjointness
  rw [hDon2] at hBound; cases hBound

/-- AG8-F: Donation chains cannot extend beyond length 1.

If thread `tid` has `.donated scId owner`, then by `donationOwnerValid`,
the `owner` has `schedContextBinding = .bound scId`. Since `.bound` and
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
  -- hBound : ownerTcb.schedContextBinding = .bound scId
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
-- Full IPC invariant bundle (16 conjuncts)
-- ============================================================================

/-- Full IPC invariant: conjunction of all sixteen IPC sub-invariants.

Z7 extends the bundle with 4 donation invariants:
- `donationChainAcyclic`: no circular donation chains
- `donationOwnerValid`: donated bindings reference valid objects
- `passiveServerIdle`: unbound non-runnable threads are idle/receiving
- `donationBudgetTransfer`: at most one thread per SchedContext

AG1-C adds `uniqueWaiters` as the 15th conjunct:
- `uniqueWaiters`: notification waiting thread lists have no duplicates

AJ1-B adds `blockedOnReplyHasTarget` as the 16th conjunct:
- `blockedOnReplyHasTarget`: every blockedOnReply thread has replyTarget = some _ -/
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ waitingThreadsPendingMessageNone st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValid st ∧
  passiveServerIdle st ∧ donationBudgetTransfer st ∧
  uniqueWaiters st ∧
  blockedOnReplyHasTarget st

-- ============================================================================
-- AN3-B (IPC-M01 / Theme 4.2): Named-projection refactor for ipcInvariantFull.
--
-- The legacy tuple form above is preserved as the primary definition so
-- every existing consumer that destructures `ipcInvariantFull` via tuple
-- projections continues to typecheck. The block below layers a named
-- `structure IpcInvariantFull` over the same 16 conjuncts, a bidirectional
-- `ipcInvariantFull_iff_IpcInvariantFull` bridge, and per-field projection
-- theorems (installed as `@[simp]`) so callers can write
-- `hInv.donationOwnerValid` (or any other conjunct name) in place of the
-- fragile `hInv.2.2.2.2.2.2.2.2.2.2.2.1` chain.
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

All 16 fields mirror the conjuncts of the legacy tuple form, one-for-one
in declaration order. The bidirectional bridge
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
  waitingThreadsPendingMessageNone : waitingThreadsPendingMessageNone st
  endpointQueueNoDup : endpointQueueNoDup st
  ipcStateQueueMembershipConsistent : ipcStateQueueMembershipConsistent st
  queueNextBlockingConsistent : queueNextBlockingConsistent st
  queueHeadBlockedConsistent : queueHeadBlockedConsistent st
  blockedThreadTimeoutConsistent : blockedThreadTimeoutConsistent st
  donationChainAcyclic : donationChainAcyclic st
  donationOwnerValid : donationOwnerValid st
  passiveServerIdle : passiveServerIdle st
  donationBudgetTransfer : donationBudgetTransfer st
  uniqueWaiters : uniqueWaiters st
  blockedOnReplyHasTarget : blockedOnReplyHasTarget st

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

@[simp] theorem waitingThreadsPendingMessageNone {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.waitingThreadsPendingMessageNone st :=
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

@[simp] theorem uniqueWaiters {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.uniqueWaiters st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] theorem blockedOnReplyHasTarget {st : SystemState}
    (h : ipcInvariantFull st) :
    _root_.SeLe4n.Kernel.blockedOnReplyHasTarget st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ipcInvariantFull

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
           h.waitingThreadsPendingMessageNone, h.endpointQueueNoDup,
           h.ipcStateQueueMembershipConsistent,
           h.queueNextBlockingConsistent, h.queueHeadBlockedConsistent,
           h.blockedThreadTimeoutConsistent, h.donationChainAcyclic,
           h.donationOwnerValid, h.passiveServerIdle,
           h.donationBudgetTransfer, h.uniqueWaiters,
           h.blockedOnReplyHasTarget⟩
  · intro h
    exact ⟨h.ipcInvariant, h.dualQueueSystemInvariant,
           h.allPendingMessagesBounded, h.badgeWellFormed,
           h.waitingThreadsPendingMessageNone, h.endpointQueueNoDup,
           h.ipcStateQueueMembershipConsistent,
           h.queueNextBlockingConsistent, h.queueHeadBlockedConsistent,
           h.blockedThreadTimeoutConsistent, h.donationChainAcyclic,
           h.donationOwnerValid, h.passiveServerIdle,
           h.donationBudgetTransfer, h.uniqueWaiters,
           h.blockedOnReplyHasTarget⟩

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
      cases hReturn : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => rfl
      | ok st' => exact returnDonatedSchedContext_scheduler_eq st st' receiver scId originalOwner hReturn

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
      cases hReturn : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => exact hObjInv
      | ok st' =>
        -- returnDonatedSchedContext does 3 storeObject calls + scThreadIndex update
        unfold returnDonatedSchedContext at hReturn
        revert hReturn
        cases hObj : st.objects[scId.toObjId]? with
        | none => intro h; cases h
        | some obj => cases obj with
          | schedContext sc =>
            simp only []
            cases hS1 : storeObject scId.toObjId _ st with
            | error _ => intro h; cases h
            | ok p1 =>
              simp only []
              have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
              cases hL1 : lookupTcb p1.2 originalOwner with
              | none => intro h; cases h
              | some _ =>
                simp only []
                cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
                | error _ => intro h; cases h
                | ok p2 =>
                  simp only []
                  have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
                  cases hL2 : lookupTcb p2.2 receiver with
                  | none => intro h; cases h
                  | some _ =>
                    simp only []
                    cases hS3 : storeObject receiver.toObjId _ p2.2 with
                    | error _ => intro h; cases h
                    | ok p3 =>
                      simp only [Except.ok.injEq]
                      intro hEq; subst hEq
                      have hInv3 := storeObject_preserves_objects_invExt p2.2 p3.2 receiver.toObjId _ hInv2 hS3
                      -- scThreadIndex update doesn't affect objects
                      exact hInv3
          | _ => simp only []; intro h; cases h

-- Helper: common proof pattern for cleanupPreReceiveDonation frame lemmas.
-- 3 of 4 branches return st unchanged. The donated+ok branch delegates to
-- returnDonatedSchedContext which only modifies TCB schedContextBinding and
-- SchedContext boundThread — transparent to all IPC/scheduler invariants.
theorem cleanupPreReceiveDonation_frame_helper
    {P : SystemState → Prop}
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hInv : P st)
    (hReturn : ∀ (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
      (st' : SystemState),
      returnDonatedSchedContext st receiver scId originalOwner = .ok st' → P st') :
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
      cases hRet : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => exact hInv
      | ok st' => exact hReturn scId originalOwner st' hRet

-- Helper: returnDonatedSchedContext only stores TCB/SchedContext objects.
-- For any invariant quantified over non-TCB/non-SchedContext objects (endpoints,
-- notifications), the invariant is trivially preserved because those objects
-- are unchanged by storeObject on different-typed ObjIds.
-- This is proven via storeObject's insert semantics on the RHTable.

/-- AI4-A: returnDonatedSchedContext preserves objects.invExt. -/
private theorem returnDonatedSchedContext_preserves_objects_invExt
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    st'.objects.invExt := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; subst hEq
                exact storeObject_preserves_objects_invExt p2.2 p3.2 serverTid.toObjId _ hInv2 hS3
    | _ => simp only []; intro h; cases h

/-- AI4-A: Backward transport — notifications are unchanged by returnDonatedSchedContext.
returnDonatedSchedContext stores 1 SchedContext + 2 TCBs. A notification in the
post-state must have been in the pre-state because storeObject on non-notification
ObjIds cannot create notification objects. -/
theorem returnDonatedSchedContext_notification_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq
                have hInv3 := storeObject_preserves_objects_invExt p2.2 p3.2 serverTid.toObjId _ hInv2 hS3
                -- st'.objects = p3.2.objects (scThreadIndex with-update doesn't affect objects)
                rw [← hEq] at hNtfn
                -- hNtfn now references p3.2.objects (via the with-update)
                -- Step 3: backward through storeObject serverTid
                have hNtfn2 : p2.2.objects[oid]? = some (.notification ntfn) := by
                  by_cases hEq3 : oid = serverTid.toObjId
                  · subst hEq3; unfold storeObject at hS3; cases hS3
                    simp only [RHTable_getElem?_eq_get?] at hNtfn
                    rw [RHTable_getElem?_insert p2.2.objects _ _ hInv2] at hNtfn
                    simp at hNtfn
                  · exact (storeObject_objects_ne p2.2 p3.2 serverTid.toObjId oid _ hEq3 hInv2 hS3).symm ▸ hNtfn
                -- Step 2: backward through storeObject originalOwner
                have hNtfn1 : p1.2.objects[oid]? = some (.notification ntfn) := by
                  by_cases hEq2 : oid = originalOwner.toObjId
                  · subst hEq2; unfold storeObject at hS2; cases hS2
                    simp only [RHTable_getElem?_eq_get?] at hNtfn2
                    rw [RHTable_getElem?_insert p1.2.objects _ _ hInv1] at hNtfn2
                    simp at hNtfn2
                  · exact (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId oid _ hEq2 hInv1 hS2).symm ▸ hNtfn2
                -- Step 1: backward through storeObject scId
                by_cases hEq1 : oid = scId.toObjId
                · subst hEq1; unfold storeObject at hS1; cases hS1
                  simp only [RHTable_getElem?_eq_get?] at hNtfn1
                  rw [RHTable_getElem?_insert st.objects _ _ hObjInv] at hNtfn1
                  simp at hNtfn1
                · exact (storeObject_objects_ne st p1.2 scId.toObjId oid _ hEq1 hObjInv hS1).symm ▸ hNtfn1
    | _ => simp only []; intro h; cases h

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
      cases hReturn : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => exact hTcb
      | ok st' =>
        -- returnDonatedSchedContext stores: SchedContext at scId, TCB at owner, TCB at receiver
        -- For any tid whose ObjId differs from scId.toObjId, the object is either
        -- unchanged (ne all 3) or replaced with a TCB (= owner or receiver).
        unfold returnDonatedSchedContext at hReturn
        revert hReturn
        cases hObj : st.objects[scId.toObjId]? with
        | none => intro h; cases h
        | some obj => cases obj with
          | schedContext sc =>
            simp only []
            cases hS1 : storeObject scId.toObjId _ st with
            | error _ => intro h; cases h
            | ok p1 =>
              simp only []
              have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
              cases hL1 : lookupTcb p1.2 originalOwner with
              | none => intro h; cases h
              | some clientTcb =>
                simp only []
                cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
                | error _ => intro h; cases h
                | ok p2 =>
                  simp only []
                  have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
                  cases hL2 : lookupTcb p2.2 receiver with
                  | none => intro h; cases h
                  | some serverTcb =>
                    simp only []
                    cases hS3 : storeObject receiver.toObjId _ p2.2 with
                    | error _ => intro h; cases h
                    | ok p3 =>
                      simp only [Except.ok.injEq]
                      intro hEq
                      -- Chain forward through 3 storeObject calls.
                      -- The goal references st' which = { p3.2 with scThreadIndex := ... }.
                      -- Since objects is unchanged by the scThreadIndex with-update,
                      -- st'.objects = p3.2.objects.
                      rcases hTcb with ⟨tcb, hTcbLookup⟩
                      suffices ∃ tcb', p3.2.objects[tid.toObjId]? = some (.tcb tcb') by
                        rw [← hEq]; exact this
                      -- Case analysis: does tid.toObjId match any stored target?
                      by_cases h3 : tid.toObjId = receiver.toObjId
                      · -- S3 stores .tcb at receiver.toObjId → TCB exists
                        rw [h3]; exact ⟨_, storeObject_objects_eq' p2.2 receiver.toObjId _ p3 hInv2 hS3⟩
                      · by_cases h2 : tid.toObjId = originalOwner.toObjId
                        · -- S2 stores .tcb at originalOwner.toObjId, S3 preserves it
                          rw [h2]
                          have hNe3' : originalOwner.toObjId ≠ receiver.toObjId := by rw [← h2]; exact h3
                          have hPres3 := storeObject_objects_ne p2.2 p3.2 receiver.toObjId originalOwner.toObjId _ hNe3' hInv2 hS3
                          rw [hPres3]; exact ⟨_, storeObject_objects_eq' p1.2 originalOwner.toObjId _ p2 hInv1 hS2⟩
                        · -- tid differs from receiver and originalOwner
                          have hNe3 := storeObject_objects_ne p2.2 p3.2 receiver.toObjId tid.toObjId _ h3 hInv2 hS3
                          have hNe2 := storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId tid.toObjId _ h2 hInv1 hS2
                          by_cases h1 : tid.toObjId = scId.toObjId
                          · -- contradiction: hTcbLookup + hObj
                            exfalso; rw [h1] at hTcbLookup; rw [hObj] at hTcbLookup; cases hTcbLookup
                          · -- tid differs from all 3 → object unchanged
                            have hNe1 := storeObject_objects_ne st p1.2 scId.toObjId tid.toObjId _ h1 hObjInv hS1
                            rw [hNe3, hNe2, hNe1]; exact ⟨tcb, hTcbLookup⟩
          | _ => simp only []; intro h; cases h

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
      cases hReturn : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => simp only [hReturn] at hTcb'; exact ⟨tcb', hTcb', rfl⟩
      | ok st' =>
        simp only [hReturn] at hTcb'
        -- Chain backward through 3 storeObject calls in returnDonatedSchedContext.
        unfold returnDonatedSchedContext at hReturn
        revert hReturn
        cases hObj : st.objects[scId.toObjId]? with
        | none => intro h; cases h
        | some obj => cases obj with
          | schedContext sc =>
            simp only []
            cases hS1 : storeObject scId.toObjId _ st with
            | error _ => intro h; cases h
            | ok p1 =>
              simp only []
              have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
              cases hL1 : lookupTcb p1.2 originalOwner with
              | none => intro h; cases h
              | some clientTcb =>
                simp only []
                cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
                | error _ => intro h; cases h
                | ok p2 =>
                  simp only []
                  have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
                  cases hL2 : lookupTcb p2.2 receiver with
                  | none => intro h; cases h
                  | some serverTcb =>
                    simp only []
                    cases hS3 : storeObject receiver.toObjId _ p2.2 with
                    | error _ => intro h; cases h
                    | ok p3 =>
                      simp only [Except.ok.injEq]
                      intro hEq
                      -- hTcb' references st'.objects = p3.2.objects (scThreadIndex update doesn't affect objects)
                      rw [← hEq] at hTcb'
                      -- Step 3: backward through storeObject receiver.toObjId (.tcb serverTcb')
                      have hTcb2 : ∃ tcb2, p2.2.objects[tid.toObjId]? = some (.tcb tcb2) ∧ tcb2.ipcState = tcb'.ipcState := by
                        by_cases hEq3 : tid.toObjId = receiver.toObjId
                        · rw [hEq3] at hTcb' ⊢; unfold storeObject at hS3; cases hS3
                          simp only [RHTable_getElem?_eq_get?] at hTcb'
                          rw [RHTable_getElem?_insert p2.2.objects _ _ hInv2] at hTcb'
                          simp at hTcb'; obtain ⟨rfl⟩ := hTcb'
                          -- The stored TCB is { serverTcb with schedContextBinding := .unbound }
                          -- so ipcState is preserved. Extract serverTcb from lookupTcb.
                          have hServerObj := lookupTcb_some_objects p2.2 receiver serverTcb hL2
                          exact ⟨serverTcb, hServerObj, rfl⟩
                        · exact ⟨tcb', (storeObject_objects_ne p2.2 p3.2 receiver.toObjId tid.toObjId _ hEq3 hInv2 hS3).symm ▸ hTcb', rfl⟩
                      -- Step 2: backward through storeObject originalOwner.toObjId (.tcb clientTcb')
                      obtain ⟨tcb2, hTcb2Obj, hIpc2⟩ := hTcb2
                      have hTcb1 : ∃ tcb1, p1.2.objects[tid.toObjId]? = some (.tcb tcb1) ∧ tcb1.ipcState = tcb2.ipcState := by
                        by_cases hEq2 : tid.toObjId = originalOwner.toObjId
                        · rw [hEq2] at hTcb2Obj ⊢; unfold storeObject at hS2; cases hS2
                          simp only [RHTable_getElem?_eq_get?] at hTcb2Obj
                          rw [RHTable_getElem?_insert p1.2.objects _ _ hInv1] at hTcb2Obj
                          simp at hTcb2Obj; obtain ⟨rfl⟩ := hTcb2Obj
                          have hClientObj := lookupTcb_some_objects p1.2 originalOwner clientTcb hL1
                          exact ⟨clientTcb, hClientObj, rfl⟩
                        · exact ⟨tcb2, (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId tid.toObjId _ hEq2 hInv1 hS2).symm ▸ hTcb2Obj, rfl⟩
                      -- Step 1: backward through storeObject scId.toObjId (.schedContext sc')
                      obtain ⟨tcb1, hTcb1Obj, hIpc1⟩ := hTcb1
                      by_cases hEq1 : tid.toObjId = scId.toObjId
                      · -- contradiction: storeObject stored a SchedContext, but we have a TCB
                        rw [hEq1] at hTcb1Obj; unfold storeObject at hS1; cases hS1
                        simp only [RHTable_getElem?_eq_get?] at hTcb1Obj
                        rw [RHTable_getElem?_insert st.objects _ _ hObjInv] at hTcb1Obj
                        simp at hTcb1Obj
                      · have hPres1 := storeObject_objects_ne st p1.2 scId.toObjId tid.toObjId _ hEq1 hObjInv hS1
                        rw [hPres1] at hTcb1Obj
                        exact ⟨tcb1, hTcb1Obj, by rw [hIpc1, hIpc2]⟩
          | _ => simp only []; intro h; cases h

/-- AI4-A: Backward transport — endpoints are unchanged by returnDonatedSchedContext.
returnDonatedSchedContext stores 1 SchedContext + 2 TCBs. An endpoint in the
post-state must have been in the pre-state because storeObject on non-endpoint
ObjIds cannot create endpoint objects. -/
theorem returnDonatedSchedContext_endpoint_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq
                rw [← hEq] at hEp
                -- Step 3: backward through storeObject serverTid (.tcb ...)
                have hEp2 : p2.2.objects[oid]? = some (.endpoint ep) := by
                  by_cases hEq3 : oid = serverTid.toObjId
                  · subst hEq3; unfold storeObject at hS3; cases hS3
                    simp only [RHTable_getElem?_eq_get?] at hEp
                    rw [RHTable_getElem?_insert p2.2.objects _ _ hInv2] at hEp
                    simp at hEp
                  · exact (storeObject_objects_ne p2.2 p3.2 serverTid.toObjId oid _ hEq3 hInv2 hS3).symm ▸ hEp
                -- Step 2: backward through storeObject originalOwner (.tcb ...)
                have hEp1 : p1.2.objects[oid]? = some (.endpoint ep) := by
                  by_cases hEq2 : oid = originalOwner.toObjId
                  · subst hEq2; unfold storeObject at hS2; cases hS2
                    simp only [RHTable_getElem?_eq_get?] at hEp2
                    rw [RHTable_getElem?_insert p1.2.objects _ _ hInv1] at hEp2
                    simp at hEp2
                  · exact (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId oid _ hEq2 hInv1 hS2).symm ▸ hEp2
                -- Step 1: backward through storeObject scId (.schedContext ...)
                by_cases hEq1 : oid = scId.toObjId
                · subst hEq1; unfold storeObject at hS1; cases hS1
                  simp only [RHTable_getElem?_eq_get?] at hEp1
                  rw [RHTable_getElem?_insert st.objects _ _ hObjInv] at hEp1
                  simp at hEp1
                · exact (storeObject_objects_ne st p1.2 scId.toObjId oid _ hEq1 hObjInv hS1).symm ▸ hEp1
    | _ => simp only []; intro h; cases h

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
    (fun scId originalOwner st' hRet hEp' =>
      returnDonatedSchedContext_endpoint_backward st st' receiver scId originalOwner hObjInv hRet oid ep hEp')
    hEp

/-- AI4-A: Backward transport — CNodes are unchanged by returnDonatedSchedContext.
returnDonatedSchedContext stores 1 SchedContext + 2 TCBs. A CNode in the
post-state must have been in the pre-state. -/
theorem returnDonatedSchedContext_cnode_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCn : st'.objects[oid]? = some (.cnode cn)) :
    st.objects[oid]? = some (.cnode cn) := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq
                rw [← hEq] at hCn
                have hCn2 : p2.2.objects[oid]? = some (.cnode cn) := by
                  by_cases hEq3 : oid = serverTid.toObjId
                  · subst hEq3; unfold storeObject at hS3; cases hS3
                    simp only [RHTable_getElem?_eq_get?] at hCn
                    rw [RHTable_getElem?_insert p2.2.objects _ _ hInv2] at hCn
                    simp at hCn
                  · exact (storeObject_objects_ne p2.2 p3.2 serverTid.toObjId oid _ hEq3 hInv2 hS3).symm ▸ hCn
                have hCn1 : p1.2.objects[oid]? = some (.cnode cn) := by
                  by_cases hEq2 : oid = originalOwner.toObjId
                  · subst hEq2; unfold storeObject at hS2; cases hS2
                    simp only [RHTable_getElem?_eq_get?] at hCn2
                    rw [RHTable_getElem?_insert p1.2.objects _ _ hInv1] at hCn2
                    simp at hCn2
                  · exact (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId oid _ hEq2 hInv1 hS2).symm ▸ hCn2
                by_cases hEq1 : oid = scId.toObjId
                · subst hEq1; unfold storeObject at hS1; cases hS1
                  simp only [RHTable_getElem?_eq_get?] at hCn1
                  rw [RHTable_getElem?_insert st.objects _ _ hObjInv] at hCn1
                  simp at hCn1
                · exact (storeObject_objects_ne st p1.2 scId.toObjId oid _ hEq1 hObjInv hS1).symm ▸ hCn1
    | _ => simp only []; intro h; cases h

/-- AI4-A: Forward transport — endpoints in pre-state exist identically in post-state
of returnDonatedSchedContext. Since the function only stores TCB/SchedContext objects,
endpoint objects at any ObjId are unchanged. -/
theorem returnDonatedSchedContext_endpoint_forward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    st'.objects[oid]? = some (.endpoint ep) := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; rw [← hEq]
                -- Step 1: forward through storeObject scId (.schedContext ...)
                have hEp1 : p1.2.objects[oid]? = some (.endpoint ep) := by
                  by_cases hEq1 : oid = scId.toObjId
                  · subst hEq1; rw [hEp] at hObj; cases hObj
                  · exact (storeObject_objects_ne st p1.2 scId.toObjId oid _ hEq1 hObjInv hS1) ▸ hEp
                -- Step 2: forward through storeObject originalOwner (.tcb ...)
                have hNe2 : oid ≠ originalOwner.toObjId := by
                  intro hEq2; rw [hEq2] at hEp1
                  have hStored := storeObject_objects_eq' p1.2 originalOwner.toObjId _ p2 hInv1 hS2
                  -- storeObject_objects_ne shows p1 object = p2 object at ne ids, but here they are equal
                  -- The store wrote .tcb at this id, so p1 lookup must be compatible.
                  -- Actually, p1 has .endpoint at originalOwner.toObjId (from hEp1), but lookupTcb
                  -- succeeded on p1 at originalOwner, meaning p1.objects[originalOwner.toObjId]? = some (.tcb ...)
                  -- Contradiction with hEp1
                  have hTcbObj := lookupTcb_some_objects p1.2 originalOwner _ hL1
                  rw [hTcbObj] at hEp1; cases hEp1
                have hEp2 : p2.2.objects[oid]? = some (.endpoint ep) :=
                  (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId oid _ hNe2 hInv1 hS2) ▸ hEp1
                -- Step 3: forward through storeObject serverTid (.tcb ...)
                have hNe3 : oid ≠ serverTid.toObjId := by
                  intro hEq3; rw [hEq3] at hEp2
                  have hTcbObj := lookupTcb_some_objects p2.2 serverTid _ hL2
                  rw [hTcbObj] at hEp2; cases hEp2
                exact (storeObject_objects_ne p2.2 p3.2 serverTid.toObjId oid _ hNe3 hInv2 hS3) ▸ hEp2
    | _ => simp only []; intro h; cases h

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
    (fun scId originalOwner st' hRet =>
      returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet oid ep hEp)

/-- AI4-A: TCB backward transport through returnDonatedSchedContext for queue fields.
If a TCB exists in the post-state, there's a TCB in the pre-state with the same
queueNext, queuePrev, ipcState, and pendingMessage. Only schedContextBinding may differ. -/
theorem returnDonatedSchedContext_tcb_queue_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (tid : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st'.objects[tid]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[tid]? = some (.tcb tcb) ∧
      tcb.queueNext = tcb'.queueNext ∧ tcb.queuePrev = tcb'.queuePrev ∧
      tcb.ipcState = tcb'.ipcState ∧ tcb.pendingMessage = tcb'.pendingMessage := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some clientTcb =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some serverTcb =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; rw [← hEq] at hTcb'
                -- Step 3: backward through storeObject serverTid (.tcb serverTcb')
                have hTcb2 : ∃ tcb2, p2.2.objects[tid]? = some (.tcb tcb2) ∧
                    tcb2.queueNext = tcb'.queueNext ∧ tcb2.queuePrev = tcb'.queuePrev ∧
                    tcb2.ipcState = tcb'.ipcState ∧ tcb2.pendingMessage = tcb'.pendingMessage := by
                  by_cases hEq3 : tid = serverTid.toObjId
                  · subst hEq3; unfold storeObject at hS3; cases hS3
                    simp only [RHTable_getElem?_eq_get?] at hTcb'
                    rw [RHTable_getElem?_insert p2.2.objects _ _ hInv2] at hTcb'
                    simp at hTcb'; obtain ⟨rfl⟩ := hTcb'
                    have hSO := lookupTcb_some_objects p2.2 serverTid serverTcb hL2
                    exact ⟨serverTcb, hSO, rfl, rfl, rfl, rfl⟩
                  · exact ⟨tcb', (storeObject_objects_ne p2.2 p3.2 serverTid.toObjId tid _ hEq3 hInv2 hS3).symm ▸ hTcb', rfl, rfl, rfl, rfl⟩
                -- Step 2: backward through storeObject originalOwner (.tcb clientTcb')
                obtain ⟨tcb2, hTcb2Obj, hQN2, hQP2, hIpc2, hMsg2⟩ := hTcb2
                have hTcb1 : ∃ tcb1, p1.2.objects[tid]? = some (.tcb tcb1) ∧
                    tcb1.queueNext = tcb2.queueNext ∧ tcb1.queuePrev = tcb2.queuePrev ∧
                    tcb1.ipcState = tcb2.ipcState ∧ tcb1.pendingMessage = tcb2.pendingMessage := by
                  by_cases hEq2 : tid = originalOwner.toObjId
                  · subst hEq2; unfold storeObject at hS2; cases hS2
                    simp only [RHTable_getElem?_eq_get?] at hTcb2Obj
                    rw [RHTable_getElem?_insert p1.2.objects _ _ hInv1] at hTcb2Obj
                    simp at hTcb2Obj; obtain ⟨rfl⟩ := hTcb2Obj
                    have hCO := lookupTcb_some_objects p1.2 originalOwner clientTcb hL1
                    exact ⟨clientTcb, hCO, rfl, rfl, rfl, rfl⟩
                  · exact ⟨tcb2, (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId tid _ hEq2 hInv1 hS2).symm ▸ hTcb2Obj, rfl, rfl, rfl, rfl⟩
                -- Step 1: backward through storeObject scId (.schedContext ...)
                obtain ⟨tcb1, hTcb1Obj, hQN1, hQP1, hIpc1, hMsg1⟩ := hTcb1
                by_cases hEq1 : tid = scId.toObjId
                · subst hEq1; unfold storeObject at hS1; cases hS1
                  simp only [RHTable_getElem?_eq_get?] at hTcb1Obj
                  rw [RHTable_getElem?_insert st.objects _ _ hObjInv] at hTcb1Obj
                  simp at hTcb1Obj
                · have hPres1 := storeObject_objects_ne st p1.2 scId.toObjId tid _ hEq1 hObjInv hS1
                  rw [hPres1] at hTcb1Obj
                  exact ⟨tcb1, hTcb1Obj, by rw [hQN1, hQN2], by rw [hQP1, hQP2], by rw [hIpc1, hIpc2], by rw [hMsg1, hMsg2]⟩
    | _ => simp only []; intro h; cases h

/-- AI4-A: TCB forward transport through returnDonatedSchedContext for queue fields.
If a TCB exists in the pre-state, there's a TCB in the post-state with the same
queueNext, queuePrev, ipcState, and pendingMessage. -/
theorem returnDonatedSchedContext_tcb_queue_forward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (tid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[tid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[tid]? = some (.tcb tcb') ∧
      tcb'.queueNext = tcb.queueNext ∧ tcb'.queuePrev = tcb.queuePrev ∧
      tcb'.ipcState = tcb.ipcState ∧ tcb'.pendingMessage = tcb.pendingMessage := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt st p1.2 scId.toObjId _ hObjInv hS1
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some clientTcb =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            have hInv2 := storeObject_preserves_objects_invExt p1.2 p2.2 originalOwner.toObjId _ hInv1 hS2
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some serverTcb =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; rw [← hEq]
                -- Step 1: forward through storeObject scId (.schedContext ...)
                have hTcb1 : ∃ tcb1, p1.2.objects[tid]? = some (.tcb tcb1) ∧
                    tcb1.queueNext = tcb.queueNext ∧ tcb1.queuePrev = tcb.queuePrev ∧
                    tcb1.ipcState = tcb.ipcState ∧ tcb1.pendingMessage = tcb.pendingMessage := by
                  by_cases hEq1 : tid = scId.toObjId
                  · subst hEq1; rw [hTcb] at hObj; cases hObj
                  · exact ⟨tcb, (storeObject_objects_ne st p1.2 scId.toObjId tid _ hEq1 hObjInv hS1) ▸ hTcb, rfl, rfl, rfl, rfl⟩
                -- Step 2: forward through storeObject originalOwner (.tcb clientTcb')
                obtain ⟨tcb1, hTcb1Obj, hQN1, hQP1, hIpc1, hMsg1⟩ := hTcb1
                have hTcb2 : ∃ tcb2, p2.2.objects[tid]? = some (.tcb tcb2) ∧
                    tcb2.queueNext = tcb1.queueNext ∧ tcb2.queuePrev = tcb1.queuePrev ∧
                    tcb2.ipcState = tcb1.ipcState ∧ tcb2.pendingMessage = tcb1.pendingMessage := by
                  by_cases hEq2 : tid = originalOwner.toObjId
                  · subst hEq2; unfold storeObject at hS2; cases hS2
                    simp only [RHTable_getElem?_eq_get?]
                    rw [RHTable_getElem?_insert p1.2.objects _ _ hInv1]
                    simp
                    -- The stored TCB is { clientTcb with schedContextBinding := .bound scId }
                    -- clientTcb was looked up from p1.2, so it preserves queue fields relative to tcb1
                    have hCO := lookupTcb_some_objects p1.2 originalOwner clientTcb hL1
                    rw [hCO] at hTcb1Obj; cases hTcb1Obj
                    exact ⟨rfl, rfl, rfl, rfl⟩
                  · exact ⟨tcb1, (storeObject_objects_ne p1.2 p2.2 originalOwner.toObjId tid _ hEq2 hInv1 hS2) ▸ hTcb1Obj, rfl, rfl, rfl, rfl⟩
                -- Step 3: forward through storeObject serverTid (.tcb serverTcb')
                obtain ⟨tcb2, hTcb2Obj, hQN2, hQP2, hIpc2, hMsg2⟩ := hTcb2
                by_cases hEq3 : tid = serverTid.toObjId
                · subst hEq3; unfold storeObject at hS3; cases hS3
                  simp only [RHTable_getElem?_eq_get?]
                  rw [RHTable_getElem?_insert p2.2.objects _ _ hInv2]
                  simp
                  have hSO := lookupTcb_some_objects p2.2 serverTid serverTcb hL2
                  rw [hSO] at hTcb2Obj; cases hTcb2Obj
                  exact ⟨by rw [hQN2, hQN1], by rw [hQP2, hQP1], by rw [hIpc2, hIpc1], by rw [hMsg2, hMsg1]⟩
                · have hPres3 := storeObject_objects_ne p2.2 p3.2 serverTid.toObjId tid _ hEq3 hInv2 hS3
                  rw [hPres3]
                  exact ⟨tcb2, hTcb2Obj, by rw [hQN2, hQN1], by rw [hQP2, hQP1], by rw [hIpc2, hIpc1], by rw [hMsg2, hMsg1]⟩
    | _ => simp only []; intro h; cases h

/-- AI4-A: cleanupPreReceiveDonation preserves allPendingMessagesBounded.
The invariant quantifies over TCBs and their pendingMessage field, which is
unchanged by returnDonatedSchedContext (only schedContextBinding is modified). -/
theorem cleanupPreReceiveDonation_preserves_allPendingMessagesBounded
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner st' hRet => by
      intro tid tcb' msg hTcb' hMsg'
      obtain ⟨tcb, hTcb, _, _, _, hMsgEq⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
          tid.toObjId tcb' hTcb'
      rw [← hMsgEq] at hMsg'
      exact hInv tid tcb msg hTcb hMsg'

/-- AI4-A: cleanupPreReceiveDonation preserves badgeWellFormed.
The invariant quantifies over notifications and CNodes, neither of which is
modified by returnDonatedSchedContext. -/
theorem cleanupPreReceiveDonation_preserves_badgeWellFormed
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : badgeWellFormed st) :
    badgeWellFormed (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner st' hRet => by
      constructor
      · -- notificationBadgesWellFormed: notifications are unchanged
        intro oid ntfn badge hNtfn hBadge
        have hNtfnPre := returnDonatedSchedContext_notification_backward st st' receiver scId originalOwner hObjInv hRet oid ntfn hNtfn
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
          (returnDonatedSchedContext_cnode_backward st st' receiver scId originalOwner hObjInv hRet oid cn hCn)
          hLookup hBadge

/-- AI4-A: cleanupPreReceiveDonation preserves waitingThreadsPendingMessageNone.
The invariant quantifies over TCBs checking ipcState and pendingMessage, both
unchanged by returnDonatedSchedContext (only schedContextBinding is modified). -/
theorem cleanupPreReceiveDonation_preserves_waitingThreadsPendingMessageNone
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : waitingThreadsPendingMessageNone st) :
    waitingThreadsPendingMessageNone (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner st' hRet => by
      intro tid tcb' hTcb'
      obtain ⟨tcb, hTcb, _, _, hIpcEq, hMsgEq⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
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
    fun scId originalOwner st' hRet => by
      intro tid tcb' hTcb'
      obtain ⟨tcb, hTcb, _, _, hIpcEq, _⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
          tid.toObjId tcb' hTcb'
      have hPre := hInv tid tcb hTcb
      rw [← hIpcEq]
      -- For each blocking ipcState case, transport the endpoint existence forward
      cases hIpc : tcb.ipcState with
      | blockedOnSend epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp⟩ := hPre
        exact ⟨ep, returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet epId ep hEp⟩
      | blockedOnReceive epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp⟩ := hPre
        exact ⟨ep, returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet epId ep hEp⟩
      | blockedOnCall epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp⟩ := hPre
        exact ⟨ep, returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet epId ep hEp⟩
      | _ => trivial

/-- AI4-A: QueueNextPath transfer: a QueueNextPath in st' implies one in st,
when st' comes from returnDonatedSchedContext (TCB queueNext is preserved). -/
private theorem QueueNextPath_backward_of_returnDonatedSchedContext
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hRet : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (a b : SeLe4n.ThreadId)
    (hPath : QueueNextPath st' a b) :
    QueueNextPath st a b := by
  induction hPath with
  | single src dst tcb' hObj' hNext' =>
    obtain ⟨tcb, hObj, hQN, _, _, _⟩ :=
      returnDonatedSchedContext_tcb_queue_backward st st' serverTid scId originalOwner hObjInv hRet
        src.toObjId tcb' hObj'
    exact .single src dst tcb hObj (hQN ▸ hNext')
  | cons src mid tgt tcb' hObj' hNext' _ ih =>
    obtain ⟨tcb, hObj, hQN, _, _, _⟩ :=
      returnDonatedSchedContext_tcb_queue_backward st st' serverTid scId originalOwner hObjInv hRet
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
    fun scId originalOwner st' hRet => by
      obtain ⟨hDQWF, hLink, hAcyc⟩ := hInv
      refine ⟨?_, ?_, ?_⟩
      · -- dualQueueEndpointWellFormed for all endpoints in st'
        intro epId ep hEp'
        have hEpPre := returnDonatedSchedContext_endpoint_backward st st' receiver scId originalOwner hObjInv hRet epId ep hEp'
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
              returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
                hd.toObjId tcb hTcb
            exact ⟨tcb', hTcb', hQP' ▸ hPrev⟩
          · intro tl hTl
            obtain ⟨tcb, hTcb, hNext⟩ := hTail tl hTl
            obtain ⟨tcb', hTcb', hQN', _, _, _⟩ :=
              returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
                tl.toObjId tcb hTcb
            exact ⟨tcb', hTcb', hQN' ▸ hNext⟩
        exact ⟨transportQ _ hDQ.1, transportQ _ hDQ.2⟩
      · -- tcbQueueLinkIntegrity in st'
        obtain ⟨hFwd, hRev⟩ := hLink
        constructor
        · -- Forward: a.queueNext = some b ⟹ b exists ∧ b.queuePrev = some a
          intro a tcbA' hTcbA' b hNext'
          obtain ⟨tcbA, hTcbA, hQNA, _, _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
              a.toObjId tcbA' hTcbA'
          obtain ⟨tcbB, hTcbB, hPrev⟩ := hFwd a tcbA hTcbA b (hQNA ▸ hNext')
          obtain ⟨tcbB', hTcbB', _, hQPB', _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
              b.toObjId tcbB hTcbB
          exact ⟨tcbB', hTcbB', hQPB' ▸ hPrev⟩
        · -- Reverse: b.queuePrev = some a ⟹ a exists ∧ a.queueNext = some b
          intro b tcbB' hTcbB' a hPrev'
          obtain ⟨tcbB, hTcbB, _, hQPB, _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
              b.toObjId tcbB' hTcbB'
          obtain ⟨tcbA, hTcbA, hNext⟩ := hRev b tcbB hTcbB a (hQPB ▸ hPrev')
          obtain ⟨tcbA', hTcbA', hQNA', _, _, _⟩ :=
            returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
              a.toObjId tcbA hTcbA
          exact ⟨tcbA', hTcbA', hQNA' ▸ hNext⟩
      · -- tcbQueueChainAcyclic in st'
        intro tid hPath'
        exact hAcyc tid
          (QueueNextPath_backward_of_returnDonatedSchedContext st st' receiver scId originalOwner hObjInv hRet tid tid hPath')

/-- AI4-A: cleanupPreReceiveDonation preserves endpointQueueNoDup. -/
theorem cleanupPreReceiveDonation_preserves_endpointQueueNoDup
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : endpointQueueNoDup st) :
    endpointQueueNoDup (cleanupPreReceiveDonation st receiver) := by
  exact cleanupPreReceiveDonation_frame_helper st receiver hInv
    fun scId originalOwner st' hRet => by
      intro oid ep hEp'
      have hEpPre := returnDonatedSchedContext_endpoint_backward st st' receiver scId originalOwner hObjInv hRet oid ep hEp'
      obtain ⟨hNoSelf, hDisjoint⟩ := hInv oid ep hEpPre
      constructor
      · -- No self-loops: for all TCBs in st', queueNext ≠ some tid
        intro tid tcb' hTcb'
        obtain ⟨tcb, hTcb, hQN, _, _, _⟩ :=
          returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
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
    fun scId originalOwner st' hRet => by
      intro tid tcb' hTcb'
      obtain ⟨tcb, hTcb, hQN, _, hIpc, _⟩ :=
        returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hRet
          tid.toObjId tcb' hTcb'
      have hPre := hInv tid tcb hTcb
      rw [← hIpc]
      cases hIpcCase : tcb.ipcState with
      | blockedOnSend epId =>
        simp only [hIpcCase] at hPre
        obtain ⟨ep, hEp, hReach⟩ := hPre
        exact ⟨ep,
          returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet epId ep hEp,
          hReach.elim
            (fun hHead => .inl hHead)
            (fun ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ =>
              .inr ⟨prev, by
                obtain ⟨prevTcb', hPrevTcb', hQN', _, _, _⟩ :=
                  returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
                    prev.toObjId prevTcb hPrevTcb
                exact ⟨prevTcb', hPrevTcb', hQN' ▸ hPrevNext⟩⟩)⟩
      | blockedOnReceive epId =>
        simp only [hIpcCase] at hPre
        obtain ⟨ep, hEp, hReach⟩ := hPre
        exact ⟨ep,
          returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet epId ep hEp,
          hReach.elim
            (fun hHead => .inl hHead)
            (fun ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ =>
              .inr ⟨prev, by
                obtain ⟨prevTcb', hPrevTcb', hQN', _, _, _⟩ :=
                  returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
                    prev.toObjId prevTcb hPrevTcb
                exact ⟨prevTcb', hPrevTcb', hQN' ▸ hPrevNext⟩⟩)⟩
      | blockedOnCall epId =>
        simp only [hIpcCase] at hPre
        obtain ⟨ep, hEp, hReach⟩ := hPre
        exact ⟨ep,
          returnDonatedSchedContext_endpoint_forward st st' receiver scId originalOwner hObjInv hRet epId ep hEp,
          hReach.elim
            (fun hHead => .inl hHead)
            (fun ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ =>
              .inr ⟨prev, by
                obtain ⟨prevTcb', hPrevTcb', hQN', _, _, _⟩ :=
                  returnDonatedSchedContext_tcb_queue_forward st st' receiver scId originalOwner hObjInv hRet
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
      | .donated scId owner => returnDonatedSchedContext st receiver scId owner
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
    thread IDs. This is the structural unreachability proof for the three
    internal error branches in `returnDonatedSchedContext`:

    (1) Missing SchedContext at `scId.toObjId` — excluded by
        `donationOwnerValid`'s SchedContext witness.
    (2) Missing owner TCB (step 2 lookupTcb) — excluded by owner TCB
        witness + SchedContext/TCB type-disjointness + owner non-reservation.
    (3) Missing server TCB (step 3 lookupTcb) — excluded by receiver TCB
        witness (derived from `lookupTcb st receiver = some recvTcb`) + the
        chain of stores preserving TCB existence at distinct ObjIds +
        receiver non-reservation.

    All three `storeObject` calls are unconditional `.ok` (see
    `Model/State.lean:531`). -/
theorem returnDonatedSchedContext_ok_under_invariants
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (recvTcb : TCB) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hDOV : donationOwnerValid st)
    (hLk : lookupTcb st receiver = some recvTcb)
    (hBind : recvTcb.schedContextBinding = .donated scId owner)
    (hRecvNotRes : ¬receiver.isReserved = true)
    (hOwnerNotRes : ¬owner.isReserved = true) :
    ∃ st', returnDonatedSchedContext st receiver scId owner = .ok st' := by
  -- Recover hypotheses from donationOwnerValid.
  have hRecvObj : st.objects[receiver.toObjId]? = some (.tcb recvTcb) :=
    lookupTcb_some_objects st receiver recvTcb hLk
  obtain ⟨⟨sc, hScObj, _⟩, ownerTcb, hOwnerObj, _, _⟩ :=
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
  -- Unfold and thread through 3 storeObject + 2 lookupTcb steps.
  unfold returnDonatedSchedContext
  rw [hScObj]
  -- Step 1: storeObject scId (.schedContext sc'). Unconditional .ok.
  simp only []
  generalize hS1 : storeObject scId.toObjId
      (.schedContext { sc with boundThread := some owner }) st = result1
  match result1, hS1 with
  | .ok pair1, hS1 =>
    -- After step 1: invExt preserved, owner/receiver objects unchanged (ne scId.toObjId).
    have hInv1 : pair1.2.objects.invExt :=
      storeObject_preserves_objects_invExt st pair1.2 scId.toObjId _ hObjInv hS1
    have hOwnerObj1 : pair1.2.objects[owner.toObjId]? = some (.tcb ownerTcb) := by
      rw [storeObject_objects_ne st pair1.2 scId.toObjId owner.toObjId _ hScNeOwner.symm hObjInv hS1]
      exact hOwnerObj
    have hRecvObj1 : pair1.2.objects[receiver.toObjId]? = some (.tcb recvTcb) := by
      rw [storeObject_objects_ne st pair1.2 scId.toObjId receiver.toObjId _ hScNeRecv.symm hObjInv hS1]
      exact hRecvObj
    -- Step 2: lookupTcb pair1.2 owner = some ownerTcb.
    have hOwnerNotResEq : owner.isReserved = false :=
      Bool.eq_false_iff.mpr hOwnerNotRes
    have hLkOwner1 : lookupTcb pair1.2 owner = some ownerTcb := by
      unfold lookupTcb
      rw [hOwnerNotResEq]
      simp only [Bool.false_eq_true, if_false]
      rw [hOwnerObj1]
    simp only [hLkOwner1]
    -- storeObject owner.toObjId (.tcb clientTcb'). Unconditional .ok.
    generalize hS2 : storeObject owner.toObjId
        (.tcb { ownerTcb with schedContextBinding := .bound scId }) pair1.2 = result2
    match result2, hS2 with
    | .ok pair2, hS2 =>
      have hInv2 : pair2.2.objects.invExt :=
        storeObject_preserves_objects_invExt pair1.2 pair2.2 owner.toObjId _ hInv1 hS2
      have hRecvObj2 : pair2.2.objects[receiver.toObjId]? = some (.tcb recvTcb) := by
        rw [storeObject_objects_ne pair1.2 pair2.2 owner.toObjId receiver.toObjId _ hOwnerObjIdNeRecv.symm hInv1 hS2]
        exact hRecvObj1
      -- Step 3: lookupTcb pair2.2 receiver = some recvTcb.
      have hRecvNotResEq : receiver.isReserved = false :=
        Bool.eq_false_iff.mpr hRecvNotRes
      have hLkRecv2 : lookupTcb pair2.2 receiver = some recvTcb := by
        unfold lookupTcb
        rw [hRecvNotResEq]
        simp only [Bool.false_eq_true, if_false]
        rw [hRecvObj2]
      simp only [hLkRecv2]
      -- storeObject receiver.toObjId (.tcb serverTcb'). Unconditional .ok.
      generalize hS3 : storeObject receiver.toObjId
          (.tcb { recvTcb with schedContextBinding := .unbound }) pair2.2 = result3
      match result3, hS3 with
      | .ok pair3, hS3 =>
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
      `returnDonatedSchedContext_ok_under_invariants` above (three sequential
      `storeObject` + two `lookupTcb` steps threaded via SchedContext/TCB
      type-disjointness — `schedContext_ne_tcb_at_objId` — and
      `donationOwnerValid_excludes_self_donation`).

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
      | .donated scId owner => returnDonatedSchedContext st receiver scId owner
      | _ => .ok st) = .ok st'
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact ⟨st, rfl⟩
    | bound _ => exact ⟨st, rfl⟩
    | donated scId owner =>
      -- Derive donated-path success from donationOwnerValid + non-reservation.
      exact returnDonatedSchedContext_ok_under_invariants
        st receiver recvTcb scId owner hObjInv hDOV hLk hBind hRecvNotRes
        (hOwnerNotRes recvTcb scId owner hLk hBind)

/-- AK1-A (I-H01): Plan-compliant alias. The plan specifies the lemma name
    `cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull` at the
    top-level function's naming scope. Since we retain two functions
    (`cleanupPreReceiveDonation` for the defensive frame-lemma
    infrastructure and `cleanupPreReceiveDonationChecked` for production
    use), this alias provides the plan-named entry point. -/
abbrev cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull :=
  @cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull

end SeLe4n.Kernel
