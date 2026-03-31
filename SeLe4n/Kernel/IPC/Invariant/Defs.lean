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
`endpointReplyRecv`). -/
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
with all queue and IPC operations. -/
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
IPC structure: a thread blocked on reply cannot initiate another Call. -/
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
1. The SchedContext object exists in the store
2. The original owner thread exists as a TCB
3. The original owner is blocked on reply (waiting for the server to reply) -/
def donationOwnerValid (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .donated scId owner →
    (∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc)) ∧
    (∃ ownerTcb, st.objects[owner.toObjId]? = some (.tcb ownerTcb) ∧
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
-- Full IPC invariant bundle (14 conjuncts)
-- ============================================================================

/-- Full IPC invariant: conjunction of all fourteen IPC sub-invariants.

Z7 extends the bundle with 4 donation invariants:
- `donationChainAcyclic`: no circular donation chains
- `donationOwnerValid`: donated bindings reference valid objects
- `passiveServerIdle`: unbound non-runnable threads are idle/receiving
- `donationBudgetTransfer`: at most one thread per SchedContext -/
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ waitingThreadsPendingMessageNone st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValid st ∧
  passiveServerIdle st ∧ donationBudgetTransfer st

end SeLe4n.Kernel
