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
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[id]? = some obj := by
  unfold storeObject at hStore; cases hStore; simp

theorem storeObject_objects_ne
    (st st' : SystemState) (id oid : SeLe4n.ObjId) (obj : KernelObject)
    (hNe : oid ≠ id) (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeObject at hStore; cases hStore
  rw [HashMap_getElem?_insert]
  have : ¬((id == oid) = true) := by intro heq; exact hNe (eq_of_beq heq).symm
  simp [this]

theorem storeObject_scheduler_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore; cases hStore; rfl

theorem tcb_lookup_of_endpoint_store
    (st st' : SystemState) (endpointId tid : SeLe4n.ObjId) (tcb : TCB) (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hObj : st'.objects[tid]? = some (.tcb tcb)) :
    st.objects[tid]? = some (.tcb tcb) := by
  by_cases hEq : tid = endpointId
  · rw [hEq, storeObject_objects_eq st st' endpointId (.endpoint ep') hStore] at hObj; cases hObj
  · rw [storeObject_objects_ne st st' endpointId tid (.endpoint ep') hEq hStore] at hObj; exact hObj

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
ensures every TCB's queueNext/queuePrev links are consistent. -/
def dualQueueSystemInvariant (st : SystemState) : Prop :=
  (∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[epId]? = some (.endpoint ep) →
    dualQueueEndpointWellFormed epId st) ∧
  tcbQueueLinkIntegrity st

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

/-- Full IPC invariant including system-level dual-queue structural
well-formedness, TCB link integrity, message payload bounds, and badge
well-formedness.
WS-H12c: Dual-queue well-formedness is enforced at the system level via
`dualQueueSystemInvariant` (per-endpoint `dualQueueEndpointWellFormed` +
system-wide `tcbQueueLinkIntegrity`).
WS-H12d: `allPendingMessagesBounded` ensures every pending message stored in
a TCB satisfies `maxMessageRegisters`/`maxExtraCaps` bounds.
WS-F5/D1d: `badgeWellFormed` ensures all badges in notifications and
capabilities are word-bounded. -/
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st

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
    (hStore : storeObject endpointId obj st = .ok ((), st1)) :
    st1.objects[tid.toObjId]? = some (.tcb tcb) := by
  have hNe : tid.toObjId ≠ endpointId := by
    rcases hEndpoint with ⟨ep, hObj⟩; intro h; rw [h] at hTcbExists; simp_all
  rwa [storeObject_objects_ne st st1 endpointId tid.toObjId obj hNe hStore]

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
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    uniqueWaiters st' := by
  intro oid ntfn hObj
  by_cases hEq : oid = notificationId
  · rw [hEq] at hObj
    cases hBadge : badge with
    | some b =>
      rcases notificationWait_badge_path_notification st st' notificationId waiter b
        (by rw [← hBadge]; exact hStep) with ⟨ntfn', hObj', hEmpty⟩
      rw [hObj] at hObj'; cases hObj'
      rw [hEmpty]; exact .nil
    | none =>
      rcases notificationWait_wait_path_notification st st' notificationId waiter
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
      | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hLookup] at hStep
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
              have hPre : st.objects[oid]? = some (.notification ntfn) := by
                have h2 := storeTcbIpcState_notification_backward pair.2 st2 waiter _ oid ntfn hTcb hObj
                by_cases hEq2 : oid = notificationId
                · exact absurd hEq2 hEq
                · rwa [storeObject_objects_ne st pair.2 notificationId oid _ hEq hStore] at h2
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
                have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hLookup hStore
                simp only [storeTcbIpcState_fromTcb_eq hLk']
                cases hTcb : storeTcbIpcState pair.2 waiter _ with
                | error e => simp
                | ok st2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩
                  have hPre : st.objects[oid]? = some (.notification ntfn) := by
                    have hRemObj : (removeRunnable st2 waiter).objects = st2.objects := rfl
                    rw [← hStEq, hRemObj] at hObj
                    have h2 := storeTcbIpcState_notification_backward pair.2 st2 waiter _ oid ntfn hTcb hObj
                    by_cases hEq2 : oid = notificationId
                    · exact absurd hEq2 hEq
                    · rwa [storeObject_objects_ne st pair.2 notificationId oid _ hEq hStore] at h2
                  exact hInv oid ntfn hPre

-- ============================================================================
-- WS-G7: notificationWaiterConsistent — base case + documentation
-- ============================================================================

/-- WS-G7: The default (empty) state trivially satisfies `notificationWaiterConsistent`
because the object store is empty, so no notification objects exist. -/
theorem default_notificationWaiterConsistent :
    notificationWaiterConsistent (default : SystemState) := by
  intro oid ntfn _ hObj _
  have h : (default : SystemState).objects[oid]? = none := HashMap_getElem?_empty
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

The formal preservation theorems for the full transition surface are deferred
to a future workstream (WS-G7+). The base case (`default_notificationWaiterConsistent`)
and the runtime check (`notificationWaiterConsistentCheck`) provide confidence
that the invariant holds in reachable states.
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

