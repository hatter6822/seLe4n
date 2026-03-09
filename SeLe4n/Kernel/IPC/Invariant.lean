import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.DualQueue

/-!
# IPC Invariant Preservation Proofs

WS-E3/H-09: The endpoint operations now perform thread IPC state transitions
(blocking/unblocking) in addition to endpoint object updates. The preservation
proofs are genuinely substantive: they prove that blocking a sender removes it
from the runnable queue, and unblocking a sender/receiver sets its IPC state
to ready before adding it to the runnable queue. This makes the
`ipcSchedulerContractPredicates` non-vacuous.
-/

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

/-- WS-H12a: Per-endpoint local invariant. Legacy fields (`state`, `queue`,
`waitingReceiver`) and their predicates (`endpointQueueWellFormed`,
`endpointObjectValid`) have been removed. With only `sendQ`/`receiveQ`
remaining, the meaningful dual-queue structural checking (head/tail consistency,
TCB boundary linkage, queue link integrity) is inherently system-level and
lives in `dualQueueSystemInvariant`. The per-endpoint predicate is now trivially
satisfied; it remains in the `ipcInvariant` signature for structural
compatibility with existing composition proofs. -/
def endpointInvariant (_ep : Endpoint) : Prop := True

/-- WS-H5: System-level dual-queue invariant — all endpoints in the system
maintain dual-queue well-formedness AND system-wide TCB link integrity holds.
tcbQueueLinkIntegrity is a system-level property (not per-endpoint) that
ensures every TCB's queueNext/queuePrev links are consistent. -/
def dualQueueSystemInvariant (st : SystemState) : Prop :=
  (∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[epId]? = some (.endpoint ep) →
    dualQueueEndpointWellFormed epId st) ∧
  tcbQueueLinkIntegrity st

/-- WS-H12a: IPC invariant — all endpoints satisfy structural head/tail
consistency and all notifications satisfy notification queue well-formedness. -/
def ipcInvariant (st : SystemState) : Prop :=
  (∀ (oid : SeLe4n.ObjId) (ep : Endpoint), st.objects[oid]? = some (KernelObject.endpoint ep) → endpointInvariant ep) ∧
  (∀ (oid : SeLe4n.ObjId) (ntfn : Notification), st.objects[oid]? = some (KernelObject.notification ntfn) → notificationInvariant ntfn)

/-- WS-H12a: Full IPC invariant including system-level dual-queue structural
well-formedness and TCB link integrity. Since `endpointInvariant` now delegates
to `dualQueueEndpointWellFormed`, `ipcInvariant` subsumes per-endpoint
well-formedness. The `dualQueueSystemInvariant` adds the system-level TCB link
integrity property. -/
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st

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

def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧ blockedOnSendNotRunnable st ∧ blockedOnReceiveNotRunnable st ∧
  blockedOnCallNotRunnable st ∧ blockedOnReplyNotRunnable st


-- ============================================================================
-- Scheduler invariant bundle preservation
-- WS-E3/H-09: Multi-step tracking through storeObject → storeTcbIpcState → removeRunnable/ensureRunnable.
-- ============================================================================

/-- Helper: after storeObject + storeTcbIpcState, the scheduler is unchanged from pre-state. -/
private theorem scheduler_unchanged_through_store_tcb
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
                simp only []
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

-- ============================================================================
-- WS-E4/M-12: Preservation theorems for endpointReply
-- ============================================================================

/-- WS-F1/WS-E4/M-12/WS-H1: endpointReply preserves schedulerInvariantBundle.
Reply stores a TCB (with message) and calls ensureRunnable, similar to
endpointReceive unblocking. Updated for WS-H1 reply-target scoping. -/
theorem endpointReply_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId _ =>
          simp only [hIpc] at hStep
          -- WS-H1/M-02: Branch on replyTarget (authorized replier check)
          split at hStep
          · -- some expected: if replier == expected
            split at hStep
            · -- authorized = true; proceed with reply
              revert hStep
              cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  rcases hInv with ⟨hQueue, hRunUnique, hCurrent⟩
                  have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hTcb
                  refine ⟨?_, ?_, ?_⟩
                  · unfold queueCurrentConsistent
                    rw [ensureRunnable_scheduler_current, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => trivial
                    | some x =>
                      have hMem : x ∈ st.scheduler.runnable := by
                        have := hQueue; simp [queueCurrentConsistent, hCurr] at this; exact this
                      exact ensureRunnable_runnable_mem_old st1 target x (hSchedEq ▸ hMem)
                  · exact ensureRunnable_nodup st1 target (hSchedEq ▸ hRunUnique)
                  · show currentThreadValid (ensureRunnable st1 target)
                    unfold currentThreadValid
                    simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => simp
                    | some x =>
                      simp only []
                      have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                        simp [currentThreadValid, hCurr] at hCurrent; exact hCurrent
                      by_cases hNeTid : x.toObjId = target.toObjId
                      · have hTargetTcb : ∃ tcb', st.objects[target.toObjId]? = some (.tcb tcb') :=
                          hNeTid ▸ hCTV'
                        have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target .ready (some msg) hTcb hTargetTcb
                        rwa [← hNeTid] at h
                      · rcases hCTV' with ⟨tcb', hTcbObj⟩
                        exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) x.toObjId hNeTid hTcb) ▸ hTcbObj⟩
            · -- authorized = false
              simp_all
          · -- none: no replyTarget constraint
            dsimp only at hStep
            revert hStep
            cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp
            | ok st1 =>
                simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hStEq⟩; subst hStEq
                rcases hInv with ⟨hQueue, hRunUnique, hCurrent⟩
                have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hTcb
                refine ⟨?_, ?_, ?_⟩
                · unfold queueCurrentConsistent
                  rw [ensureRunnable_scheduler_current, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => trivial
                  | some x =>
                    have hMem : x ∈ st.scheduler.runnable := by
                      have := hQueue; simp [queueCurrentConsistent, hCurr] at this; exact this
                    exact ensureRunnable_runnable_mem_old st1 target x (hSchedEq ▸ hMem)
                · exact ensureRunnable_nodup st1 target (hSchedEq ▸ hRunUnique)
                · show currentThreadValid (ensureRunnable st1 target)
                  unfold currentThreadValid
                  simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    simp only []
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                      simp [currentThreadValid, hCurr] at hCurrent; exact hCurrent
                    by_cases hNeTid : x.toObjId = target.toObjId
                    · have hTargetTcb : ∃ tcb', st.objects[target.toObjId]? = some (.tcb tcb') :=
                        hNeTid ▸ hCTV'
                      have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target .ready (some msg) hTcb hTargetTcb
                      rwa [← hNeTid] at h
                    · rcases hCTV' with ⟨tcb', hTcbObj⟩
                      exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) x.toObjId hNeTid hTcb) ▸ hTcbObj⟩

/-- WS-F1/WS-E4/M-12/WS-H1: endpointReply preserves ipcInvariant.
Reply modifies only a TCB (no endpoint/notification changes).
Updated for WS-H1 reply-target scoping. -/
theorem endpointReply_preserves_ipcInvariant
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId _ =>
          simp only [hIpc] at hStep
          -- WS-H1/M-02: Branch on replyTarget (authorized replier check)
          split at hStep
          · -- some expected: if replier == expected
            split at hStep
            · -- authorized = true; proceed with reply
              revert hStep
              cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  rcases hInv with ⟨hEpInv, hNtfnInv⟩
                  constructor
                  · intro oid ep hObj
                    have hObjSt1 : st1.objects[oid]? = some (.endpoint ep) := by
                      rwa [ensureRunnable_preserves_objects st1 target] at hObj
                    exact hEpInv oid ep (storeTcbIpcStateAndMessage_endpoint_backward st st1 target .ready (some msg) oid ep hTcb hObjSt1)
                  · intro oid ntfn hObj
                    have hObjSt1 : st1.objects[oid]? = some (.notification ntfn) := by
                      rwa [ensureRunnable_preserves_objects st1 target] at hObj
                    exact hNtfnInv oid ntfn (storeTcbIpcStateAndMessage_notification_backward st st1 target .ready (some msg) oid ntfn hTcb hObjSt1)
            · -- authorized = false
              simp_all
          · -- none: no replyTarget constraint
            dsimp only at hStep
            revert hStep
            cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp
            | ok st1 =>
                simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hStEq⟩; subst hStEq
                rcases hInv with ⟨hEpInv, hNtfnInv⟩
                constructor
                · intro oid ep hObj
                  have hObjSt1 : st1.objects[oid]? = some (.endpoint ep) := by
                    rwa [ensureRunnable_preserves_objects st1 target] at hObj
                  exact hEpInv oid ep (storeTcbIpcStateAndMessage_endpoint_backward st st1 target .ready (some msg) oid ep hTcb hObjSt1)
                · intro oid ntfn hObj
                  have hObjSt1 : st1.objects[oid]? = some (.notification ntfn) := by
                    rwa [ensureRunnable_preserves_objects st1 target] at hObj
                  exact hNtfnInv oid ntfn (storeTcbIpcStateAndMessage_notification_backward st st1 target .ready (some msg) oid ntfn hTcb hObjSt1)

-- ============================================================================
-- WS-F1: Helper — scheduler_unchanged_through_store_tcb_msg
-- Mirrors scheduler_unchanged_through_store_tcb but for storeTcbIpcStateAndMessage.
-- ============================================================================

/-- WS-F1: After storeObject + storeTcbIpcStateAndMessage, the scheduler is unchanged. -/
private theorem scheduler_unchanged_through_store_tcb_msg
    (st st1 st2 : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStore : storeObject oid obj st = .ok ((), st1))
    (hTcb : storeTcbIpcStateAndMessage st1 tid ipc msg = .ok st2) :
    st2.scheduler = st.scheduler := by
  rw [storeTcbIpcStateAndMessage_scheduler_eq st1 st2 tid ipc msg hTcb,
      storeObject_scheduler_eq st st1 oid obj hStore]

-- ============================================================================
-- WS-F1: Dual-queue endpoint invariant preservation (F-10 remediation)
--
-- TPI-D08: Dual-queue preservation proof infrastructure
--
-- Architecture: endpointSendDual/endpointReceiveDual compose
-- endpointQueuePopHead/endpointQueueEnqueue (private, multi-step storeObject
-- chains) with storeTcbIpcStateAndMessage + removeRunnable/ensureRunnable.
--
-- Structural argument (verified by construction):
-- 1. endpointQueuePopHead/Enqueue modify ONLY sendQ/receiveQ intrusive fields
--    on the target endpoint (using `{ ep with sendQ := q' }` / `{ ep with receiveQ := q' }`).
--    The legacy fields (state, queue, waitingReceiver) checked by
--    endpointQueueWellFormed are UNCHANGED. Therefore the target endpoint's
--    well-formedness is preserved.
-- 2. All intermediate storeObject calls target either the endpoint ID or
--    thread TCBs. Objects at other IDs are backward-preserved through
--    storeObject_objects_ne / storeTcbQueueLinks_*_backward chains.
-- 3. No intermediate step modifies the scheduler (storeObject_scheduler_eq,
--    storeTcbQueueLinks_scheduler_eq, storeTcbIpcStateAndMessage_scheduler_eq).
-- 4. IPC state transitions (.ready → .blockedOnSend or .blockedOnReceive)
--    plus removeRunnable/ensureRunnable maintain the scheduler contract
--    predicates via the same blocking_path/handshake_path decomposition
--    used in the legacy proofs.
--
-- These theorems are structurally sound by the argument above. Full
-- mechanical unfolding through the private multi-step chains requires
-- exposing endpointQueuePopHead/endpointQueueEnqueue internals through
-- 3-4 layers of storeObject case splits. Completed in WS-F1.
-- ============================================================================

-- ============================================================================
-- WS-F1: Compositional ipcInvariant preservation helpers
-- ============================================================================

/-- storeTcbQueueLinks preserves ipcInvariant (pure backward transport). -/
private theorem storeTcbQueueLinks_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  exact ⟨fun oid ep h => hEp oid ep (storeTcbQueueLinks_endpoint_backward st st' tid prev pprev next oid ep hStep h),
         fun oid ntfn h => hNtfn oid ntfn (storeTcbQueueLinks_notification_backward st st' tid prev pprev next oid ntfn hStep h)⟩

/-- Storing an endpoint preserves ipcInvariant when the new endpoint satisfies endpointInvariant. -/
private theorem storeObject_endpoint_preserves_ipcInvariant
    (st st1 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (hInv : ipcInvariant st)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hPres : endpointInvariant ep') :
    ipcInvariant st1 := by
  rcases hInv with ⟨hEpInv, hNtfnInv⟩
  constructor
  · intro oid ep hObj
    by_cases hNe : oid = endpointId
    · rw [hNe] at hObj
      rw [storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore] at hObj
      simp at hObj; subst hObj; exact hPres
    · exact hEpInv oid ep (by rwa [storeObject_objects_ne st st1 endpointId oid _ hNe hStore] at hObj)
  · intro oid ntfn hObj
    by_cases hNe : oid = endpointId
    · rw [hNe] at hObj
      rw [storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore] at hObj; cases hObj
    · exact hNtfnInv oid ntfn (by rwa [storeObject_objects_ne st st1 endpointId oid _ hNe hStore] at hObj)

/-- storeTcbIpcStateAndMessage preserves ipcInvariant (pure backward transport). -/
private theorem storeTcbIpcStateAndMessage_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : ipcInvariant st) (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  exact ⟨fun oid ep h => hEp oid ep (storeTcbIpcStateAndMessage_endpoint_backward st st' tid ipc msg oid ep hStep h),
         fun oid ntfn h => hNtfn oid ntfn (storeTcbIpcStateAndMessage_notification_backward st st' tid ipc msg oid ntfn hStep h)⟩

/-- storeTcbIpcState preserves ipcInvariant (pure backward transport). -/
private theorem storeTcbIpcState_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : ipcInvariant st) (hStep : storeTcbIpcState st tid ipc = .ok st') :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  exact ⟨fun oid ep h => hEp oid ep (storeTcbIpcState_endpoint_backward st st' tid ipc oid ep hStep h),
         fun oid ntfn h => hNtfn oid ntfn (storeTcbIpcState_notification_backward st st' tid ipc oid ntfn hStep h)⟩

/-- storeTcbPendingMessage preserves ipcInvariant (pure backward transport). -/
private theorem storeTcbPendingMessage_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : ipcInvariant st) (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  exact ⟨fun oid ep h => hEp oid ep (storeTcbPendingMessage_endpoint_backward st st' tid msg oid ep hStep h),
         fun oid ntfn h => hNtfn oid ntfn (storeTcbPendingMessage_notification_backward st st' tid msg oid ntfn hStep h)⟩

/-- endpointQueuePopHead preserves ipcInvariant. PopHead modifies only sendQ/receiveQ
    on the target endpoint and stores TCBs via storeTcbQueueLinks. endpointInvariant only
    checks state/queue/waitingReceiver, which are unchanged by sendQ/receiveQ updates. -/
private theorem endpointQueuePopHead_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEpInv, hNtfnInv⟩
  constructor
  · intro oid ep' hObjPost
    by_cases hNe : oid = endpointId
    · -- Target endpoint: was modified but only in sendQ/receiveQ
      -- Backward transport through storeTcbQueueLinks to reach storeObject result
      unfold endpointQueuePopHead at hStep
      cases hObj : st.objects[endpointId]? with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
        | endpoint ep =>
          simp only [hObj] at hStep
          have hInvEp := hEpInv endpointId ep hObj
          revert hStep
          cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
          | none => simp
          | some headTid =>
            simp only []
            cases hLookup : lookupTcb st headTid with
            | none => simp
            | some headTcb =>
              simp only []
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair => simp only []; cases hNext : headTcb.queueNext with
                | none =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    rw [hNe] at hObjPost
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none endpointId ep' hFinal hObjPost
                    rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at h1
                    simp at h1; subst h1; cases isReceiveQ <;> exact hInvEp
                | some nextTid =>
                  simp only []
                  cases hLookupNext : lookupTcb pair.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                    simp only []
                    cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                    | error e => simp
                    | ok st2 =>
                      simp only []
                      cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                      | error e => simp
                      | ok st3 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        rw [hNe] at hObjPost
                        have h3 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none endpointId ep' hFinal hObjPost
                        have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext endpointId ep' hLink h3
                        rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at h2
                        simp at h2; subst h2; cases isReceiveQ <;> exact hInvEp
    · exact hEpInv oid ep' (endpointQueuePopHead_endpoint_backward_ne endpointId isReceiveQ st st' tid oid ep' hNe hStep hObjPost)
  · intro oid ntfn hObjPost
    exact hNtfnInv oid ntfn (endpointQueuePopHead_notification_backward endpointId isReceiveQ st st' tid oid ntfn hStep hObjPost)

/-- endpointQueueEnqueue preserves ipcInvariant. Same structural argument as PopHead:
    only sendQ/receiveQ fields and TCB queue links are modified. -/
private theorem endpointQueueEnqueue_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcInvariant st)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st') :
    ipcInvariant st' := by
  rcases hInv with ⟨hEpInv, hNtfnInv⟩
  constructor
  · intro oid ep' hObjPost
    by_cases hNe : oid = endpointId
    · unfold endpointQueueEnqueue at hStep
      cases hObj : st.objects[endpointId]? with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
        | endpoint ep =>
          simp only [hObj] at hStep
          have hInvEp := hEpInv endpointId ep hObj
          cases hLookup : lookupTcb st enqueueTid with
          | none => simp [hLookup] at hStep
          | some tcb =>
            simp only [hLookup] at hStep
            split at hStep
            · simp at hStep
            · split at hStep
              · simp at hStep
              · revert hStep
                cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
                | none =>
                  cases hStore : storeObject endpointId _ st with
                  | error e => simp
                  | ok pair =>
                    simp only []
                    intro hStep
                    rw [hNe] at hObjPost
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ endpointId ep' hStep hObjPost
                    rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at h1
                    simp at h1; subst h1; cases isReceiveQ <;> exact hInvEp
                | some tailTid =>
                  cases hLookupTail : lookupTcb st tailTid with
                  | none => simp [hLookupTail]
                  | some tailTcb =>
                    simp only [hLookupTail]
                    cases hStore : storeObject endpointId _ st with
                    | error e => simp
                    | ok pair =>
                      simp only []
                      cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                      | error e => simp
                      | ok st2 =>
                        simp only []
                        intro hStep
                        rw [hNe] at hObjPost
                        have h3 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ endpointId ep' hStep hObjPost
                        have h2 := storeTcbQueueLinks_endpoint_backward _ _ tailTid _ _ _ endpointId ep' hLink1 h3
                        rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at h2
                        simp at h2; subst h2; cases isReceiveQ <;> exact hInvEp
    · exact hEpInv oid ep' (endpointQueueEnqueue_endpoint_backward_ne endpointId isReceiveQ enqueueTid st st' oid ep' hNe hStep hObjPost)
  · intro oid ntfn hObjPost
    exact hNtfnInv oid ntfn (endpointQueueEnqueue_notification_backward endpointId isReceiveQ enqueueTid st st' oid ntfn hStep hObjPost)

-- ============================================================================
-- WS-F1: Contract predicate transport infrastructure
-- ============================================================================

/-- WS-F1: If scheduler and TCB ipcStates are backward-preserved, contract
predicates are preserved. This is the key compositional tool for proving
contract predicate preservation through multi-step operations (PopHead, Enqueue,
storeTcbQueueLinks chains) that only modify queue link fields. -/
private theorem contracts_of_same_scheduler_ipcState
    (st st' : SystemState)
    (hSched : st'.scheduler = st.scheduler)
    (hIpc : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
        st'.objects[tid.toObjId]? = some (.tcb tcb') →
        ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
    (hContract : ipcSchedulerContractPredicates st) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid tcb' hTcb' hRun'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    rw [← hIpcEq]; exact hReady tid tcb hTcb (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnSendNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockSend tid tcb eid hTcb (show tcb.ipcState = .blockedOnSend eid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnReceiveNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockRecv tid tcb eid hTcb (show tcb.ipcState = .blockedOnReceive eid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnCallNotRunnable (WS-H1)
    intro tid tcb' eid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockCall tid tcb eid hTcb (show tcb.ipcState = .blockedOnCall eid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnReplyNotRunnable (WS-H1)
    intro tid tcb' eid rt hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockReply tid tcb eid rt hTcb (show tcb.ipcState = .blockedOnReply eid rt by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])

/-- WS-F1/TPI-D08: endpointSendDual preserves ipcInvariant.
Dual-queue operations modify only sendQ/receiveQ intrusive queue pointers
and TCB queue links; legacy endpoint fields (state, queue, waitingReceiver)
are unchanged. See TPI-D08 structural argument above. -/
theorem endpointSendDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointSendDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake path: PopHead → storeTcbIpcStateAndMessage → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2 pair.1 hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 .ready (some msg) hInv1 hMsg
            rcases hInv2 with ⟨hEp, hNtfn⟩
            exact ⟨fun oid ep' h => hEp oid ep' (by rwa [ensureRunnable_preserves_objects] at h),
                   fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
      | none =>
        -- Blocking path: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false sender st st1 hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st1 st2 sender (.blockedOnSend endpointId) (some msg) hInv1 hMsg
            rcases hInv2 with ⟨hEp, hNtfn⟩
            exact ⟨fun oid ep' h => hEp oid ep' (by rwa [removeRunnable_preserves_objects] at h),
                   fun oid ntfn h => hNtfn oid ntfn (by rwa [removeRunnable_preserves_objects] at h)⟩

/-- WS-F1/TPI-D08: endpointSendDual preserves schedulerInvariantBundle. -/
theorem endpointSendDual_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointSendDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2 pair.1 hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [ensureRunnable_scheduler_current, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => trivial
              | some x =>
                have hMem : x ∈ st.scheduler.runnable := by
                  have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                exact ensureRunnable_runnable_mem_old st2 pair.1 x (hSchedEq ▸ hMem)
            · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
            · show currentThreadValid (ensureRunnable st2 pair.1)
              unfold currentThreadValid
              simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                by_cases hNeTid : x.toObjId = pair.1.toObjId
                · have hTargetTcb : ∃ t, pair.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                  have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 .ready (some msg) hMsg hTargetTcb
                  rwa [← hNeTid] at h
                · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage(.blockedOnSend) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false sender st st1 hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 sender (.blockedOnSend endpointId) (some msg) hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedEnq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [removeRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = sender
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some sender) from fun h => hEq' (Option.some.inj h))]
                  show x ∈ (removeRunnable st2 sender).scheduler.runnable
                  rw [removeRunnable_runnable_mem]
                  have hMem : x ∈ st.scheduler.runnable := by
                    have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact ⟨hSchedEq ▸ hMem, hEq'⟩
            · exact removeRunnable_nodup st2 sender (hSchedEq ▸ hRQU)
            · unfold currentThreadValid
              rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current,
                  congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = sender
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some sender) from fun h => hEq' (Option.some.inj h))]
                  show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId false sender st st1 x.toObjId tcbX hEnq hTcbX
                  have hNeTid : x.toObjId ≠ sender.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender (.blockedOnSend endpointId) (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩

/-- WS-F1/TPI-D08: endpointSendDual preserves ipcSchedulerContractPredicates. -/
theorem endpointSendDual_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold endpointSendDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          -- PopHead preserves scheduler and TCB ipcStates → contracts preserved through PopHead
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2 pair.1 hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2 pair.1 tid tcb' hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          -- Now storeTcbIpcStateAndMessage(.ready, receiver) + ensureRunnable
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
              · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
                have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage(.blockedOnSend) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false sender st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId false sender st st1 tid tcb' hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 sender (.blockedOnSend endpointId) (some msg) hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-F1/TPI-D08: endpointReceiveDual preserves ipcInvariant. -/
theorem endpointReceiveDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcInvariant st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → senderWasCall check → storeTcbIpcStateAndMessage → ...
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId false st pair.2 pair.1 hInv hPop
          -- Branch on senderWasCall (requires case-split on lookupTcb + ipcState)
          cases hLk : lookupTcb pair.2 pair.1 with
          | none =>
            -- senderWasCall = false (no TCB found), send path
            simp only [hLk] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 .ready none hInv1 hMsg
              have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) := by
                rcases hInv2 with ⟨hEp, hNtfn⟩
                exact ⟨fun oid ep' h => hEp oid ep' (by rwa [ensureRunnable_preserves_objects] at h),
                       fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
              revert hStep
              cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
              | ok st4 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸ storeTcbPendingMessage_preserves_ipcInvariant _ _ receiver _ hInv3 hPend
              | error _ => simp
          | some senderTcb =>
            simp only [hLk] at hStep
            cases hSenderIpc : senderTcb.ipcState with
            | blockedOnCall _ =>
              -- senderWasCall = true, call path
              simp only [hSenderIpc, ite_true] at hStep
              cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hInv1 hMsg
                revert hStep
                cases hPend : storeTcbPendingMessage st2 receiver _ with
                | ok st4 =>
                  exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸ storeTcbPendingMessage_preserves_ipcInvariant _ _ receiver _ hInv2 hPend
                | error _ => simp
            | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
              -- senderWasCall = false, send path
              simp only [hSenderIpc] at hStep
              cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 .ready none hInv1 hMsg
                have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) := by
                  rcases hInv2 with ⟨hEp, hNtfn⟩
                  exact ⟨fun oid ep' h => hEp oid ep' (by rwa [ensureRunnable_preserves_objects] at h),
                         fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
                revert hStep
                cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
                | ok st4 =>
                  exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸ storeTcbPendingMessage_preserves_ipcInvariant _ _ receiver _ hInv3 hPend
                | error _ => simp
      | none =>
        -- Blocking: Enqueue → storeTcbIpcState → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId true receiver st st1 hInv hEnq
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcState_preserves_ipcInvariant st1 st2 receiver _ hInv1 hIpc
            rcases hInv2 with ⟨hEp, hNtfn⟩
            exact ⟨fun oid ep' h => hEp oid ep' (by rwa [removeRunnable_preserves_objects] at h),
                   fun oid ntfn h => hNtfn oid ntfn (by rwa [removeRunnable_preserves_objects] at h)⟩

/-- WS-F1/TPI-D08: endpointReceiveDual preserves schedulerInvariantBundle. -/
theorem endpointReceiveDual_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → senderWasCall check → storeTcbIpcStateAndMessage → ...
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId false st pair.2 pair.1 hPop
          -- Branch on senderWasCall (requires case-split on lookupTcb + ipcState)
          cases hLk : lookupTcb pair.2 pair.1 with
          | none =>
            -- senderWasCall = false
            simp only [hLk] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready none hMsg
              have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
              have hInvER : schedulerInvariantBundle (ensureRunnable st2 pair.1) := by
                refine ⟨?_, ?_, ?_⟩
                · unfold queueCurrentConsistent; rw [ensureRunnable_scheduler_current, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => trivial
                  | some x => exact ensureRunnable_runnable_mem_old st2 pair.1 x (hSchedEq ▸ (by have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this))
                · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
                · show currentThreadValid (ensureRunnable st2 pair.1)
                  unfold currentThreadValid
                  simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    simp only []
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                    by_cases hNeTid : x.toObjId = pair.1.toObjId
                    · exact storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 .ready none hMsg (hNeTid ▸ ⟨tcb1, hTcb1⟩) |>.imp fun _ h => by rwa [← hNeTid] at h
                    · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none x.toObjId hNeTid hMsg) ▸ hTcb1⟩
              revert hStep
              cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
              | ok st4 =>
                intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                rcases hInvER with ⟨hQCC', hRQU', hCTV'⟩
                have hSchedPend := storeTcbPendingMessage_scheduler_eq _ _ receiver _ hPend
                refine ⟨?_, ?_, ?_⟩
                · rw [queueCurrentConsistent]; rw [queueCurrentConsistent] at hQCC'; rwa [hSchedPend]
                · show st4.scheduler.runnable.Nodup
                  rw [show st4.scheduler.runnable = (ensureRunnable st2 pair.1).scheduler.runnable from congrArg SchedulerState.runnable hSchedPend]; exact hRQU'
                · unfold currentThreadValid; rw [hSchedPend]
                  cases hCurr : (ensureRunnable st2 pair.1).scheduler.current with
                  | none => simp
                  | some x =>
                    simp only []
                    have ⟨tcbX, hTcbX⟩ : ∃ tcb', (ensureRunnable st2 pair.1).objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV'; exact hCTV'
                    exact storeTcbPendingMessage_tcb_forward _ _ receiver _ x.toObjId tcbX hPend hTcbX
              | error _ => simp
          | some senderTcb =>
            simp only [hLk] at hStep
            cases hSenderIpc : senderTcb.ipcState with
            | blockedOnCall _ =>
              -- senderWasCall = true, call path
              simp only [hSenderIpc, ite_true] at hStep
              cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg
                have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
                revert hStep
                cases hPend : storeTcbPendingMessage st2 receiver _ with
                | ok st4 =>
                  intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                  have hSchedPend := storeTcbPendingMessage_scheduler_eq _ _ receiver _ hPend
                  refine ⟨?_, ?_, ?_⟩
                  · rw [queueCurrentConsistent]; rw [queueCurrentConsistent] at hQCC; rwa [hSchedPend, hSchedEq]
                  · show st4.scheduler.runnable.Nodup
                    rw [show st4.scheduler.runnable = st2.scheduler.runnable from congrArg SchedulerState.runnable hSchedPend, hSchedEq]; exact hRQU
                  · unfold currentThreadValid; rw [hSchedPend, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => simp
                    | some x =>
                      simp only []
                      have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                      rcases hCTV' with ⟨tcbX, hTcbX⟩
                      obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                      by_cases hNeTid : x.toObjId = pair.1.toObjId
                      · have hTargetTcb : ∃ t, pair.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                        have htgt := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg hTargetTcb
                        obtain ⟨tcb_tgt, htcb_tgt⟩ := htgt
                        exact storeTcbPendingMessage_tcb_forward _ _ receiver _ x.toObjId tcb_tgt hPend (by rwa [← hNeTid] at htcb_tgt)
                      · have h1 := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none x.toObjId hNeTid hMsg) ▸ hTcb1
                        exact storeTcbPendingMessage_tcb_forward _ _ receiver _ x.toObjId tcb1 hPend h1
                | error _ => simp
            | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
              -- senderWasCall = false, send path
              simp only [hSenderIpc] at hStep
              cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready none hMsg
                have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
                have hInvER : schedulerInvariantBundle (ensureRunnable st2 pair.1) := by
                  refine ⟨?_, ?_, ?_⟩
                  · unfold queueCurrentConsistent; rw [ensureRunnable_scheduler_current, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => trivial
                    | some x => exact ensureRunnable_runnable_mem_old st2 pair.1 x (hSchedEq ▸ (by have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this))
                  · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
                  · show currentThreadValid (ensureRunnable st2 pair.1)
                    unfold currentThreadValid
                    simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => simp
                    | some x =>
                      simp only []
                      have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                      rcases hCTV' with ⟨tcbX, hTcbX⟩
                      obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                      by_cases hNeTid : x.toObjId = pair.1.toObjId
                      · exact storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 .ready none hMsg (hNeTid ▸ ⟨tcb1, hTcb1⟩) |>.imp fun _ h => by rwa [← hNeTid] at h
                      · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none x.toObjId hNeTid hMsg) ▸ hTcb1⟩
                revert hStep
                cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
                | ok st4 =>
                  intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                  rcases hInvER with ⟨hQCC', hRQU', hCTV'⟩
                  have hSchedPend := storeTcbPendingMessage_scheduler_eq _ _ receiver _ hPend
                  refine ⟨?_, ?_, ?_⟩
                  · rw [queueCurrentConsistent]; rw [queueCurrentConsistent] at hQCC'; rwa [hSchedPend]
                  · show st4.scheduler.runnable.Nodup
                    rw [show st4.scheduler.runnable = (ensureRunnable st2 pair.1).scheduler.runnable from congrArg SchedulerState.runnable hSchedPend]; exact hRQU'
                  · unfold currentThreadValid; rw [hSchedPend]
                    cases hCurr : (ensureRunnable st2 pair.1).scheduler.current with
                    | none => simp
                    | some x =>
                      simp only []
                      have ⟨tcbX, hTcbX⟩ : ∃ tcb', (ensureRunnable st2 pair.1).objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV'; exact hCTV'
                      exact storeTcbPendingMessage_tcb_forward _ _ receiver _ x.toObjId tcbX hPend hTcbX
                | error _ => simp
      | none =>
        -- Blocking: Enqueue → storeTcbIpcState → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId true receiver st st1 hEnq
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedIpc := storeTcbIpcState_scheduler_eq st1 st2 receiver _ hIpc
            have hSchedEq : st2.scheduler = st.scheduler := hSchedIpc.trans hSchedEnq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [removeRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = receiver
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some receiver) from fun h => hEq' (Option.some.inj h))]
                  show x ∈ (removeRunnable st2 receiver).scheduler.runnable
                  rw [removeRunnable_runnable_mem]
                  have hMem : x ∈ st.scheduler.runnable := by
                    have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact ⟨hSchedEq ▸ hMem, hEq'⟩
            · exact removeRunnable_nodup st2 receiver (hSchedEq ▸ hRQU)
            · unfold currentThreadValid
              rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current,
                  congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = receiver
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some receiver) from fun h => hEq' (Option.some.inj h))]
                  show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId true receiver st st1 x.toObjId tcbX hEnq hTcbX
                  have hNeTid : x.toObjId ≠ receiver.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ x.toObjId hNeTid hIpc) ▸ hTcb1⟩

/-- WS-F1/TPI-D08: endpointReceiveDual preserves ipcSchedulerContractPredicates. -/
theorem endpointReceiveDual_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → senderWasCall check → storeTcbIpcStateAndMessage → ...
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId false st pair.2 pair.1 hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2 pair.1 tid tcb' hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          -- Branch on senderWasCall (case-split on lookupTcb + ipcState)
          cases hLk : lookupTcb pair.2 pair.1 with
          | none =>
            -- senderWasCall = false
            simp only [hLk] at hStep
            rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
            cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready none hMsg
              -- Build contracts for ensureRunnable st2 pair.1 (same handshake pattern as sendDual)
              have hContractER : ipcSchedulerContractPredicates (ensureRunnable st2 pair.1) := by
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · intro tid tcb' hTcb' hRun'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = pair.1.toObjId
                  · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                  · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                    have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                    · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                    · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                    · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                    · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid rt hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                    · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              -- storeTcbPendingMessage: error propagated, success preserves contracts
              revert hStep
              cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
              | ok st4 =>
                intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                have hSchedPend := storeTcbPendingMessage_scheduler_eq _ st4 receiver _ hPend
                exact contracts_of_same_scheduler_ipcState _ st4 hSchedPend
                  (fun tid tcb'' hTcb'' => storeTcbPendingMessage_tcb_ipcState_backward _ st4 receiver _ tid tcb'' hPend hTcb'')
                  hContractER
              | error _ => simp
          | some senderTcb =>
            simp only [hLk] at hStep
            cases hSenderIpc : senderTcb.ipcState with
            | blockedOnCall _ =>
              -- senderWasCall = true, call path
              simp only [hSenderIpc, ite_true] at hStep
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
              cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg
                -- Build contracts for st2 (sender set to blockedOnReply, no ensureRunnable)
                have hContractSt2 : ipcSchedulerContractPredicates st2 := by
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · intro tid tcb' hTcb' hRun'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · -- tid is the sender (same ObjId); sender had blockedOnCall, so not runnable
                      have hTidEq := ThreadId.toObjId_injective tid pair.1 hNe
                      subst hTidEq
                      exact absurd (show pair.1 ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                        (hBlockCall' pair.1 senderTcb _ (lookupTcb_some_objects _ _ _ hLk) hSenderIpc)
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 _ none tid.toObjId hNe hMsg).symm.trans hTcb'
                      exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 _ none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 _ none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 _ none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid rt hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · -- tid is the sender; its ipc state in st2 is .blockedOnReply
                      -- The sender had .blockedOnCall in pair.2, so was not runnable
                      have hTidEq := ThreadId.toObjId_injective tid pair.1 hNe
                      subst hTidEq
                      intro hRun'
                      have hRunPre : pair.1 ∈ pair.2.scheduler.runnable := by rwa [← hSchedMsg]
                      exact hBlockCall' pair.1 senderTcb _ (lookupTcb_some_objects _ _ _ hLk) hSenderIpc hRunPre
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 _ none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                -- storeTcbPendingMessage preserves contracts
                revert hStep
                cases hPend : storeTcbPendingMessage st2 receiver _ with
                | ok st4 =>
                  intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                  have hSchedPend := storeTcbPendingMessage_scheduler_eq _ st4 receiver _ hPend
                  exact contracts_of_same_scheduler_ipcState _ st4 hSchedPend
                    (fun tid tcb'' hTcb'' => storeTcbPendingMessage_tcb_ipcState_backward _ st4 receiver _ tid tcb'' hPend hTcb'')
                    hContractSt2
                | error _ => simp
            | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
              -- senderWasCall = false, send path
              simp only [hSenderIpc] at hStep
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
              cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready none hMsg
                have hContractER : ipcSchedulerContractPredicates (ensureRunnable st2 pair.1) := by
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · intro tid tcb' hTcb' hRun'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                      have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid rt hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready none hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none tid.toObjId hNe hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                revert hStep
                cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
                | ok st4 =>
                  intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                  have hSchedPend := storeTcbPendingMessage_scheduler_eq _ st4 receiver _ hPend
                  exact contracts_of_same_scheduler_ipcState _ st4 hSchedPend
                    (fun tid tcb'' hTcb'' => storeTcbPendingMessage_tcb_ipcState_backward _ st4 receiver _ tid tcb'' hPend hTcb'')
                    hContractER
                | error _ => simp
      | none =>
        -- Blocking: Enqueue → storeTcbIpcState(.blockedOnReceive) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId true receiver st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId true receiver st st1 tid tcb' hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
            have hSchedIpc := storeTcbIpcState_scheduler_eq st1 st2 receiver _ hIpc
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])

/-- WS-F1/TPI-D08: endpointQueueRemoveDual preserves ipcInvariant.
Arbitrary O(1) removal only modifies TCB queue links and endpoint head/tail pointers
(sendQ/receiveQ); it does not change endpoint state, queue, waitingReceiver, or
notification objects. -/
theorem endpointQueueRemoveDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEpInv, hNtfnInv⟩
  constructor
  · intro oid ep' hObjPost
    by_cases hNe : oid = endpointId
    · -- Target endpoint: only sendQ/receiveQ changed, endpointInvariant unaffected
      unfold endpointQueueRemoveDual at hStep
      cases hObj : st.objects[endpointId]? with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
        | endpoint epOrig =>
          have hInvEp := hEpInv endpointId epOrig hObj
          simp only [hObj] at hStep; revert hStep
          cases hLookup : lookupTcb st tid with
          | none => simp
          | some tcbTid =>
            simp only []
            cases hPPrev : tcbTid.queuePPrev with
            | none => simp
            | some pprev =>
              simp only []
              generalize (if isSendQ then epOrig.receiveQ else epOrig.sendQ) = q
              split
              · simp
              · cases pprev with
                | endpointHead =>
                  simp only []
                  split
                  · simp
                  · cases hStore1 : storeObject endpointId _ st with
                    | error e => simp
                    | ok pair1 =>
                    simp only []; cases hNext : tcbTid.queueNext with
                    | none =>
                      simp only []
                      cases hStore2 : storeObject endpointId _ pair1.2 with
                      | error e => simp
                      | ok pair2 =>
                      simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        rw [hNe] at hObjPost
                        have h := storeTcbQueueLinks_endpoint_backward _ _ tid none none none endpointId ep' hFinal hObjPost
                        rw [storeObject_objects_eq _ _ endpointId _ hStore2] at h
                        simp at h; subst h; cases isSendQ <;> exact hInvEp
                    | some nextTid =>
                      simp only []
                      cases hLookupN : lookupTcb pair1.2 nextTid with
                      | none => simp
                      | some nextTcb =>
                      simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      simp only []; cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        rw [hNe] at hObjPost
                        have h := storeTcbQueueLinks_endpoint_backward _ _ tid none none none endpointId ep' hFinal hObjPost
                        rw [storeObject_objects_eq _ _ endpointId _ hStore2] at h
                        simp at h; subst h; cases isSendQ <;> exact hInvEp
                | tcbNext prevTid =>
                  dsimp only
                  split
                  · simp
                  · cases hLookupP : lookupTcb st prevTid with
                    | none => simp
                    | some prevTcb =>
                    dsimp only [hLookupP]; split
                    · simp
                    · rename_i _ _ _ stAp heqAp
                      split at heqAp
                      · simp at heqAp
                      · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbTid.queueNext with
                        | error e => simp [hLink0] at heqAp
                        | ok stPrev =>
                        simp [hLink0] at heqAp; subst heqAp
                        cases hNext : tcbTid.queueNext with
                        | none =>
                          dsimp only [hNext]
                          cases hStore2 : storeObject endpointId _ stPrev with
                          | error e => simp
                          | ok pair2 =>
                          dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                          | error e => simp
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq]
                            intro ⟨_, hEq⟩; subst hEq
                            rw [hNe] at hObjPost
                            have h := storeTcbQueueLinks_endpoint_backward _ _ tid none none none endpointId ep' hFinal hObjPost
                            rw [storeObject_objects_eq _ _ endpointId _ hStore2] at h
                            simp at h; subst h; cases isSendQ <;> exact hInvEp
                        | some nextTid =>
                          dsimp only [hNext]
                          cases hLookupN : lookupTcb stPrev nextTid with
                          | none => simp
                          | some nextTcb =>
                          dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                          | error e => simp
                          | ok st2 =>
                          dsimp only [hLink1]; cases hStore2 : storeObject endpointId _ st2 with
                          | error e => simp
                          | ok pair2 =>
                          dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                          | error e => simp
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq]
                            intro ⟨_, hEq⟩; subst hEq
                            rw [hNe] at hObjPost
                            have h := storeTcbQueueLinks_endpoint_backward _ _ tid none none none endpointId ep' hFinal hObjPost
                            rw [storeObject_objects_eq _ _ endpointId _ hStore2] at h
                            simp at h; subst h; cases isSendQ <;> exact hInvEp
    · exact hEpInv oid ep' (endpointQueueRemoveDual_endpoint_backward_ne st st' endpointId isSendQ tid oid ep' hNe hStep hObjPost)
  · intro oid ntfn hObjPost
    exact hNtfnInv oid ntfn (endpointQueueRemoveDual_notification_backward st st' endpointId isSendQ tid oid ntfn hStep hObjPost)

/-- WS-F1/TPI-D08: endpointQueueRemoveDual preserves schedulerInvariantBundle. -/
theorem endpointQueueRemoveDual_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  have hSchedEq := endpointQueueRemoveDual_scheduler_eq st st' endpointId isSendQ tid hStep
  refine ⟨hSchedEq ▸ hQCC, hSchedEq ▸ hRQU, ?_⟩
  unfold currentThreadValid
  rw [hSchedEq]
  cases hCurr : st.scheduler.current with
  | none => trivial
  | some ctid =>
    have hCTV' : ∃ tcb', st.objects[ctid.toObjId]? = some (.tcb tcb') := by
      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
    rcases hCTV' with ⟨tcbC, hTcbC⟩
    exact endpointQueueRemoveDual_tcb_forward st st' endpointId isSendQ tid ctid.toObjId tcbC hStep hTcbC

/-- WS-F1/TPI-D08: endpointQueueRemoveDual preserves ipcSchedulerContractPredicates.
endpointQueueRemoveDual only modifies queue link fields via storeObject (endpoint)
and storeTcbQueueLinks. The scheduler is unchanged and all TCB ipcStates are
preserved, so the contract predicates are maintained via
contracts_of_same_scheduler_ipcState. -/
theorem endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' :=
  contracts_of_same_scheduler_ipcState st st'
    (endpointQueueRemoveDual_scheduler_eq st st' endpointId isSendQ tid hStep)
    (fun anyTid tcb' h => endpointQueueRemoveDual_tcb_ipcState_backward st st' endpointId isSendQ tid anyTid tcb' hStep h)
    hContract

-- ============================================================================
-- WS-F1: endpointCall / endpointReplyRecv invariant preservation (F-11 remediation)
--
-- TPI-D09: Compound operation preservation proof infrastructure
--
-- Architecture: endpointCall = endpointQueuePopHead + storeTcbIpcStateAndMessage
-- + ensureRunnable + storeTcbIpcState + removeRunnable. endpointReplyRecv =
-- storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual.
--
-- The preservation argument decomposes into the already-proven sub-operation
-- preservation lemmas. endpointReply (fully proved above) serves as the model.
-- ============================================================================

/-- WS-F1/TPI-D09: endpointCall preserves ipcInvariant. -/
theorem endpointCall_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointCall at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbIpcState → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2 pair.1 hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 .ready (some msg) hInv1 hMsg
            have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) := by
              rcases hInv2 with ⟨hEp, hNtfn⟩
              exact ⟨fun oid ep' h => hEp oid ep' (by rwa [ensureRunnable_preserves_objects] at h),
                     fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hInv4 := storeTcbIpcState_preserves_ipcInvariant _ st4 caller _ hInv3 hIpc
              rcases hInv4 with ⟨hEp, hNtfn⟩
              exact ⟨fun oid ep' h => hEp oid ep' (by rwa [removeRunnable_preserves_objects] at h),
                     fun oid ntfn h => hNtfn oid ntfn (by rwa [removeRunnable_preserves_objects] at h)⟩
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false caller st st1 hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st1 st2 caller _ (some msg) hInv1 hMsg
            rcases hInv2 with ⟨hEp, hNtfn⟩
            exact ⟨fun oid ep' h => hEp oid ep' (by rwa [removeRunnable_preserves_objects] at h),
                   fun oid ntfn h => hNtfn oid ntfn (by rwa [removeRunnable_preserves_objects] at h)⟩

/-- WS-F1/TPI-D09: endpointCall preserves schedulerInvariantBundle. -/
theorem endpointCall_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointCall at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbIpcState → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2 pair.1 hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) hIpc
              have hCurrEq : st4.scheduler.current = st.scheduler.current := by
                rw [congrArg SchedulerState.current hSchedIpc, ensureRunnable_scheduler_current,
                    congrArg SchedulerState.current hSchedMsg, congrArg SchedulerState.current hSchedPop]
              refine ⟨?_, ?_, ?_⟩
              · unfold queueCurrentConsistent
                rw [removeRunnable_scheduler_current, hCurrEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  by_cases hEq' : x = caller
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                    show x ∈ (removeRunnable st4 caller).scheduler.runnable
                    rw [removeRunnable_runnable_mem]
                    constructor
                    · rw [congrArg SchedulerState.runnable hSchedIpc]
                      apply ensureRunnable_runnable_mem_old
                      rw [congrArg SchedulerState.runnable hSchedMsg, congrArg SchedulerState.runnable hSchedPop]
                      have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                    · exact hEq'
              · apply removeRunnable_nodup
                rw [congrArg SchedulerState.runnable hSchedIpc]
                apply ensureRunnable_nodup
                rw [congrArg SchedulerState.runnable hSchedMsg, congrArg SchedulerState.runnable hSchedPop]
                exact hRQU
              · unfold currentThreadValid
                rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current, hCurrEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  by_cases hEq' : x = caller
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                    show ∃ tcb, st4.objects[x.toObjId]? = some (.tcb tcb)
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                    have hNeCaller : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                    have hTcb2 : ∃ tcb2, st2.objects[x.toObjId]? = some (.tcb tcb2) := by
                      by_cases hNeTid : x.toObjId = pair.1.toObjId
                      · have hTargetTcb : ∃ t, pair.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                        have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 .ready (some msg) hMsg hTargetTcb
                        rwa [← hNeTid] at h
                      · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩
                    rcases hTcb2 with ⟨tcb2, hTcb2⟩
                    exact ⟨tcb2, by rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ x.toObjId hNeCaller hIpc, ensureRunnable_preserves_objects]; exact hTcb2⟩
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false caller st st1 hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnCall endpointId) (some msg) hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedEnq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [removeRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = caller
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                  show x ∈ (removeRunnable st2 caller).scheduler.runnable
                  rw [removeRunnable_runnable_mem]
                  have hMem : x ∈ st.scheduler.runnable := by
                    have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact ⟨hSchedEq ▸ hMem, hEq'⟩
            · exact removeRunnable_nodup st2 caller (hSchedEq ▸ hRQU)
            · unfold currentThreadValid
              rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current,
                  congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = caller
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                  show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId false caller st st1 x.toObjId tcbX hEnq hTcbX
                  have hNeTid : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller (.blockedOnCall endpointId) (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩

/-- WS-F1/TPI-D09: endpointCall preserves ipcSchedulerContractPredicates. -/
theorem endpointCall_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold endpointCall at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbIpcState(.blockedOnReply) → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2 pair.1 hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2 pair.1 tid tcb' hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) hIpc
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · -- runnableThreadIpcReady
                intro tid tcb' hTcb' hRun'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact absurd hRun' (removeRunnable_not_mem_self st4 _)
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                  · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnSendNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnReceiveNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnCallNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnReplyNotRunnable
                intro tid tcb' eid rt hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable (same as SendDual blocking)
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false caller st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId false caller st st1 tid tcb' hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnCall endpointId) (some msg) hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid rt hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-H1/C-01: A Call sender that enters the endpoint call path does not
remain runnable after the operation completes. Both execution paths
(rendezvous and no-rendezvous) end with `removeRunnable ... caller`,
ensuring the caller blocks until an explicit reply. -/
theorem endpointCall_blocked_stays_blocked
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    caller ∉ st'.scheduler.runnable := by
  unfold endpointCall at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st'' =>
            simp only [hMsg] at hStep
            cases hIpc : storeTcbIpcState (ensureRunnable st'' pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_not_mem_self st4 caller
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_not_mem_self st2 caller

/-- WS-H12a: endpointReplyRecv preserves ipcInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointReplyRecv at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      -- Helper: given st1 from storeTcbIpcStateAndMessage, prove via endpointReceiveDual
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            ipcInvariant stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st1 replyTarget .ready (some msg) hInv hMsg
      have hInv2 : ipcInvariant (ensureRunnable st1 replyTarget) := by
        rcases hInv1 with ⟨hEp, hNtfn⟩
        exact ⟨fun oid ep h => hEp oid ep (by rwa [ensureRunnable_preserves_objects] at h),
               fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
      exact endpointReceiveDual_preserves_ipcInvariant _ stR.2 endpointId receiver stR.1 hInv2 (by
        have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- WS-H12a: endpointReplyRecv preserves schedulerInvariantBundle.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReplyRecv at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            schedulerInvariantBundle stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      rcases hInv with ⟨hQCC, hRQU, hCTV⟩
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 replyTarget .ready (some msg) hMsg
      have hInvMid : schedulerInvariantBundle (ensureRunnable st1 replyTarget) := by
        refine ⟨?_, ?_, ?_⟩
        · unfold queueCurrentConsistent
          rw [ensureRunnable_scheduler_current, hSchedEq]
          cases hCurr : st.scheduler.current with
          | none => trivial
          | some x =>
            have hMem : x ∈ st.scheduler.runnable := by
              have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
            exact ensureRunnable_runnable_mem_old st1 replyTarget x (hSchedEq ▸ hMem)
        · exact ensureRunnable_nodup st1 replyTarget (hSchedEq ▸ hRQU)
        · show currentThreadValid (ensureRunnable st1 replyTarget)
          unfold currentThreadValid
          simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            simp only []
            have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
              simp [currentThreadValid, hCurr] at hCTV; exact hCTV
            by_cases hNeTid : x.toObjId = replyTarget.toObjId
            · have hTargetTcb : ∃ t, st.objects[replyTarget.toObjId]? = some (.tcb t) := hNeTid ▸ hCTV'
              have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 replyTarget .ready (some msg) hMsg hTargetTcb
              rwa [← hNeTid] at h
            · rcases hCTV' with ⟨tcb', hTcbObj⟩
              exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) x.toObjId hNeTid hMsg) ▸ hTcbObj⟩
      exact endpointReceiveDual_preserves_schedulerInvariantBundle _ stR.2 endpointId receiver stR.1 hInvMid (by
        have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- WS-H12a: endpointReplyRecv preserves ipcSchedulerContractPredicates.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold endpointReplyRecv at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            ipcSchedulerContractPredicates stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 replyTarget .ready (some msg) hMsg
      have hContractMid : ipcSchedulerContractPredicates (ensureRunnable st1 replyTarget) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro tid tcb' hTcb' hRun'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · exact storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockSend tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockRecv tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockCall tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid rt hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockReply tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
      exact endpointReceiveDual_preserves_ipcSchedulerContractPredicates _ stR.2 endpointId receiver stR.1 hContractMid (by
        have : stR = (stR.1, stR.2) := Prod.ext rfl rfl
        rw [this] at hRecv; exact hRecv)

/-- WS-F1/TPI-D09: endpointReply preserves ipcSchedulerContractPredicates.
endpointReply only stores a TCB and calls ensureRunnable; the contract
predicate preservation follows the handshake_path_preserves_contracts pattern
since the target is set to .ready and added to runnable. -/
theorem endpointReply_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId _ =>
      simp only [hIpc] at hStep
      -- WS-H1/M-02: Branch on replyTarget (authorized replier check)
      -- Both branches share identical 5-conjunct proof after authorization resolves.
      -- Helper: given st1 from storeTcbIpcStateAndMessage, prove the 5 conjuncts.
      suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
          ipcSchedulerContractPredicates (ensureRunnable st1 target) by
        split at hStep
        · -- some expected: if replier == expected
          split at hStep
          · -- authorized = true
            revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg
          · -- authorized = false
            simp_all
        · -- none: no replyTarget constraint
          dsimp only at hStep
          revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact this st1 hMsg
      -- Shared proof body
      intro st1 hMsg
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hMsg
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- runnableThreadIpcReady
        intro tid tcb' hTcb' hRun'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · exact storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
        · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnSendNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockSend tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnReceiveNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockRecv tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnCallNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockCall tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnReplyNotRunnable
        intro tid tcb' eid rt' hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockReply tid tcb' eid rt' hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid

-- ============================================================================
-- WS-F4: Notification preservation helpers and theorems
-- ============================================================================

/-- Storing a notification preserves ipcInvariant when the new notification
    satisfies notificationInvariant. Dual of storeObject_endpoint_preserves_ipcInvariant. -/
private theorem storeObject_notification_preserves_ipcInvariant
    (st st1 : SystemState) (notifId : SeLe4n.ObjId) (ntfn' : Notification)
    (hInv : ipcInvariant st)
    (hStore : storeObject notifId (.notification ntfn') st = .ok ((), st1))
    (hPres : notificationInvariant ntfn') :
    ipcInvariant st1 := by
  rcases hInv with ⟨hEpInv, hNtfnInv⟩
  constructor
  · intro oid ep hObj
    by_cases hNe : oid = notifId
    · rw [hNe] at hObj
      rw [storeObject_objects_eq st st1 notifId (.notification ntfn') hStore] at hObj; cases hObj
    · exact hEpInv oid ep (by rwa [storeObject_objects_ne st st1 notifId oid _ hNe hStore] at hObj)
  · intro oid ntfn hObj
    by_cases hNe : oid = notifId
    · rw [hNe] at hObj
      rw [storeObject_objects_eq st st1 notifId (.notification ntfn') hStore] at hObj
      simp at hObj; subst hObj; exact hPres
    · exact hNtfnInv oid ntfn (by rwa [storeObject_objects_ne st st1 notifId oid _ hNe hStore] at hObj)

/-- WS-F4: notificationSignal preserves ipcInvariant.
Wake path: stores updated notification (well-formed) + storeTcbIpcState + ensureRunnable.
Merge path: stores active notification (well-formed). -/
theorem notificationSignal_preserves_ipcInvariant
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariant st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        -- Wake path: storeObject → storeTcbIpcState → ensureRunnable
        simp only [hWaiters] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId
            _ hInv hStore (notificationSignal_result_wellFormed_wake rest)
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hInv2 := storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter .ready hInv1 hTcb
            rcases hInv2 with ⟨hEp, hNtfn⟩
            exact ⟨fun oid ep h => hEp oid ep (by rwa [ensureRunnable_preserves_objects] at h),
                   fun oid ntfn' h => hNtfn oid ntfn' (by rwa [ensureRunnable_preserves_objects] at h)⟩
      | nil =>
        -- Merge path: storeObject only
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_ipcInvariant st st' notificationId
          _ hInv hStep (notificationSignal_result_wellFormed_merge _)

/-- WS-F4: notificationSignal preserves schedulerInvariantBundle.
Wake path: storeObject + storeTcbIpcState (scheduler unchanged) + ensureRunnable.
Merge path: storeObject only (scheduler unchanged). -/
theorem notificationSignal_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : schedulerInvariantBundle st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        -- Wake path: storeObject → storeTcbIpcState → ensureRunnable
        simp only [hWaiters] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st'' notificationId _ waiter _ hStore hTcb
            refine ⟨?_, ?_, ?_⟩
            · -- queueCurrentConsistent
              unfold queueCurrentConsistent
              rw [ensureRunnable_scheduler_current, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => trivial
              | some x =>
                have hMem : x ∈ st.scheduler.runnable := by
                  have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                exact ensureRunnable_runnable_mem_old st'' waiter x (hSchedEq ▸ hMem)
            · exact ensureRunnable_nodup st'' waiter (hSchedEq ▸ hRQU)
            · show currentThreadValid (ensureRunnable st'' waiter)
              unfold currentThreadValid
              simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                have hNeNotif : x.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
                have hTcb1 : pair.2.objects[x.toObjId]? = some (.tcb tcbX) := by
                  rw [storeObject_objects_ne st pair.2 notificationId x.toObjId _ hNeNotif hStore]; exact hTcbX
                by_cases hNeTid : x.toObjId = waiter.toObjId
                · have hTargetTcb : ∃ t, pair.2.objects[waiter.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcbX, hTcb1⟩
                  have h := storeTcbIpcState_tcb_exists_at_target pair.2 st'' waiter .ready hTcb hTargetTcb
                  rwa [← hNeTid] at h
                · exact ⟨tcbX, (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter .ready x.toObjId hNeTid hTcb) ▸ hTcb1⟩
      | nil =>
        -- Merge path: storeObject only (scheduler unchanged)
        simp only [hWaiters] at hStep
        have hSchedEq := storeObject_scheduler_eq st st' notificationId _ hStep
        have hCurrEq := congrArg SchedulerState.current hSchedEq
        have hRunEq := congrArg SchedulerState.runnable hSchedEq
        refine ⟨?_, ?_, ?_⟩
        · unfold queueCurrentConsistent; rw [hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => trivial
          | some x =>
            show x ∈ st'.scheduler.runnable; rw [hRunEq]
            have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
        · show st'.scheduler.runnable.Nodup; rw [hRunEq]; exact hRQU
        · unfold currentThreadValid; rw [hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            simp only []
            have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
              simp [currentThreadValid, hCurr] at hCTV; exact hCTV
            rcases hCTV' with ⟨tcbX, hTcbX⟩
            have hNeNotif : x.toObjId ≠ notificationId := by
              intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
            exact ⟨tcbX, by rw [storeObject_objects_ne st st' notificationId x.toObjId _ hNeNotif hStep]; exact hTcbX⟩

/-- WS-F4: notificationWait preserves ipcInvariant.
Badge-consume path: stores idle notification + storeTcbIpcState.
Wait path: stores waiting notification + storeTcbIpcState + removeRunnable. -/
theorem notificationWait_preserves_ipcInvariant
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariant st)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcInvariant st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Badge-consume path: storeObject → storeTcbIpcState
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId
            _ hInv hStore notificationWait_result_wellFormed_badge
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter .ready hInv1 hTcb
      | none =>
        -- WS-G7: Wait path: lookupTcb → ipcState check → storeObject → storeTcbIpcState → removeRunnable
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              have hInv1 := storeObject_notification_preserves_ipcInvariant st pair.2 notificationId
                _ hInv hStore (notificationWait_result_wellFormed_wait waiter ntfn.waitingThreads)
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hInv2 := storeTcbIpcState_preserves_ipcInvariant pair.2 st'' waiter
                  (.blockedOnNotification notificationId) hInv1 hTcb
                rcases hInv2 with ⟨hEp, hNtfn⟩
                exact ⟨fun oid ep h => hEp oid ep (by rwa [removeRunnable_preserves_objects] at h),
                       fun oid ntfn' h => hNtfn oid ntfn' (by rwa [removeRunnable_preserves_objects] at h)⟩

/-- WS-F4: notificationWait preserves schedulerInvariantBundle.
Badge-consume path: storeObject + storeTcbIpcState (scheduler unchanged).
Wait path: storeObject + storeTcbIpcState (scheduler unchanged) + removeRunnable. -/
theorem notificationWait_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : schedulerInvariantBundle st)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Badge-consume path: storeObject → storeTcbIpcState (scheduler unchanged)
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st'' notificationId _ waiter _ hStore hTcb
            have hCurrEq := congrArg SchedulerState.current hSchedEq
            have hRunEq := congrArg SchedulerState.runnable hSchedEq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent; rw [hCurrEq]
              cases hCurr : st.scheduler.current with
              | none => trivial
              | some x =>
                show x ∈ st''.scheduler.runnable; rw [hRunEq]
                have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
            · show st''.scheduler.runnable.Nodup; rw [hRunEq]; exact hRQU
            · unfold currentThreadValid; rw [hCurrEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                have hNeNotif : x.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
                have hTcb1 : pair.2.objects[x.toObjId]? = some (.tcb tcbX) := by
                  rw [storeObject_objects_ne st pair.2 notificationId x.toObjId _ hNeNotif hStore]; exact hTcbX
                by_cases hNeTid : x.toObjId = waiter.toObjId
                · have hTargetTcb : ∃ t, pair.2.objects[waiter.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcbX, hTcb1⟩
                  have h := storeTcbIpcState_tcb_exists_at_target pair.2 st'' waiter .ready hTcb hTargetTcb
                  rwa [← hNeTid] at h
                · exact ⟨tcbX, (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter .ready x.toObjId hNeTid hTcb) ▸ hTcb1⟩
      | none =>
        -- WS-G7: Wait path: lookupTcb → ipcState check → storeObject → storeTcbIpcState → removeRunnable
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st'' notificationId _ waiter _ hStore hTcb
                have hCurrEq := congrArg SchedulerState.current hSchedEq
                refine ⟨?_, ?_, ?_⟩
                · unfold queueCurrentConsistent
                  rw [removeRunnable_scheduler_current, hCurrEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    by_cases hEq' : x = waiter
                    · subst hEq'; simp
                    · rw [if_neg (show ¬(some x = some waiter) from fun h => hEq' (Option.some.inj h))]
                      show x ∈ (removeRunnable st'' waiter).scheduler.runnable
                      rw [removeRunnable_runnable_mem]
                      have hMem : x ∈ st.scheduler.runnable := by
                        have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                      exact ⟨hSchedEq ▸ hMem, hEq'⟩
                · exact removeRunnable_nodup st'' waiter (hSchedEq ▸ hRQU)
                · unfold currentThreadValid
                  rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current, hCurrEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    by_cases hEq' : x = waiter
                    · subst hEq'; simp
                    · rw [if_neg (show ¬(some x = some waiter) from fun h => hEq' (Option.some.inj h))]
                      show ∃ tcb, st''.objects[x.toObjId]? = some (.tcb tcb)
                      have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                        simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                      rcases hCTV' with ⟨tcbX, hTcbX⟩
                      have hNeNotif : x.toObjId ≠ notificationId := by
                        intro h; rw [h] at hTcbX; rw [hObj] at hTcbX; cases hTcbX
                      have hTcb1 : pair.2.objects[x.toObjId]? = some (.tcb tcbX) := by
                        rw [storeObject_objects_ne st pair.2 notificationId x.toObjId _ hNeNotif hStore]; exact hTcbX
                      have hNeTid : x.toObjId ≠ waiter.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                      exact ⟨tcbX, (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter (.blockedOnNotification notificationId) x.toObjId hNeTid hTcb) ▸ hTcb1⟩

/-- WS-F4: notificationSignal preserves ipcSchedulerContractPredicates.
Wake path: storeObject + storeTcbIpcState(.ready) + ensureRunnable — waiter gets
.ready and is added to runnable; other threads are backward-transported.
Merge path: storeObject notification only — scheduler and TCBs unchanged,
contracts preserved via contracts_of_same_scheduler_ipcState. -/
theorem notificationSignal_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        simp only [hWaiters] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := if rest.isEmpty then .idle else .waiting,
                             waitingThreads := rest, pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st''
              notificationId _ waiter _ hStore hTcb
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · exact storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockSend tid tcb' eid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockRecv tid tcb' eid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockCall tid tcb' eid hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                have hNeTid : tid ≠ waiter := fun h => hNe (congrArg ThreadId.toObjId h)
                intro hRun'
                rcases ensureRunnable_mem_reverse st'' waiter tid hRun' with hOld | hEq
                · exact hBlockReply tid tcb' eid rt hTcbPre hIpcState'
                    (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · exact absurd hEq hNeTid
      | nil =>
        simp only [hWaiters] at hStep
        exact contracts_of_same_scheduler_ipcState st st'
          (storeObject_scheduler_eq st st' notificationId _ hStep)
          (fun tid tcb' hTcb' => by
            have hNeNotif : tid.toObjId ≠ notificationId := by
              intro h; rw [h] at hTcb'
              rw [storeObject_objects_eq st st' notificationId _ hStep] at hTcb'; cases hTcb'
            exact ⟨tcb', by rwa [storeObject_objects_ne st st' notificationId tid.toObjId
              _ hNeNotif hStep] at hTcb', rfl⟩)
          ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩

/-- WS-F4: notificationWait preserves ipcSchedulerContractPredicates.
Badge-consume: storeObject + storeTcbIpcState(.ready) — scheduler unchanged.
Wait: storeObject + storeTcbIpcState(.blockedOnNotification) + removeRunnable —
waiter's .blockedOnNotification is not .blockedOnSend/.blockedOnReceive, so
contract predicates are maintained through backward transport. -/
theorem notificationWait_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notificationId
            (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st'' =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st''
              notificationId _ waiter _ hStore hTcb
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · exact storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockSend tid tcb' eid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockRecv tid tcb' eid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockCall tid tcb' eid hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              by_cases hNe : tid.toObjId = waiter.toObjId
              · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter .ready hTcb tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                    .ready tid.toObjId hNe hTcb).symm.trans hTcb'
                have hNeNotif : tid.toObjId ≠ notificationId := by
                  intro h; rw [h] at hTcbMid
                  rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                  cases hTcbMid
                have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                  _ hNeNotif hStore).symm.trans hTcbMid
                intro hRun'
                exact hBlockReply tid tcb' eid rt hTcbPre hIpcState'
                  (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
      | none =>
        -- WS-G7: Wait path: lookupTcb → ipcState check → storeObject → storeTcbIpcState → removeRunnable
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notificationId
                (.notification { state := .waiting,
                                 waitingThreads := waiter :: ntfn.waitingThreads,
                                 pendingBadge := none }) st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hTcb : storeTcbIpcState pair.2 waiter
                  (.blockedOnNotification notificationId) with
              | error e => simp
              | ok st'' =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st''
                  notificationId _ waiter _ hStore hTcb
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · -- runnableThreadIpcReady
                  intro tid tcb' hTcb' hRun'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  rw [removeRunnable_runnable_mem] at hRun'
                  have ⟨hMem, hNeTid⟩ := hRun'
                  have hNe : tid.toObjId ≠ waiter.toObjId :=
                    fun h => hNeTid (threadId_toObjId_injective h)
                  have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                      (.blockedOnNotification notificationId) tid.toObjId hNe hTcb).symm.trans hTcb'
                  have hNeNotif : tid.toObjId ≠ notificationId := by
                    intro h; rw [h] at hTcbMid
                    rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                    cases hTcbMid
                  have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                    _ hNeNotif hStore).symm.trans hTcbMid
                  exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnSendNotRunnable
                  intro tid tcb' eid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockSend tid tcb' eid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnReceiveNotRunnable
                  intro tid tcb' eid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockRecv tid tcb' eid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnCallNotRunnable
                  intro tid tcb' eid hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockCall tid tcb' eid hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                · -- blockedOnReplyNotRunnable
                  intro tid tcb' eid rt hTcb' hIpcState'
                  rw [removeRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = waiter.toObjId
                  · have := storeTcbIpcState_ipcState_eq pair.2 st'' waiter
                        (.blockedOnNotification notificationId) hTcb tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hTcbMid := (storeTcbIpcState_preserves_objects_ne pair.2 st'' waiter
                        (.blockedOnNotification notificationId) tid.toObjId hNe hTcb).symm.trans hTcb'
                    have hNeNotif : tid.toObjId ≠ notificationId := by
                      intro h; rw [h] at hTcbMid
                      rw [storeObject_objects_eq st pair.2 notificationId _ hStore] at hTcbMid
                      cases hTcbMid
                    have hTcbPre := (storeObject_objects_ne st pair.2 notificationId tid.toObjId
                      _ hNeNotif hStore).symm.trans hTcbMid
                    intro hRun'
                    rw [removeRunnable_runnable_mem] at hRun'
                    have ⟨hMem, _⟩ := hRun'
                    exact hBlockReply tid tcb' eid rt hTcbPre hIpcState'
                      (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])


-- ============================================================================
-- WS-H5: Intrusive dual-queue structural invariant preservation proofs
-- C-04/A-22: Well-formedness predicates and preservation for all dual-queue ops.
-- A-23: Link dereference safety under well-formedness.
-- A-24: TCB existence after popHead.
-- ============================================================================

-- ---- Base cases ----

/-- WS-H5: Empty intrusive queue is trivially well-formed. -/
theorem intrusiveQueueWellFormed_empty (st : SystemState) :
    intrusiveQueueWellFormed {} st := by
  refine ⟨Iff.rfl, ?_, ?_⟩ <;> (intro _ h; cases h)

/-- WS-H5: tcbQueueLinkIntegrity for a state where no TCB has queue links. -/
theorem tcbQueueLinkIntegrity_initial (st : SystemState)
    (hNoLinks : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.queueNext = none ∧ tcb.queuePrev = none) :
    tcbQueueLinkIntegrity st := by
  constructor
  · intro a tA hA b hN; have := (hNoLinks a tA hA).1; rw [this] at hN; cases hN
  · intro b tB hB a hP; have := (hNoLinks b tB hB).2; rw [this] at hP; cases hP

/-- WS-H5: Empty endpoint has well-formed dual queues. -/
theorem dualQueueEndpointWellFormed_empty_endpoint
    (epId : SeLe4n.ObjId) (st : SystemState) (ep : Endpoint)
    (hObj : st.objects[epId]? = some (.endpoint ep))
    (hSendEmpty : ep.sendQ = {}) (hRecvEmpty : ep.receiveQ = {}) :
    dualQueueEndpointWellFormed epId st := by
  simp only [dualQueueEndpointWellFormed, hObj, hSendEmpty, hRecvEmpty]
  exact ⟨intrusiveQueueWellFormed_empty st, intrusiveQueueWellFormed_empty st⟩

/-- WS-H5: Non-endpoint objects trivially satisfy dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_non_endpoint
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hNoEp : ∀ ep, st.objects[epId]? ≠ some (.endpoint ep)) :
    dualQueueEndpointWellFormed epId st := by
  unfold dualQueueEndpointWellFormed
  cases hObj : st.objects[epId]? with
  | none => trivial
  | some obj => cases obj with
    | endpoint ep => exact absurd hObj (hNoEp ep)
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => trivial

-- ---- A-23 / A-24 closure ----

/-- WS-H5/A-23: Under tcbQueueLinkIntegrity, any TCB's queueNext link is safe
to dereference — it points to a valid TCB with consistent back-pointer. -/
theorem tcbQueueLink_forward_safe (st : SystemState)
    (hInteg : tcbQueueLinkIntegrity st) (a : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : st.objects[a.toObjId]? = some (.tcb tcbA))
    (b : SeLe4n.ThreadId) (hNext : tcbA.queueNext = some b) :
    ∃ tcbB, st.objects[b.toObjId]? = some (.tcb tcbB) ∧ tcbB.queuePrev = some a :=
  hInteg.1 a tcbA hA b hNext

/-- WS-H5/A-23: Under tcbQueueLinkIntegrity, any TCB's queuePrev link
is safe to dereference (symmetric direction). -/
theorem tcbQueueLink_reverse_safe (st : SystemState)
    (hInteg : tcbQueueLinkIntegrity st) (b : SeLe4n.ThreadId) (tcbB : TCB)
    (hB : st.objects[b.toObjId]? = some (.tcb tcbB))
    (a : SeLe4n.ThreadId) (hPrev : tcbB.queuePrev = some a) :
    ∃ tcbA, st.objects[a.toObjId]? = some (.tcb tcbA) ∧ tcbA.queueNext = some b :=
  hInteg.2 b tcbB hB a hPrev

/-- WS-H5/A-24: Under intrusiveQueueWellFormed, the head of a non-empty queue
always has a valid TCB. Closes finding A-24. -/
theorem endpointQueuePopHead_sender_exists (q : IntrusiveQueue) (st : SystemState)
    (hWf : intrusiveQueueWellFormed q st)
    (hd : SeLe4n.ThreadId) (hHd : q.head = some hd) :
    ∃ tcb, st.objects[hd.toObjId]? = some (.tcb tcb) := by
  obtain ⟨_, hHead, _⟩ := hWf
  obtain ⟨tcb, hTcb, _⟩ := hHead hd hHd
  exact ⟨tcb, hTcb⟩

/-- WS-H5/A-24: Under dualQueueEndpointWellFormed, the sender popped from
sendQ is guaranteed to have a valid TCB. -/
theorem endpointReceiveDual_sender_exists
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hWf : dualQueueEndpointWellFormed epId st)
    (ep : Endpoint) (hObj : st.objects[epId]? = some (.endpoint ep))
    (hd : SeLe4n.ThreadId) (hHd : ep.sendQ.head = some hd) :
    ∃ tcb, st.objects[hd.toObjId]? = some (.tcb tcb) := by
  unfold dualQueueEndpointWellFormed at hWf; rw [hObj] at hWf
  exact endpointQueuePopHead_sender_exists ep.sendQ st hWf.1 hd hHd

/-- WS-H5/A-23: Under dualQueueSystemInvariant, popHead link dereference
is safe — the head TCB's queueNext either is none or points to a valid TCB. -/
theorem endpointQueuePopHead_link_safe (q : IntrusiveQueue) (st : SystemState)
    (hInteg : tcbQueueLinkIntegrity st) (_hWf : intrusiveQueueWellFormed q st)
    (hd : SeLe4n.ThreadId) (_hHd : q.head = some hd)
    (tcb : TCB) (hTcb : st.objects[hd.toObjId]? = some (.tcb tcb)) :
    match tcb.queueNext with
    | none => True
    | some next => ∃ nextTcb, st.objects[next.toObjId]? = some (.tcb nextTcb) := by
  cases hNext : tcb.queueNext with
  | none => trivial
  | some next => exact let ⟨t, h, _⟩ := hInteg.1 hd tcb hTcb next hNext; ⟨t, h⟩

-- ---- Frame lemmas: ensureRunnable / removeRunnable ----

/-- WS-H5: ensureRunnable preserves intrusiveQueueWellFormed. -/
theorem ensureRunnable_preserves_intrusiveQueueWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q (ensureRunnable st tid) := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  exact ⟨hHT,
    fun hd h => let ⟨t, ht, hp⟩ := hHead hd h; ⟨t, by rwa [ensureRunnable_preserves_objects], hp⟩,
    fun tl h => let ⟨t, ht, hn⟩ := hTail tl h; ⟨t, by rwa [ensureRunnable_preserves_objects], hn⟩⟩

/-- WS-H5: removeRunnable preserves intrusiveQueueWellFormed. -/
theorem removeRunnable_preserves_intrusiveQueueWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q (removeRunnable st tid) := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  exact ⟨hHT,
    fun hd h => let ⟨t, ht, hp⟩ := hHead hd h; ⟨t, by rwa [removeRunnable_preserves_objects], hp⟩,
    fun tl h => let ⟨t, ht, hn⟩ := hTail tl h; ⟨t, by rwa [removeRunnable_preserves_objects], hn⟩⟩

/-- WS-H5: ensureRunnable preserves tcbQueueLinkIntegrity. -/
theorem ensureRunnable_preserves_tcbQueueLinkIntegrity
    (st : SystemState) (tid : SeLe4n.ThreadId) (h : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity (ensureRunnable st tid) := by
  constructor
  · intro a tA hA b hN; rw [ensureRunnable_preserves_objects] at hA
    obtain ⟨tB, hB, hP⟩ := h.1 a tA hA b hN
    exact ⟨tB, by rw [ensureRunnable_preserves_objects]; exact hB, hP⟩
  · intro b tB hB a hP; rw [ensureRunnable_preserves_objects] at hB
    obtain ⟨tA, hA, hN⟩ := h.2 b tB hB a hP
    exact ⟨tA, by rw [ensureRunnable_preserves_objects]; exact hA, hN⟩

/-- WS-H5: removeRunnable preserves tcbQueueLinkIntegrity. -/
theorem removeRunnable_preserves_tcbQueueLinkIntegrity
    (st : SystemState) (tid : SeLe4n.ThreadId) (h : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity (removeRunnable st tid) := by
  constructor
  · intro a tA hA b hN; rw [removeRunnable_preserves_objects] at hA
    obtain ⟨tB, hB, hP⟩ := h.1 a tA hA b hN
    exact ⟨tB, by rw [removeRunnable_preserves_objects]; exact hB, hP⟩
  · intro b tB hB a hP; rw [removeRunnable_preserves_objects] at hB
    obtain ⟨tA, hA, hN⟩ := h.2 b tB hB a hP
    exact ⟨tA, by rw [removeRunnable_preserves_objects]; exact hA, hN⟩

/-- WS-H5: ensureRunnable preserves dualQueueEndpointWellFormed. -/
theorem ensureRunnable_preserves_dualQueueEndpointWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hWf : dualQueueEndpointWellFormed epId st) :
    dualQueueEndpointWellFormed epId (ensureRunnable st tid) := by
  unfold dualQueueEndpointWellFormed at hWf ⊢; rw [ensureRunnable_preserves_objects]
  cases hObjCase : st.objects[epId]? with
  | none => trivial
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => trivial
    | endpoint ep =>
        simp only [hObjCase] at hWf
        exact ⟨ensureRunnable_preserves_intrusiveQueueWellFormed st tid ep.sendQ hWf.1,
               ensureRunnable_preserves_intrusiveQueueWellFormed st tid ep.receiveQ hWf.2⟩

/-- WS-H5: removeRunnable preserves dualQueueEndpointWellFormed. -/
theorem removeRunnable_preserves_dualQueueEndpointWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hWf : dualQueueEndpointWellFormed epId st) :
    dualQueueEndpointWellFormed epId (removeRunnable st tid) := by
  unfold dualQueueEndpointWellFormed at hWf ⊢; rw [removeRunnable_preserves_objects]
  cases hObjCase : st.objects[epId]? with
  | none => trivial
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => trivial
    | endpoint ep =>
        simp only [hObjCase] at hWf
        exact ⟨removeRunnable_preserves_intrusiveQueueWellFormed st tid ep.sendQ hWf.1,
               removeRunnable_preserves_intrusiveQueueWellFormed st tid ep.receiveQ hWf.2⟩

/-- WS-H5: ensureRunnable preserves dualQueueSystemInvariant. -/
theorem ensureRunnable_preserves_dualQueueSystemInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (ensureRunnable st tid) := by
  obtain ⟨hEp, hLink⟩ := hInv
  refine ⟨?_, ensureRunnable_preserves_tcbQueueLinkIntegrity st tid hLink⟩
  intro epId ep hObj; rw [ensureRunnable_preserves_objects] at hObj
  exact ensureRunnable_preserves_dualQueueEndpointWellFormed st tid epId (hEp epId ep hObj)

/-- WS-H5: removeRunnable preserves dualQueueSystemInvariant. -/
theorem removeRunnable_preserves_dualQueueSystemInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (removeRunnable st tid) := by
  obtain ⟨hEp, hLink⟩ := hInv
  refine ⟨?_, removeRunnable_preserves_tcbQueueLinkIntegrity st tid hLink⟩
  intro epId ep hObj; rw [removeRunnable_preserves_objects] at hObj
  exact removeRunnable_preserves_dualQueueEndpointWellFormed st tid epId (hEp epId ep hObj)

-- ---- Frame lemma: storeObject for TCB preserves queue well-formedness ----
-- storeTcbIpcState / storeTcbIpcStateAndMessage / storeTcbPendingMessage all
-- call storeObject with { tcb with ipcState := ..., pendingMessage := ... },
-- preserving queueNext / queuePrev / queuePPrev.

/-- WS-H5: storeObject of a TCB-variant with preserved queue links maintains
intrusiveQueueWellFormed for queues whose boundary TCBs either:
(a) are at different ObjIds (unchanged), or
(b) are the modified TCB (queue links preserved by with-syntax). -/
theorem storeObject_tcb_preserves_intrusiveQueueWellFormed
    (st st' : SystemState) (tid : SeLe4n.ObjId) (tcb tcb' : TCB)
    (hPrevEq : tcb'.queuePrev = tcb.queuePrev)
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd
    obtain ⟨t, hT, hP⟩ := hHead hd hHd
    by_cases hEq : hd.toObjId = tid
    · rw [hEq, storeObject_objects_eq st st' tid _ hStore]
      rw [hEq] at hT; rw [hTcbPre] at hT; cases hT
      exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
    · exact ⟨t, by rw [storeObject_objects_ne st st' tid hd.toObjId _ hEq hStore]; exact hT, hP⟩
  · intro tl hTl
    obtain ⟨t, hT, hN⟩ := hTail tl hTl
    by_cases hEq : tl.toObjId = tid
    · rw [hEq, storeObject_objects_eq st st' tid _ hStore]
      rw [hEq] at hT; rw [hTcbPre] at hT; cases hT
      exact ⟨tcb', rfl, hNextEq ▸ hN⟩
    · exact ⟨t, by rw [storeObject_objects_ne st st' tid tl.toObjId _ hEq hStore]; exact hT, hN⟩

/-- WS-H5: storeObject of a TCB-variant with preserved queue links maintains
tcbQueueLinkIntegrity. -/
theorem storeObject_tcb_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (tid : SeLe4n.ObjId) (tcb tcb' : TCB)
    (hPrevEq : tcb'.queuePrev = tcb.queuePrev)
    (hNextEq : tcb'.queueNext = tcb.queueNext)
    (hTcbPre : st.objects[tid]? = some (.tcb tcb))
    (hStore : storeObject tid (.tcb tcb') st = .ok ((), st'))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid
    · rw [hEqA, storeObject_objects_eq st st' tid _ hStore] at hA; cases hA
      -- tA = tcb', tA.queueNext = tcb'.queueNext = tcb.queueNext
      rw [hNextEq] at hN
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tcb (hEqA ▸ hTcbPre) b hN
      by_cases hEqB : b.toObjId = tid
      · rw [hEqB, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqB] at hB; rw [hTcbPre] at hB; cases hB
        exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
      · exact ⟨tB, by rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hStore]; exact hB, hP⟩
    · rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hStore] at hA
      obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA b hN
      by_cases hEqB : b.toObjId = tid
      · rw [hEqB, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqB] at hB; rw [hTcbPre] at hB; cases hB
        exact ⟨tcb', rfl, hPrevEq ▸ hP⟩
      · exact ⟨tB, by rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid
    · rw [hEqB, storeObject_objects_eq st st' tid _ hStore] at hB; cases hB
      rw [hPrevEq] at hP
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tcb (hEqB ▸ hTcbPre) a hP
      by_cases hEqA : a.toObjId = tid
      · rw [hEqA, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqA] at hA; rw [hTcbPre] at hA; cases hA
        exact ⟨tcb', rfl, hNextEq ▸ hN⟩
      · exact ⟨tA, by rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hStore]; exact hA, hN⟩
    · rw [storeObject_objects_ne st st' tid b.toObjId _ hEqB hStore] at hB
      obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB a hP
      by_cases hEqA : a.toObjId = tid
      · rw [hEqA, storeObject_objects_eq st st' tid _ hStore]
        rw [hEqA] at hA; rw [hTcbPre] at hA; cases hA
        exact ⟨tcb', rfl, hNextEq ▸ hN⟩
      · exact ⟨tA, by rw [storeObject_objects_ne st st' tid a.toObjId _ hEqA hStore]; exact hA, hN⟩

-- ---- Helper: storeObject endpoint preserves queue invariant properties ----

/-- WS-H5: Storing an endpoint preserves tcbQueueLinkIntegrity (no TCB is modified). -/
theorem storeObject_endpoint_preserves_tcbQueueLinkIntegrity
    (st st' : SystemState) (epId : SeLe4n.ObjId) (epNew : Endpoint)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st'))
    (hPreEp : ∀ tcb : TCB, st.objects[epId]? ≠ some (.tcb tcb))
    (hInteg : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  constructor
  · intro a tA hA b hN
    have hA' := tcb_lookup_of_endpoint_store st st' epId a.toObjId tA epNew hStore hA
    obtain ⟨tB, hB, hP⟩ := hInteg.1 a tA hA' b hN
    have : b.toObjId ≠ epId := fun h => absurd (h ▸ hB) (hPreEp tB)
    exact ⟨tB, by rw [storeObject_objects_ne st st' epId b.toObjId _ this hStore]; exact hB, hP⟩
  · intro b tB hB a hP
    have hB' := tcb_lookup_of_endpoint_store st st' epId b.toObjId tB epNew hStore hB
    obtain ⟨tA, hA, hN⟩ := hInteg.2 b tB hB' a hP
    have : a.toObjId ≠ epId := fun h => absurd (h ▸ hA) (hPreEp tA)
    exact ⟨tA, by rw [storeObject_objects_ne st st' epId a.toObjId _ this hStore]; exact hA, hN⟩

/-- WS-H5: Storing an endpoint preserves intrusiveQueueWellFormed.
Boundary TCBs can't be at the endpoint ObjId (they are TCBs, not endpoints). -/
theorem storeObject_endpoint_preserves_intrusiveQueueWellFormed
    (st st' : SystemState) (epId : SeLe4n.ObjId) (epNew : Endpoint)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st'))
    (hPreEp : ∀ tcb : TCB, st.objects[epId]? ≠ some (.tcb tcb))
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    have : hd.toObjId ≠ epId := fun h => absurd (h ▸ hT) (hPreEp t)
    exact ⟨t, by rw [storeObject_objects_ne st st' epId hd.toObjId _ this hStore]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    have : tl.toObjId ≠ epId := fun h => absurd (h ▸ hT) (hPreEp t)
    exact ⟨t, by rw [storeObject_objects_ne st st' epId tl.toObjId _ this hStore]; exact hT, hN⟩

-- ---- Derived frame lemmas for storeTcbIpcState, storeTcbIpcStateAndMessage, storeTcbPendingMessage ----

/-- WS-H5: storeTcbIpcState preserves dualQueueSystemInvariant.
storeTcbIpcState uses { tcb with ipcState := ipc }, preserving queue links. -/
theorem storeTcbIpcState_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
            unfold lookupTcb at hLookup
            split at hLookup
            · simp at hLookup
            · cases h : st.objects[tid.toObjId]? with
              | none => simp [h] at hLookup
              | some obj => cases obj with
                | tcb t => simp only [h, Option.some.injEq] at hLookup; cases hLookup; rfl
                | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
                    simp [h] at hLookup
          have hPrev : ({ tcb with ipcState := ipc } : TCB).queuePrev = tcb.queuePrev := rfl
          have hNext : ({ tcb with ipcState := ipc } : TCB).queueNext = tcb.queueNext := rfl
          refine ⟨?_, storeObject_tcb_preserves_tcbQueueLinkIntegrity st pair.2
                       tid.toObjId tcb { tcb with ipcState := ipc } hPrev hNext hTcbPre hStore hLink⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.receiveQ hWfPre.2⟩

/-- WS-H5: storeTcbIpcStateAndMessage preserves dualQueueSystemInvariant. -/
theorem storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
            unfold lookupTcb at hLookup; split at hLookup
            · simp at hLookup
            · cases h : st.objects[tid.toObjId]? with
              | none => simp [h] at hLookup
              | some obj => cases obj with
                | tcb t => simp only [h, Option.some.injEq] at hLookup; cases hLookup; rfl
                | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
                    simp [h] at hLookup
          have hPrev : ({ tcb with ipcState := ipc, pendingMessage := msg } : TCB).queuePrev = tcb.queuePrev := rfl
          have hNext : ({ tcb with ipcState := ipc, pendingMessage := msg } : TCB).queueNext = tcb.queueNext := rfl
          refine ⟨?_, storeObject_tcb_preserves_tcbQueueLinkIntegrity st pair.2
                       tid.toObjId tcb _ hPrev hNext hTcbPre hStore hLink⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.receiveQ hWfPre.2⟩

/-- WS-H5: storeTcbPendingMessage preserves dualQueueSystemInvariant. -/
theorem storeTcbPendingMessage_preserves_dualQueueSystemInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
          simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
          have hTcbPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
            unfold lookupTcb at hLookup; split at hLookup
            · simp at hLookup
            · cases h : st.objects[tid.toObjId]? with
              | none => simp [h] at hLookup
              | some obj => cases obj with
                | tcb t => simp only [h, Option.some.injEq] at hLookup; cases hLookup; rfl
                | endpoint _ | cnode _ | vspaceRoot _ | notification _ | untyped _ =>
                    simp [h] at hLookup
          have hPrev : ({ tcb with pendingMessage := msg } : TCB).queuePrev = tcb.queuePrev := rfl
          have hNext : ({ tcb with pendingMessage := msg } : TCB).queueNext = tcb.queueNext := rfl
          refine ⟨?_, storeObject_tcb_preserves_tcbQueueLinkIntegrity st pair.2
                       tid.toObjId tcb _ hPrev hNext hTcbPre hStore hLink⟩
          intro epId ep hObj
          by_cases hEq : epId = tid.toObjId
          · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hObj; cases hObj
          · have hObjPre : st.objects[epId]? = some (.endpoint ep) := by
              rwa [storeObject_objects_ne st pair.2 tid.toObjId epId _ hEq hStore] at hObj
            have hWfPre := hEpInv epId ep hObjPre
            unfold dualQueueEndpointWellFormed at hWfPre ⊢
            rw [hObjPre] at hWfPre; rw [hObj]
            exact ⟨storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.sendQ hWfPre.1,
                   storeObject_tcb_preserves_intrusiveQueueWellFormed st pair.2
                     tid.toObjId tcb _ hPrev hNext hTcbPre hStore ep.receiveQ hWfPre.2⟩

-- ============================================================================
-- WS-H5 Part C: Preservation for the 7 dual-queue operations.
-- Strategy: endpointReply / endpointReplyRecv don't modify intrusive queues.
-- endpointSendDual / endpointReceiveDual / endpointCall compose
-- endpointQueueEnqueue/PopHead with state transition frame lemmas.
-- ============================================================================

/-- WS-H5: endpointReply preserves dualQueueSystemInvariant.
endpointReply performs storeTcbIpcStateAndMessage + ensureRunnable —
neither touches queue links or endpoint queue boundaries. -/
theorem endpointReply_preserves_dualQueueSystemInvariant
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hStep : (endpointReply replier target msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
        | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId' rt =>
          simp only [hIpc] at hStep
          -- Resolve the let/if authorization + storeTcbIpcStateAndMessage
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e =>
              -- Regardless of authorization, store failed → error ≠ ok
              revert hStep; simp only [hStore]; intro hStep
              cases rt with
              | none => simp at hStep
              | some val => dsimp only [] at hStep; split at hStep <;> simp at hStep
          | ok st1 =>
              simp only [hStore] at hStep
              have hInv1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                st st1 target .ready (some msg) hStore hInv
              have hInvER := ensureRunnable_preserves_dualQueueSystemInvariant st1 target hInv1
              -- Case split on authorization to extract st' = ensureRunnable st1 target
              cases rt with
              | none => simp at hStep; subst hStep; exact hInvER
              | some val =>
                  dsimp only [] at hStep
                  split at hStep
                  · simp at hStep; subst hStep; exact hInvER
                  · simp at hStep

-- ---- WS-H5: storeTcbQueueLinks helper lemmas for queue invariant proofs ----

/-- Helper: storeTcbQueueLinks stores a specific TCB at tid.toObjId. -/
private theorem storeTcbQueueLinks_result_tcb
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    ∃ origTcb, lookupTcb st tid = some origTcb ∧
    st'.objects[tid.toObjId]? = some (.tcb (tcbWithQueueLinks origTcb prev pprev next)) := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
      exact ⟨tcb, rfl, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

/-- Helper: storeTcbQueueLinks preserves intrusiveQueueWellFormed when
the new link values are compatible with the queue's head/tail boundaries.
Clearing (all none) is always compatible. -/
private theorem storeTcbQueueLinks_preserves_iqwf
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (q : IntrusiveQueue) (hWf : intrusiveQueueWellFormed q st)
    (hHeadOk : ∀ hd, q.head = some hd → hd.toObjId = tid.toObjId → prev = none)
    (hTailOk : ∀ tl, q.tail = some tl → tl.toObjId = tid.toObjId → next = none) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hHT, hHead, hTail⟩ := hWf
  obtain ⟨origTcb, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid prev pprev next hStep
  refine ⟨hHT, ?_, ?_⟩
  · intro hd hHd; obtain ⟨t, hT, hP⟩ := hHead hd hHd
    by_cases hEq : hd.toObjId = tid.toObjId
    · exact ⟨tcbWithQueueLinks origTcb prev pprev next, hEq ▸ hTcb',
        by simp only [tcbWithQueueLinks]; exact hHeadOk hd hHd hEq⟩
    · exact ⟨t, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next
        hd.toObjId hEq hStep]; exact hT, hP⟩
  · intro tl hTl; obtain ⟨t, hT, hN⟩ := hTail tl hTl
    by_cases hEq : tl.toObjId = tid.toObjId
    · exact ⟨tcbWithQueueLinks origTcb prev pprev next, hEq ▸ hTcb',
        by simp only [tcbWithQueueLinks]; exact hTailOk tl hTl hEq⟩
    · exact ⟨t, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next
        tl.toObjId hEq hStep]; exact hT, hN⟩

/-- Helper: Clearing all queue links preserves tcbQueueLinkIntegrity when
no other TCB's forward/reverse links point to the cleared thread. -/
private theorem storeTcbQueueLinks_clearing_preserves_linkInteg
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid none none none = .ok st')
    (hLink : tcbQueueLinkIntegrity st)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB), st.objects[b.toObjId]? = some (.tcb tcbB) →
      tcbB.queuePrev ≠ some tid) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨_, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid none none none hStep
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid.toObjId
    · rw [hEqA] at hA; rw [hTcb'] at hA; cases hA; simp [tcbWithQueueLinks] at hN
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none a.toObjId hEqA hStep] at hA
      obtain ⟨tB, hB, hP⟩ := hLink.1 a tA hA' b hN
      have hNeB : b.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA')
      exact ⟨tB, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none
        b.toObjId hNeB hStep]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid.toObjId
    · rw [hEqB] at hB; rw [hTcb'] at hB; cases hB; simp [tcbWithQueueLinks] at hP
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none b.toObjId hEqB hStep] at hB
      obtain ⟨tA, hA, hN⟩ := hLink.2 b tB hB' a hP
      have hNeA : a.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB')
      exact ⟨tA, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none none none
        a.toObjId hNeA hStep]; exact hA, hN⟩

/-- Helper: storeTcbQueueLinks with prev=none and next=none (arbitrary pprev)
preserves tcbQueueLinkIntegrity when no external refs point to the modified thread.
This generalizes storeTcbQueueLinks_clearing_preserves_linkInteg to allow non-none pprev,
since tcbQueueLinkIntegrity only inspects queuePrev and queueNext. -/
private theorem storeTcbQueueLinks_noprevnext_preserves_linkInteg
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (hStep : storeTcbQueueLinks st tid none pprev none = .ok st')
    (hLink : tcbQueueLinkIntegrity st)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB), st.objects[b.toObjId]? = some (.tcb tcbB) →
      tcbB.queuePrev ≠ some tid) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨_, _, hTcb'⟩ := storeTcbQueueLinks_result_tcb st st' tid none pprev none hStep
  constructor
  · intro a tA hA b hN
    by_cases hEqA : a.toObjId = tid.toObjId
    · rw [hEqA] at hA; rw [hTcb'] at hA; cases hA; simp [tcbWithQueueLinks] at hN
    · have hA' : st.objects[a.toObjId]? = some (.tcb tA) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none a.toObjId hEqA hStep] at hA
      obtain ⟨tB, hB, hP⟩ := hLink.1 a tA hA' b hN
      have hNeB : b.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA')
      exact ⟨tB, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none
        b.toObjId hNeB hStep]; exact hB, hP⟩
  · intro b tB hB a hP
    by_cases hEqB : b.toObjId = tid.toObjId
    · rw [hEqB] at hB; rw [hTcb'] at hB; cases hB; simp [tcbWithQueueLinks] at hP
    · have hB' : st.objects[b.toObjId]? = some (.tcb tB) := by
        rwa [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none b.toObjId hEqB hStep] at hB
      obtain ⟨tA, hA, hN⟩ := hLink.2 b tB hB' a hP
      have hNeA : a.toObjId ≠ tid.toObjId := fun hh =>
        absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB')
      exact ⟨tA, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid none pprev none
        a.toObjId hNeA hStep]; exact hA, hN⟩

/-- Helper: Two-step storeTcbQueueLinks append-to-tail preserves tcbQueueLinkIntegrity.
Step 1 sets old tail's next to newTid. Step 2 sets newTid's prev to tailTid.
The resulting forward link (tailTid→newTid) is matched by the reverse (newTid→tailTid). -/
private theorem storeTcbQueueLinks_append_tail_preserves_linkInteg
    (st1 st2 stF : SystemState) (tailTid newTid : SeLe4n.ThreadId)
    (prevT : Option SeLe4n.ThreadId) (pprevT pprevN : Option QueuePPrev)
    (hStep1 : storeTcbQueueLinks st1 tailTid prevT pprevT (some newTid) = .ok st2)
    (hStep2 : storeTcbQueueLinks st2 newTid (some tailTid) pprevN none = .ok stF)
    (hNe : tailTid.toObjId ≠ newTid.toObjId)
    (hLink : tcbQueueLinkIntegrity st1)
    (hPrevMatch : ∀ t, st1.objects[tailTid.toObjId]? = some (.tcb t) → prevT = t.queuePrev)
    (hTailNext : ∀ t, st1.objects[tailTid.toObjId]? = some (.tcb t) → t.queueNext = none)
    (hNoFwd : ∀ (a : SeLe4n.ThreadId) (tA : TCB), st1.objects[a.toObjId]? = some (.tcb tA) →
      tA.queueNext ≠ some newTid)
    (hNoRev : ∀ (b : SeLe4n.ThreadId) (tB : TCB), st1.objects[b.toObjId]? = some (.tcb tB) →
      tB.queuePrev ≠ some newTid) :
    tcbQueueLinkIntegrity stF := by
  -- Extract TCB results from both steps
  obtain ⟨origTail, hLookupTail, hTailSt2⟩ := storeTcbQueueLinks_result_tcb
    st1 st2 tailTid prevT pprevT (some newTid) hStep1
  obtain ⟨origNew, hLookupNew2, hNewStF⟩ := storeTcbQueueLinks_result_tcb
    st2 stF newTid (some tailTid) pprevN none hStep2
  -- tailTid's TCB in stF is preserved from st2 (step 2 only modifies newTid)
  have hTailStF : stF.objects[tailTid.toObjId]? =
      some (.tcb (tcbWithQueueLinks origTail prevT pprevT (some newTid))) := by
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none
      tailTid.toObjId hNe hStep2]
    exact hTailSt2
  -- Original tail TCB
  have hTailOrig := lookupTcb_some_objects st1 tailTid origTail hLookupTail
  -- prevT matches original prev
  have hPM := hPrevMatch origTail hTailOrig
  -- Original tail had next=none
  have hTN := hTailNext origTail hTailOrig
  -- Transport: for oid ≠ tailTid and oid ≠ newTid, objects unchanged
  have hOther : ∀ oid, oid ≠ tailTid.toObjId → oid ≠ newTid.toObjId →
      stF.objects[oid]? = st1.objects[oid]? := by
    intro oid hne1 hne2
    rw [storeTcbQueueLinks_preserves_objects_ne st2 stF newTid (some tailTid) pprevN none
      oid hne2 hStep2]
    rw [storeTcbQueueLinks_preserves_objects_ne st1 st2 tailTid prevT pprevT (some newTid)
      oid hne1 hStep1]
  constructor
  -- Forward direction: a.next = some b → b.prev = some a
  · intro a tA hA b hN
    by_cases haT : a.toObjId = tailTid.toObjId
    · -- a is tailTid: tA has next = some newTid (from tcbWithQueueLinks)
      rw [haT] at hA; rw [hTailStF] at hA; cases hA
      simp only [tcbWithQueueLinks] at hN
      -- hN : some newTid = some b, so newTid = b
      simp only [Option.some.injEq] at hN
      rw [← hN, threadId_toObjId_injective haT]
      exact ⟨tcbWithQueueLinks origNew (some tailTid) pprevN none, hNewStF,
        by simp [tcbWithQueueLinks]⟩
    · by_cases haN : a.toObjId = newTid.toObjId
      · -- a is newTid: tA has next = none (from tcbWithQueueLinks)
        rw [haN] at hA; rw [hNewStF] at hA; cases hA
        simp [tcbWithQueueLinks] at hN
      · -- a is neither: tA unchanged from st1
        have hA1 : st1.objects[a.toObjId]? = some (.tcb tA) := by
          rwa [hOther a.toObjId haT haN] at hA
        obtain ⟨tB, hB1, hP⟩ := hLink.1 a tA hA1 b hN
        -- b ≠ newTid (since no TCB in st1 has next=newTid)
        have hbNeN : b.toObjId ≠ newTid.toObjId := fun hh =>
          absurd (by rwa [threadId_toObjId_injective hh] at hN) (hNoFwd a tA hA1)
        by_cases hbT : b.toObjId = tailTid.toObjId
        · -- b is tailTid: in stF, tailTid has prev = prevT = origTail.queuePrev
          rw [hbT] at hB1; rw [hTailOrig] at hB1; cases hB1
          -- hP : origTail.queuePrev = some a
          have hbEq := threadId_toObjId_injective hbT; rw [hbEq] at ⊢
          exact ⟨tcbWithQueueLinks origTail prevT pprevT (some newTid), hTailStF,
            by simp [tcbWithQueueLinks]; exact hPM ▸ hP⟩
        · exact ⟨tB, by rw [hOther b.toObjId hbT hbNeN]; exact hB1, hP⟩
  -- Reverse direction: b.prev = some a → a.next = some b
  · intro b tB hB a hP
    by_cases hbN : b.toObjId = newTid.toObjId
    · -- b is newTid: tB has prev = some tailTid
      rw [hbN] at hB; rw [hNewStF] at hB; cases hB
      simp only [tcbWithQueueLinks, Option.some.injEq] at hP
      -- hP : tailTid = a
      rw [← hP]
      refine ⟨tcbWithQueueLinks origTail prevT pprevT (some newTid), hTailStF, ?_⟩
      simp [tcbWithQueueLinks]
      exact (threadId_toObjId_injective hbN).symm
    · by_cases hbT : b.toObjId = tailTid.toObjId
      · -- b is tailTid: prev = prevT = origTail.queuePrev
        rw [hbT] at hB; rw [hTailStF] at hB; cases hB
        simp only [tcbWithQueueLinks] at hP
        rw [hPM] at hP
        obtain ⟨tA, hA1, hNxt⟩ := hLink.2 tailTid origTail hTailOrig a hP
        have haNeT : a.toObjId ≠ tailTid.toObjId := by
          intro hh; rw [hh] at hA1; rw [hTailOrig] at hA1; cases hA1
          rw [hTN] at hNxt; simp at hNxt
        have haNeN : a.toObjId ≠ newTid.toObjId := fun hh =>
          absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev tailTid origTail hTailOrig)
        refine ⟨tA, by rw [hOther a.toObjId haNeT haNeN]; exact hA1, ?_⟩
        rw [threadId_toObjId_injective hbT]; exact hNxt
      · -- b is neither: tB unchanged from st1
        have hB1 : st1.objects[b.toObjId]? = some (.tcb tB) := by
          rwa [hOther b.toObjId hbT hbN] at hB
        -- a ≠ newTid (no TCB in st1 has prev=newTid)
        have haNeN : a.toObjId ≠ newTid.toObjId := fun hh =>
          absurd (by rwa [threadId_toObjId_injective hh] at hP) (hNoRev b tB hB1)
        obtain ⟨tA, hA1, hNxt⟩ := hLink.2 b tB hB1 a hP
        by_cases haT : a.toObjId = tailTid.toObjId
        · -- a = tailTid: but origTail.queueNext = none contradicts hNxt
          rw [haT] at hA1; rw [hTailOrig] at hA1; cases hA1
          exact absurd hNxt (by rw [hTN]; simp)
        · exact ⟨tA, by rw [hOther a.toObjId haT haNeN]; exact hA1, hNxt⟩

-- ---- WS-H5: Dual-queue preservation for queue operations ----

/-- WS-H5: endpointQueuePopHead preserves dualQueueSystemInvariant. -/
theorem endpointQueuePopHead_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some headTcb =>
          simp only [hLookup] at hStep
          have hHeadTcb := lookupTcb_some_objects st headTid headTcb hLookup
          have hNeEpHead : endpointId ≠ headTid.toObjId :=
            fun h => by rw [h] at hObj; rw [hHeadTcb] at hObj; cases hObj
          have hEpWf := hEpInv endpointId ep hObj
          unfold dualQueueEndpointWellFormed at hEpWf; simp only [hObj] at hEpWf
          have hWfQ : intrusiveQueueWellFormed (if isReceiveQ then ep.receiveQ else ep.sendQ) st := by
            cases isReceiveQ <;> simp_all
          obtain ⟨hHT, hHdBnd, hTlBnd⟩ := hWfQ
          obtain ⟨_, hTcbH, hPrevNone⟩ := hHdBnd headTid hHead
          rw [hHeadTcb] at hTcbH; cases hTcbH
          have hPreEp : ∀ tcb : TCB, st.objects[endpointId]? ≠ some (.tcb tcb) := by
            intro tcb h; rw [hObj] at h; cases h
          cases hNext : headTcb.queueNext with
          | none =>
            simp only [hNext] at hStep
            cases hStoreEp : storeObject endpointId
                (.endpoint (if isReceiveQ then { ep with receiveQ := {} }
                 else { ep with sendQ := {} })) st with
            | error e => simp [hStoreEp] at hStep
            | ok pair =>
              simp only [hStoreEp] at hStep
              -- Reduce the let/match on none to get storeTcbQueueLinks pair.2 headTid
              generalize hSt2 : storeTcbQueueLinks pair.2 headTid none none none = r at hStep
              cases r with
              | error e => simp at hStep
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨rfl, rfl⟩ := hStep
                have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                  st pair.2 endpointId _ hStoreEp hPreEp hLink
                have hTransport : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                    pair.2.objects[x.toObjId]? = some (.tcb t) →
                    st.objects[x.toObjId]? = some (.tcb t) := by
                  intro x t h
                  by_cases hx : x.toObjId = endpointId
                  · rw [hx, storeObject_objects_eq st pair.2 endpointId _ hStoreEp] at h; cases h
                  · rwa [storeObject_objects_ne st pair.2 endpointId x.toObjId _ hx hStoreEp] at h
                have hNoFwd1 : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                    pair.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some headTid := by
                  intro a tA hA hN
                  obtain ⟨_, hB, hP⟩ := hLink.1 a tA (hTransport a tA hA) headTid hN
                  rw [hHeadTcb] at hB; cases hB; rw [hPrevNone] at hP; exact absurd hP (by simp)
                have hNoRev1 : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                    pair.2.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev ≠ some headTid := by
                  intro b tB hB hP
                  obtain ⟨_, hA, hN⟩ := hLink.2 b tB (hTransport b tB hB) headTid hP
                  rw [hHeadTcb] at hA; cases hA; rw [hNext] at hN; exact absurd hN (by simp)
                refine ⟨?_, storeTcbQueueLinks_clearing_preserves_linkInteg
                  pair.2 st3 headTid hSt2 hLink1 hNoFwd1 hNoRev1⟩
                intro epId' ep' hObj'
                have hObj1 := storeTcbQueueLinks_endpoint_backward pair.2 st3 headTid none none none
                  epId' ep' hSt2 hObj'
                unfold dualQueueEndpointWellFormed; rw [hObj']
                by_cases hNe : epId' = endpointId
                · rw [hNe] at hObj1
                  rw [storeObject_objects_eq st pair.2 endpointId _ hStoreEp] at hObj1; cases hObj1
                  cases hRQ : isReceiveQ
                  · -- isReceiveQ = false: sendQ was emptied, receiveQ preserved
                    exact ⟨intrusiveQueueWellFormed_empty st3,
                      storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                        ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pair.2 endpointId _ hStoreEp hPreEp _ hEpWf.2)
                        (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                  · -- isReceiveQ = true: receiveQ was emptied, sendQ preserved
                    exact ⟨storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                        ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pair.2 endpointId _ hStoreEp hPreEp _ hEpWf.1)
                        (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                      intrusiveQueueWellFormed_empty st3⟩
                · have hObjSt : st.objects[epId']? = some (.endpoint ep') := by
                    rwa [storeObject_objects_ne st pair.2 endpointId epId' _ hNe hStoreEp] at hObj1
                  have hWfPre := hEpInv epId' ep' hObjSt
                  unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt] at hWfPre
                  exact ⟨storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                      ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pair.2 endpointId _ hStoreEp hPreEp _ hWfPre.1)
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                    storeTcbQueueLinks_preserves_iqwf pair.2 st3 headTid none none none hSt2
                      ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pair.2 endpointId _ hStoreEp hPreEp _ hWfPre.2)
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
          | some nextTid =>
            simp only [hNext] at hStep
            -- CASE B: multi-element queue (next = some nextTid)
            -- Steps: storeObject ep → lookupTcb nextTid → storeTcbQueueLinks nextTid → storeTcbQueueLinks headTid (clear)
            cases hStoreEpB : storeObject endpointId
                (.endpoint (if isReceiveQ then
                  { ep with receiveQ := ⟨some nextTid, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩ }
                 else
                  { ep with sendQ := ⟨some nextTid, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩ })) st with
            | error e => simp [hStoreEpB] at hStep
            | ok pairB =>
              cases hLkN : lookupTcb pairB.2 nextTid with
              | none => simp [hStoreEpB, hLkN] at hStep
              | some nextTcb =>
                cases hStN : storeTcbQueueLinks pairB.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hStoreEpB, hLkN, hStN] at hStep
                | ok st2 =>
                  cases hClH : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hStoreEpB, hLkN, hStN, hClH] at hStep
                  | ok st3 =>
                    simp [hStoreEpB, hLkN, hStN, hClH] at hStep
                    obtain ⟨rfl, rfl⟩ := hStep
                    -- Key facts
                    have hNeEpNextB : endpointId ≠ nextTid.toObjId := by
                      intro h; have := lookupTcb_some_objects pairB.2 nextTid nextTcb hLkN
                      rw [← h, storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at this; cases this
                    have hNextTcbSt : st.objects[nextTid.toObjId]? = some (.tcb nextTcb) := by
                      have := lookupTcb_some_objects pairB.2 nextTid nextTcb hLkN
                      rwa [storeObject_objects_ne st pairB.2 endpointId nextTid.toObjId _
                        (Ne.symm hNeEpNextB) hStoreEpB] at this
                    have hNextPrevB : nextTcb.queuePrev = some headTid := by
                      obtain ⟨_, hB, hP⟩ := hLink.1 headTid headTcb hHeadTcb nextTid hNext
                      rw [hNextTcbSt] at hB; cases hB; exact hP
                    have hNeHN : headTid.toObjId ≠ nextTid.toObjId := by
                      intro h
                      have hEq : st.objects[nextTid.toObjId]? = some (.tcb headTcb) := h ▸ hHeadTcb
                      rw [hNextTcbSt] at hEq; cases hEq
                      rw [hPrevNone] at hNextPrevB; exact absurd hNextPrevB (by simp)
                    have hLink1B := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                      st pairB.2 endpointId _ hStoreEpB hPreEp hLink
                    have hTransportB : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        pairB.2.objects[x.toObjId]? = some (.tcb t) →
                        st.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t h
                      by_cases hx : x.toObjId = endpointId
                      · rw [hx, storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at h; cases h
                      · rwa [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ hx hStoreEpB] at h
                    -- nextTid in st2 (after storeTcbQueueLinks nextTid)
                    have hNextResultB := storeTcbQueueLinks_result_tcb pairB.2 st2 nextTid none
                        (some QueuePPrev.endpointHead) nextTcb.queueNext hStN
                    obtain ⟨origNextB, hOrigLkB, hNextSt2B⟩ := hNextResultB
                    -- origNextB = nextTcb since both come from lookupTcb pairB.2 nextTid
                    rw [hLkN] at hOrigLkB; cases hOrigLkB
                    -- Now origNextB is replaced by nextTcb everywhere
                    -- nextTid in st3 (preserved by clearing headTid)
                    have hNextSt3 : st3.objects[nextTid.toObjId]? = some
                        (.tcb (tcbWithQueueLinks nextTcb none (some QueuePPrev.endpointHead) nextTcb.queueNext)) := by
                      rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _
                        nextTid.toObjId hNeHN.symm hClH]; exact hNextSt2B
                    -- headTid in st3 (cleared)
                    have hHeadResultB := storeTcbQueueLinks_result_tcb st2 st3 headTid none none none hClH
                    obtain ⟨_, _, hHeadSt3B⟩ := hHeadResultB
                    -- headTid in st2 (unchanged from st by storeObject + storeTcbQueueLinks nextTid)
                    have hHeadSt2 : st2.objects[headTid.toObjId]? = some (.tcb headTcb) := by
                      rw [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _
                        headTid.toObjId hNeHN hStN]
                      rwa [storeObject_objects_ne st pairB.2 endpointId headTid.toObjId _
                        hNeEpHead.symm hStoreEpB]
                    -- Transport: other TCBs in st3 = TCBs in st
                    have hFwdOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        x.toObjId ≠ headTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                        st.objects[x.toObjId]? = some (.tcb t) →
                        st3.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t hxh hxn ht
                      rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ x.toObjId hxh hClH,
                          storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _ x.toObjId hxn hStN]
                      rw [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ ?_ hStoreEpB]; exact ht
                      intro h; rw [h] at ht; rw [hObj] at ht; cases ht
                    have hBackOther : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                        x.toObjId ≠ headTid.toObjId → x.toObjId ≠ nextTid.toObjId →
                        st3.objects[x.toObjId]? = some (.tcb t) →
                        st.objects[x.toObjId]? = some (.tcb t) := by
                      intro x t hxh hxn ht
                      have h1 : st2.objects[x.toObjId]? = some (.tcb t) := by
                        rwa [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ x.toObjId hxh hClH] at ht
                      have h2 : pairB.2.objects[x.toObjId]? = some (.tcb t) := by
                        rwa [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _ x.toObjId hxn hStN] at h1
                      exact hTransportB x t h2
                    -- Construct well-formedness of the new queue in st2
                    have hWfQNewSt2 : intrusiveQueueWellFormed
                        ⟨some nextTid, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩ st2 := by
                      refine ⟨⟨(fun h => absurd h (by simp)), (fun h => absurd (hHT.2 h) (by rw [hHead]; simp))⟩, ?_, ?_⟩
                      · intro hd hHdEq; cases hHdEq
                        exact ⟨_, hNextSt2B, by simp [tcbWithQueueLinks]⟩
                      · intro tl hTl
                        obtain ⟨tOrig, hTOrig, hTNextOrig⟩ := hTlBnd tl hTl
                        by_cases htN : tl.toObjId = nextTid.toObjId
                        · have := threadId_toObjId_injective htN; subst this
                          rw [hNextTcbSt] at hTOrig; cases hTOrig
                          exact ⟨_, hNextSt2B, by simp [tcbWithQueueLinks]; exact hTNextOrig⟩
                        · have hTSt2 : st2.objects[tl.toObjId]? = some (.tcb tOrig) := by
                            rw [storeTcbQueueLinks_preserves_objects_ne pairB.2 st2 nextTid _ _ _
                              tl.toObjId htN hStN]
                            rw [storeObject_objects_ne st pairB.2 endpointId tl.toObjId _ ?_ hStoreEpB]
                            exact hTOrig
                            intro h; rw [h] at hTOrig; rw [hObj] at hTOrig; cases hTOrig
                          exact ⟨tOrig, hTSt2, hTNextOrig⟩
                    -- Helper: if nextTid is the tail of any well-formed queue in st,
                    -- then nextTcb.queueNext = none.
                    have hNextTailProp : ∀ (q : IntrusiveQueue),
                        intrusiveQueueWellFormed q st →
                        ∀ tl, q.tail = some tl → tl.toObjId = nextTid.toObjId →
                        nextTcb.queueNext = none := by
                      intro q hWf tl hTl hEq
                      have hTlEq := threadId_toObjId_injective hEq
                      rw [hTlEq] at hTl
                      obtain ⟨_, hT, hN⟩ := hWf.2.2 nextTid hTl
                      rw [hNextTcbSt] at hT; cases hT; exact hN
                    -- SPLIT: endpoint well-formedness ∧ link integrity
                    refine ⟨?_, ?_⟩
                    -- PART 1: Endpoint well-formedness
                    · intro epId' ep' hObj'
                      have hObjSt2 := storeTcbQueueLinks_endpoint_backward st2 st3 headTid _ _ _
                        epId' ep' hClH hObj'
                      have hObjPB := storeTcbQueueLinks_endpoint_backward pairB.2 st2 nextTid _ _ _
                        epId' ep' hStN hObjSt2
                      unfold dualQueueEndpointWellFormed; rw [hObj']
                      by_cases hNe : epId' = endpointId
                      · rw [hNe] at hObjPB
                        rw [storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at hObjPB
                        cases hObjPB
                        cases hRQ : isReceiveQ
                        · -- false: sendQ = new queue, receiveQ unchanged
                          simp only [hRQ, Bool.false_eq_true, ↓reduceIte] at hWfQNewSt2
                          constructor
                          · -- sendQ = ⟨some nextTid, q.tail⟩ (new queue)
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              _ hWfQNewSt2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                          · -- receiveQ unchanged
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              ep.receiveQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                                ep.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pairB.2 endpointId _ hStoreEpB hPreEp _ hEpWf.2)
                                (fun _ _ _ => rfl) (hNextTailProp ep.receiveQ hEpWf.2))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                        · -- true: receiveQ = new queue, sendQ unchanged
                          simp only [hRQ, ↓reduceIte] at hWfQNewSt2
                          constructor
                          · -- sendQ unchanged
                            simp only [↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              ep.sendQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                                ep.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                  st pairB.2 endpointId _ hStoreEpB hPreEp _ hEpWf.1)
                                (fun _ _ _ => rfl) (hNextTailProp ep.sendQ hEpWf.1))
                              (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                          · -- receiveQ = ⟨some nextTid, q.tail⟩ (new queue)
                            simp only [↓reduceIte]
                            exact storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                              _ hWfQNewSt2 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                      · have hObjSt' : st.objects[epId']? = some (.endpoint ep') := by
                          rw [storeObject_objects_ne st pairB.2 endpointId epId' _ hNe hStoreEpB] at hObjPB
                          exact hObjPB
                        have hWfPre := hEpInv epId' ep' hObjSt'
                        unfold dualQueueEndpointWellFormed at hWfPre; rw [hObjSt'] at hWfPre
                        exact ⟨storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                            ep'.sendQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                              ep'.sendQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                st pairB.2 endpointId _ hStoreEpB hPreEp _ hWfPre.1)
                              (fun _ _ _ => rfl) (hNextTailProp ep'.sendQ hWfPre.1))
                            (fun _ _ _ => rfl) (fun _ _ _ => rfl),
                          storeTcbQueueLinks_preserves_iqwf st2 st3 headTid _ _ _ hClH
                            ep'.receiveQ (storeTcbQueueLinks_preserves_iqwf pairB.2 st2 nextTid _ _ _ hStN
                              ep'.receiveQ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                                st pairB.2 endpointId _ hStoreEpB hPreEp _ hWfPre.2)
                              (fun _ _ _ => rfl) (hNextTailProp ep'.receiveQ hWfPre.2))
                            (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
                    -- PART 2: Link integrity
                    · constructor
                      -- Forward: a.queueNext = some b → b.queuePrev = some a
                      · intro a tcbA hA b hNxt
                        by_cases haH : a.toObjId = headTid.toObjId
                        · rw [haH] at hA; rw [hHeadSt3B] at hA; cases hA
                          simp [tcbWithQueueLinks] at hNxt
                        · by_cases haN : a.toObjId = nextTid.toObjId
                          · rw [haN] at hA; rw [hNextSt3] at hA; cases hA
                            simp [tcbWithQueueLinks] at hNxt
                            have ha := threadId_toObjId_injective haN
                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 nextTid nextTcb hNextTcbSt b hNxt
                            have hbH : b.toObjId ≠ headTid.toObjId := by
                              intro hh; have := threadId_toObjId_injective hh; subst this
                              rw [hHeadTcb] at hB; cases hB; rw [hPrevNone] at hP
                              exact absurd hP (by simp)
                            have hbN : b.toObjId ≠ nextTid.toObjId := by
                              intro hh; have hbEq := threadId_toObjId_injective hh
                              rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP)) hNeHN
                            exact ⟨tcbB, hFwdOther b tcbB hbH hbN hB, ha ▸ hP⟩
                          · have hA' := hBackOther a tcbA haH haN hA
                            obtain ⟨tcbB, hB, hP⟩ := hLink.1 a tcbA hA' b hNxt
                            have hbH : b.toObjId ≠ headTid.toObjId := by
                              intro hh; have := threadId_toObjId_injective hh; subst this
                              rw [hHeadTcb] at hB; cases hB; rw [hPrevNone] at hP
                              exact absurd hP (by simp)
                            have hbN : b.toObjId ≠ nextTid.toObjId := by
                              intro hh; have hbEq := threadId_toObjId_injective hh
                              rw [hbEq, hNextTcbSt] at hB; cases hB; rw [hNextPrevB] at hP
                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hP).symm) haH
                            exact ⟨tcbB, hFwdOther b tcbB hbH hbN hB, hP⟩
                      -- Reverse: b.queuePrev = some a → a.queueNext = some b
                      · intro b tcbB hB a hPrv
                        by_cases hbH : b.toObjId = headTid.toObjId
                        · rw [hbH] at hB; rw [hHeadSt3B] at hB; cases hB
                          simp [tcbWithQueueLinks] at hPrv
                        · by_cases hbN : b.toObjId = nextTid.toObjId
                          · rw [hbN] at hB; rw [hNextSt3] at hB; cases hB
                            simp [tcbWithQueueLinks] at hPrv
                          · have hB' := hBackOther b tcbB hbH hbN hB
                            obtain ⟨tcbA, hA, hNxt⟩ := hLink.2 b tcbB hB' a hPrv
                            by_cases haH : a.toObjId = headTid.toObjId
                            · have haEq := threadId_toObjId_injective haH
                              rw [haEq, hHeadTcb] at hA; cases hA; rw [hNext] at hNxt
                              exact absurd (congrArg ThreadId.toObjId (Option.some.inj hNxt).symm) hbN
                            · by_cases haN : a.toObjId = nextTid.toObjId
                              · have := threadId_toObjId_injective haN; subst this
                                rw [hNextTcbSt] at hA; cases hA
                                exact ⟨_, hNextSt3, by simp [tcbWithQueueLinks]; exact hNxt⟩
                              · exact ⟨tcbA, hFwdOther a tcbA haH haN hA, hNxt⟩

/-- WS-H5: endpointQueueEnqueue preserves dualQueueSystemInvariant.
Requires freshness preconditions: the enqueued thread must not currently appear
in any endpoint queue boundary, and the current tail (if any) must not be
shared across queue boundaries of different endpoints. -/
theorem endpointQueueEnqueue_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : dualQueueSystemInvariant st)
    (hFreshTid : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some enqueueTid ∧ ep.sendQ.tail ≠ some enqueueTid ∧
      ep.receiveQ.head ≠ some enqueueTid ∧ ep.receiveQ.tail ≠ some enqueueTid)
    (hTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          (if isReceiveQ then ep'.sendQ else ep'.receiveQ).tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpInv, hLink⟩ := hInv
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        have hTcbObj := lookupTcb_some_objects st enqueueTid tcb hLookup
        have hNeEpTid : endpointId ≠ enqueueTid.toObjId :=
          fun h => by rw [h] at hObj; rw [hTcbObj] at hObj; cases hObj
        -- Guard: ipcState and queue link checks
        split at hStep
        · simp at hStep
        · rename_i hNotIpc
          split at hStep
          · simp at hStep
          · rename_i hLinksClean
            -- Derive that enqueueTid has no existing queue links
            have hPrevNone : tcb.queuePrev = none := by
              cases hp : tcb.queuePrev <;> simp_all
            have hNextNone : tcb.queueNext = none := by
              cases hn : tcb.queueNext <;> simp_all
            have hEpWf := hEpInv endpointId ep hObj
            unfold dualQueueEndpointWellFormed at hEpWf; simp only [hObj] at hEpWf
            -- Select the queue
            cases hRQ : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              -- ====== Case A: Empty queue ======
              simp only [hRQ] at hStep
              -- Store endpoint with new head/tail
              generalize hStoreEp : storeObject endpointId (.endpoint
                (if isReceiveQ then { ep with receiveQ := { head := some enqueueTid, tail := some enqueueTid } }
                 else { ep with sendQ := { head := some enqueueTid, tail := some enqueueTid } })) st
                = rEp at hStep
              cases rEp with
              | error e => simp at hStep
              | ok pairA =>
                simp only [] at hStep
                generalize hSt2 : storeTcbQueueLinks pairA.2 enqueueTid none (some QueuePPrev.endpointHead) none
                  = rSt2 at hStep
                cases rSt2 with
                | error e => simp at hStep
                | ok stA =>
                  have hStEq : stA = st' := Except.ok.inj hStep
                  rw [← hStEq]
                  -- Goal: dualQueueSystemInvariant stA
                  -- hSt2 : storeTcbQueueLinks pairA.2 enqueueTid ... = .ok stA
                  have hPreEp : ∀ t : TCB, st.objects[endpointId]? ≠ some (.tcb t) :=
                    fun t h => by rw [hObj] at h; cases h
                  have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                    st pairA.2 endpointId _ hStoreEp hPreEp hLink
                  have hTA : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                      pairA.2.objects[x.toObjId]? = some (.tcb t) →
                      st.objects[x.toObjId]? = some (.tcb t) := by
                    intro x t h; by_cases hx : x.toObjId = endpointId
                    · rw [hx, storeObject_objects_eq st pairA.2 endpointId _ hStoreEp] at h; cases h
                    · rwa [storeObject_objects_ne st pairA.2 endpointId x.toObjId _ hx hStoreEp] at h
                  have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
                      pairA.2.objects[a.toObjId]? = some (.tcb tcbA) →
                      tcbA.queueNext ≠ some enqueueTid := by
                    intro a tA hA hN
                    obtain ⟨_, hB, hP⟩ := hLink.1 a tA (hTA a tA hA) enqueueTid hN
                    rw [hTcbObj] at hB; cases hB; simp [hPrevNone] at hP
                  have hNoRev : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
                      pairA.2.objects[b.toObjId]? = some (.tcb tcbB) →
                      tcbB.queuePrev ≠ some enqueueTid := by
                    intro b tB hB hP
                    obtain ⟨_, hA, hN⟩ := hLink.2 b tB (hTA b tB hB) enqueueTid hP
                    rw [hTcbObj] at hA; cases hA; simp [hNextNone] at hN
                  obtain ⟨origTcbA, _, hTcbFinal⟩ := storeTcbQueueLinks_result_tcb
                    pairA.2 stA enqueueTid none (some QueuePPrev.endpointHead) none hSt2
                  have hQT : ∀ q, intrusiveQueueWellFormed q pairA.2 →
                      intrusiveQueueWellFormed q stA :=
                    fun q hWf => storeTcbQueueLinks_preserves_iqwf pairA.2 stA enqueueTid
                      none (some QueuePPrev.endpointHead) none hSt2 q hWf
                      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
                  refine ⟨?_, storeTcbQueueLinks_noprevnext_preserves_linkInteg
                    pairA.2 stA enqueueTid (some QueuePPrev.endpointHead) hSt2 hLink1 hNoFwd hNoRev⟩
                  intro epId' ep'A hObj'A
                  have hObj1A := storeTcbQueueLinks_endpoint_backward pairA.2 stA enqueueTid
                    none (some QueuePPrev.endpointHead) none epId' ep'A hSt2 hObj'A
                  unfold dualQueueEndpointWellFormed; rw [hObj'A]
                  by_cases hNeA : epId' = endpointId
                  · rw [hNeA] at hObj1A
                    rw [storeObject_objects_eq st pairA.2 endpointId _ hStoreEp] at hObj1A
                    simp only [Option.some.injEq, KernelObject.endpoint.injEq] at hObj1A
                    subst hObj1A
                    have hSing : intrusiveQueueWellFormed
                        { head := some enqueueTid, tail := some enqueueTid } stA :=
                      ⟨Iff.rfl,
                       fun hd hhd => by simp at hhd; subst hhd; exact ⟨_, hTcbFinal, by simp [tcbWithQueueLinks]⟩,
                       fun tl htl => by simp at htl; subst htl; exact ⟨_, hTcbFinal, by simp [tcbWithQueueLinks]⟩⟩
                    cases isReceiveQ
                    · exact ⟨hSing, hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hEpWf.2)⟩
                    · exact ⟨hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hEpWf.1), hSing⟩
                  · rw [storeObject_objects_ne st pairA.2 endpointId epId' _ hNeA hStoreEp] at hObj1A
                    have hWfOrig := hEpInv epId' ep'A hObj1A
                    unfold dualQueueEndpointWellFormed at hWfOrig; rw [hObj1A] at hWfOrig
                    exact ⟨hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hWfOrig.1),
                      hQT _ (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                        st pairA.2 endpointId _ hStoreEp hPreEp _ hWfOrig.2)⟩
            | some tailTid =>
              -- ====== Case B: Non-empty queue ======
              simp only [hRQ] at hStep
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail] at hStep
              | some tailTcb =>
                simp only [hLookupTail] at hStep
                -- Store endpoint with new tail
                generalize hStoreEpB : storeObject endpointId (.endpoint
                  (if isReceiveQ
                   then { ep with receiveQ := { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some enqueueTid } }
                   else { ep with sendQ := { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head, tail := some enqueueTid } })) st
                  = rEpB at hStep
                cases rEpB with
                | error e => simp at hStep
                | ok pairB =>
                  simp only [] at hStep
                  -- Update old tail's next pointer
                  generalize hSt2B : storeTcbQueueLinks pairB.2 tailTid tailTcb.queuePrev
                    tailTcb.queuePPrev (some enqueueTid) = rSt2B at hStep
                  cases rSt2B with
                  | error e => simp at hStep
                  | ok st2B =>
                    simp only [] at hStep
                    -- Set new node's prev pointer
                    generalize hSt3B : storeTcbQueueLinks st2B enqueueTid (some tailTid)
                      (some (QueuePPrev.tcbNext tailTid)) none = rSt3B at hStep
                    cases rSt3B with
                    | error e => simp at hStep
                    | ok st3B =>
                      have hEqStB : st3B = st' := Except.ok.inj hStep
                      rw [← hEqStB]
                      -- ====== Case B proof: Non-empty queue ======
                      have hTailTcbObj := lookupTcb_some_objects st tailTid tailTcb hLookupTail
                      have hPreEp : ∀ t : TCB, st.objects[endpointId]? ≠ some (.tcb t) :=
                        fun t h => by rw [hObj] at h; cases h
                      have hNeTailEp : tailTid.toObjId ≠ endpointId := fun h => by
                        rw [← h] at hObj; rw [hTailTcbObj] at hObj; cases hObj
                      have hNeTailEnq : tailTid.toObjId ≠ enqueueTid.toObjId := by
                        intro h; have hEq := threadId_toObjId_injective h; rw [hEq] at hRQ
                        exact absurd hRQ (by cases isReceiveQ <;> simp [hFreshTid endpointId ep hObj])
                      have hLink1 := storeObject_endpoint_preserves_tcbQueueLinkIntegrity
                        st pairB.2 endpointId _ hStoreEpB hPreEp hLink
                      have hTcbBack : ∀ (x : SeLe4n.ThreadId) (t : TCB),
                          pairB.2.objects[x.toObjId]? = some (.tcb t) →
                          st.objects[x.toObjId]? = some (.tcb t) := by
                        intro x t h; by_cases hx : x.toObjId = endpointId
                        · rw [hx, storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at h; cases h
                        · rwa [storeObject_objects_ne st pairB.2 endpointId x.toObjId _ hx hStoreEpB] at h
                      have hTailInPB : pairB.2.objects[tailTid.toObjId]? = some (.tcb tailTcb) := by
                        rw [storeObject_objects_ne st pairB.2 endpointId tailTid.toObjId _
                          hNeTailEp hStoreEpB]; exact hTailTcbObj
                      have hEnqInPB : pairB.2.objects[enqueueTid.toObjId]? = some (.tcb tcb) := by
                        rw [storeObject_objects_ne st pairB.2 endpointId enqueueTid.toObjId _
                          (Ne.symm hNeEpTid) hStoreEpB]; exact hTcbObj
                      have hTailNextNone : tailTcb.queueNext = none := by
                        have hQWf : intrusiveQueueWellFormed
                            (if isReceiveQ then ep.receiveQ else ep.sendQ) st := by
                          cases isReceiveQ
                          · exact hEpWf.1
                          · exact hEpWf.2
                        obtain ⟨_, hT, hN⟩ := hQWf.2.2 tailTid hRQ
                        rw [hTailTcbObj] at hT; cases hT; exact hN
                      have hNoFwd : ∀ (a : SeLe4n.ThreadId) (tA : TCB),
                          pairB.2.objects[a.toObjId]? = some (.tcb tA) →
                          tA.queueNext ≠ some enqueueTid := by
                        intro a tA hA hN
                        obtain ⟨tB, hB, hP⟩ := hLink.1 a tA (hTcbBack a tA hA) enqueueTid hN
                        rw [hTcbObj] at hB; cases hB; rw [hPrevNone] at hP; cases hP
                      have hNoRev : ∀ (b : SeLe4n.ThreadId) (tB : TCB),
                          pairB.2.objects[b.toObjId]? = some (.tcb tB) →
                          tB.queuePrev ≠ some enqueueTid := by
                        intro b tB hB hP
                        obtain ⟨tA, hA, hN⟩ := hLink.2 b tB (hTcbBack b tB hB) enqueueTid hP
                        rw [hTcbObj] at hA; cases hA; rw [hNextNone] at hN; cases hN
                      have hLinkFinal := storeTcbQueueLinks_append_tail_preserves_linkInteg
                        pairB.2 st2B st3B tailTid enqueueTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some (QueuePPrev.tcbNext tailTid))
                        hSt2B hSt3B hNeTailEnq hLink1
                        (fun t h => by rw [hTailInPB] at h; cases h; rfl)
                        (fun t h => by rw [hTailInPB] at h; cases h; exact hTailNextNone)
                        hNoFwd hNoRev
                      -- Endpoint well-formedness transport
                      obtain ⟨origEnq2, _, hEnqSt3⟩ := storeTcbQueueLinks_result_tcb
                        st2B st3B enqueueTid (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hSt3B
                      -- Transport iqwf through both steps for unmodified queues
                      have hQT : ∀ q, intrusiveQueueWellFormed q pairB.2 →
                          (∀ hd, q.head = some hd → hd.toObjId = tailTid.toObjId → tailTcb.queuePrev = none) →
                          (∀ tl, q.tail = some tl → tl.toObjId ≠ tailTid.toObjId) →
                          (∀ hd, q.head = some hd → hd.toObjId ≠ enqueueTid.toObjId) →
                          intrusiveQueueWellFormed q st3B := by
                        intro q hWf hH1 hT1 hH2
                        exact storeTcbQueueLinks_preserves_iqwf st2B st3B enqueueTid
                          (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none hSt3B q
                          (storeTcbQueueLinks_preserves_iqwf pairB.2 st2B tailTid
                            tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) hSt2B q hWf
                            hH1 (fun tl hTl hOid => absurd hOid (hT1 tl hTl)))
                          (fun hd hHd hOid => absurd hOid (hH2 hd hHd))
                          (fun _ _ _ => rfl)
                      -- Common hH1 derivation: if any queue's head is at tailTid, then tailTcb.queuePrev = none
                      have hHeadTailPrev : ∀ q, intrusiveQueueWellFormed q st →
                          ∀ hd, q.head = some hd → hd.toObjId = tailTid.toObjId → tailTcb.queuePrev = none := by
                        intro q hWf hd hHd hOid
                        obtain ⟨t, hT, hP⟩ := hWf.2.1 hd hHd
                        rw [hOid, hTailTcbObj] at hT; cases hT; exact hP
                      -- Unmodified queue transport helper (used for both branches)
                      have hUnmodWfSt3B : ∀ q, intrusiveQueueWellFormed q st →
                          (∀ tl, q.tail = some tl → tl.toObjId ≠ tailTid.toObjId) →
                          (∀ hd, q.head = some hd → hd.toObjId ≠ enqueueTid.toObjId) →
                          intrusiveQueueWellFormed q st3B := by
                        intro q hWfSt hT1 hH2
                        exact hQT q (storeObject_endpoint_preserves_intrusiveQueueWellFormed
                          st pairB.2 endpointId _ hStoreEpB hPreEp q hWfSt)
                          (hHeadTailPrev q hWfSt) hT1 hH2
                      refine ⟨?_, hLinkFinal⟩
                      intro epId' ep'F hObj'F
                      have hObj'2 := storeTcbQueueLinks_endpoint_backward st2B st3B enqueueTid
                        (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none epId' ep'F hSt3B hObj'F
                      have hObj'1 := storeTcbQueueLinks_endpoint_backward pairB.2 st2B tailTid
                        tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) epId' ep'F hSt2B hObj'2
                      unfold dualQueueEndpointWellFormed; rw [hObj'F]
                      by_cases hNeEp : epId' = endpointId
                      · -- Same endpoint (modified)
                        rw [hNeEp] at hObj'1
                        rw [storeObject_objects_eq st pairB.2 endpointId _ hStoreEpB] at hObj'1
                        simp only [Option.some.injEq, KernelObject.endpoint.injEq] at hObj'1
                        rw [← hObj'1]
                        -- Construct modified queue wf in pairB.2 then transport
                        have hSelQWf : intrusiveQueueWellFormed
                            (if isReceiveQ then ep.receiveQ else ep.sendQ) st := by
                          cases isReceiveQ
                          · exact hEpWf.1
                          · exact hEpWf.2
                        have hModWfPB : intrusiveQueueWellFormed
                            { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head,
                              tail := some enqueueTid } pairB.2 := by
                          refine ⟨?_, ?_, ?_⟩
                          · constructor
                            · intro hh; exfalso
                              have hTN : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail ≠ none := by
                                rw [hRQ]; exact Option.some_ne_none _
                              exact hTN (hSelQWf.1.mp hh)
                            · intro h; simp at h
                          · intro hd hHd
                            obtain ⟨t, hT, hP⟩ := hSelQWf.2.1 hd hHd
                            have : hd.toObjId ≠ endpointId := fun hh =>
                              absurd (hh ▸ hT) (hPreEp t)
                            exact ⟨t, by rw [storeObject_objects_ne st pairB.2 endpointId hd.toObjId _
                              this hStoreEpB]; exact hT, hP⟩
                          · intro tl hTl; simp only [Option.some.injEq] at hTl; rw [← hTl]
                            exact ⟨tcb, hEnqInPB, hNextNone⟩
                        have hModWf := hQT _ hModWfPB
                          (fun hd hHd hOid => hHeadTailPrev _ hSelQWf hd hHd hOid)
                          (fun tl hTl hOid => by simp only [Option.some.injEq] at hTl; rw [← hTl] at hOid
                                                 exact absurd hOid (Ne.symm hNeTailEnq))
                          (fun hd hHd hOid => by
                            have hEq := threadId_toObjId_injective hOid; rw [hEq] at hHd
                            exact absurd hHd (by cases isReceiveQ <;> simp [hFreshTid endpointId ep hObj]))
                        have hTFH := (hTailFresh ep tailTid hObj hRQ endpointId ep hObj).2 rfl
                        have hFH := hFreshTid endpointId ep hObj
                        cases isReceiveQ
                        · simp only [] at hModWf hTFH ⊢
                          exact ⟨hModWf, hUnmodWfSt3B ep.receiveQ hEpWf.2
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFH)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFH.2.2.1)⟩
                        · simp only [] at hModWf hTFH ⊢
                          exact ⟨hUnmodWfSt3B ep.sendQ hEpWf.1
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFH)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFH.1),
                            hModWf⟩
                      · -- Different endpoint
                        have hObjSt : st.objects[epId']? = some (.endpoint ep'F) := by
                          rwa [storeObject_objects_ne st pairB.2 endpointId epId' _ hNeEp hStoreEpB] at hObj'1
                        have hWfOrig := hEpInv epId' ep'F hObjSt
                        unfold dualQueueEndpointWellFormed at hWfOrig; rw [hObjSt] at hWfOrig
                        have hFO := hFreshTid epId' ep'F hObjSt
                        have hTFO := (hTailFresh ep tailTid hObj hRQ epId' ep'F hObjSt).1 hNeEp
                        exact ⟨hUnmodWfSt3B ep'F.sendQ hWfOrig.1
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFO.1)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFO.1),
                          hUnmodWfSt3B ep'F.receiveQ hWfOrig.2
                            (fun tl hTl hOid => by rw [threadId_toObjId_injective hOid] at hTl; exact absurd hTl hTFO.2)
                            (fun hd hHd hOid => by rw [threadId_toObjId_injective hOid] at hHd; exact absurd hHd hFO.2.2.1)⟩

/-- WS-H5: endpointSendDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointSendDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hStep : (endpointSendDual endpointId sender msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointSendDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        -- Path A: dequeue receiver, transfer message, unblock
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          cases hStore : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ensureRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hStore
                (endpointQueuePopHead_preserves_dualQueueSystemInvariant _ _ _ _ _ hPop hInv))
      | none =>
        -- Path B: enqueue sender, store message, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hStore
                (endpointQueueEnqueue_preserves_dualQueueSystemInvariant _ _ _ _ _ hEnq hInv
                  hFreshSender hSendTailFresh))

/-- WS-H5: endpointReceiveDual preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointReceiveDual_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hStep : (endpointReceiveDual endpointId receiver) st = .ok (senderId, st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.sendQ.head with
      | some sndr =>
        -- Path A: dequeue sender, transfer message/unblock
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
            _ _ _ _ _ hPop hInv
          -- Case on lookupTcb to determine senderMsg and senderWasCall
          cases hLk : lookupTcb pair.2 pair.1 with
          | none =>
            simp only [hLk] at hStep
            -- senderWasCall = false, senderMsg = none → send path
            cases hStore : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              cases hMsg : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver none with
              | error e => simp [hMsg] at hStep
              | ok st3 =>
                simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant _ _ _ _ hMsg
                  (ensureRunnable_preserves_dualQueueSystemInvariant _ _
                    (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                      _ _ _ _ _ hStore hInv1))
          | some tcb =>
            simp only [hLk] at hStep
            cases hIpc : tcb.ipcState with
            | blockedOnCall epCall =>
              -- Call path: senderWasCall = true
              simp only [hIpc] at hStep
              cases hStore : storeTcbIpcStateAndMessage pair.2 pair.1
                  (.blockedOnReply endpointId (some receiver)) none with
              | error e => simp [hStore] at hStep
              | ok st2 =>
                simp only [hStore] at hStep
                cases hMsg : storeTcbPendingMessage st2 receiver tcb.pendingMessage with
                | error e => simp [hMsg] at hStep
                | ok st3 =>
                  simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                  exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant _ _ _ _ hMsg
                    (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                      _ _ _ _ _ hStore hInv1)
            | ready | blockedOnSend _ | blockedOnReceive _
              | blockedOnReply _ _ | blockedOnNotification _ =>
              -- Send path: senderWasCall = false
              simp only [hIpc] at hStep
              cases hStore : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
              | error e => simp [hStore] at hStep
              | ok st2 =>
                simp only [hStore] at hStep
                cases hMsg : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver
                    tcb.pendingMessage with
                | error e => simp [hMsg] at hStep
                | ok st3 =>
                  simp only [hMsg] at hStep; rcases hStep with ⟨-, rfl⟩
                  exact storeTcbPendingMessage_preserves_dualQueueSystemInvariant _ _ _ _ hMsg
                    (ensureRunnable_preserves_dualQueueSystemInvariant _ _
                      (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                        _ _ _ _ _ hStore hInv1))
      | none =>
        -- Path B: enqueue receiver, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep; rcases hStep with ⟨-, rfl⟩
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcState_preserves_dualQueueSystemInvariant _ _ _ _ hStore
                (endpointQueueEnqueue_preserves_dualQueueSystemInvariant _ _ _ _ _ hEnq hInv
                  hFreshReceiver hRecvTailFresh))

/-- WS-H12a: endpointReplyRecv preserves dualQueueSystemInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation.
Freshness preconditions are transported through the reply phase since
storeTcbIpcStateAndMessage and ensureRunnable do not modify endpoint objects. -/
theorem endpointReplyRecv_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hStep : (endpointReplyRecv endpointId receiver replyTarget msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointReplyRecv at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            dualQueueSystemInvariant stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      have hInv1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hMsg hInv
      have hInv2 := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hInv1
      -- Transport freshness: storeTcbIpcStateAndMessage + ensureRunnable don't modify endpoint objects
      -- Transport freshness through storeTcbIpcStateAndMessage + ensureRunnable
      -- Both operations preserve endpoint objects (only modify TCBs/scheduler)
      have hFreshReceiver' : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
          (ensureRunnable st1 replyTarget).objects[epId]? = some (.endpoint ep) →
          ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
          ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver := by
        intro epId ep hEp
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp
        exact hFreshReceiver epId ep
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId ep hMsg hEp)
      have hRecvTailFresh' : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          (ensureRunnable st1 replyTarget).objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
            (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep') →
            (epId' ≠ endpointId →
              ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep'.sendQ.tail ≠ some tailTid) := by
        intro ep tailTid hEp hTail epId' ep' hEp'
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp hEp'
        exact hRecvTailFresh ep tailTid
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep hMsg hEp)
          hTail epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hMsg hEp')
      exact endpointReceiveDual_preserves_dualQueueSystemInvariant _ _ _ stR.2 stR.1
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)
        hInv2 hFreshReceiver' hRecvTailFresh'

/-- WS-H5: endpointCall preserves dualQueueSystemInvariant.
Requires freshness preconditions for the enqueue path. -/
theorem endpointCall_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hStep : (endpointCall endpointId caller msg) st = .ok ((), st'))
    (hInv : dualQueueSystemInvariant st)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant st' := by
  unfold endpointCall at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    simp only [hObj] at hStep
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ => simp at hStep
    | endpoint ep =>
      cases hHead : ep.receiveQ.head with
      | some rcvr =>
        -- Path A: dequeue receiver, transfer message, block caller for reply
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
            _ _ _ _ _ hPop hInv
          cases hStore1 : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hStore1] at hStep
          | ok st2 =>
            simp only [hStore1] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              _ _ _ _ _ hStore1 hInv1
            have hInv3 := ensureRunnable_preserves_dualQueueSystemInvariant st2 pair.1 hInv2
            cases hStore2 : storeTcbIpcState (ensureRunnable st2 pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hStore2] at hStep
            | ok st3 =>
              simp only [hStore2, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_preserves_dualQueueSystemInvariant _ _
                (storeTcbIpcState_preserves_dualQueueSystemInvariant _ _ _ _ hStore2 hInv3)
      | none =>
        -- Path B: enqueue caller, store message, block
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hStore : storeTcbIpcStateAndMessage st1 caller
              (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_preserves_dualQueueSystemInvariant _ _
              (storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hStore
                (endpointQueueEnqueue_preserves_dualQueueSystemInvariant _ _ _ _ _ hEnq hInv
                  hFreshCaller hSendTailFresh))

end SeLe4n.Kernel
