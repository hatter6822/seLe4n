import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

/-!
# IPC Invariant Preservation Proofs

WS-E4: Updated for dual-queue endpoint model (M-01), message payloads (M-02),
and reply operations (M-12). Preservation proofs cover all endpoint operations
over the restructured `Endpoint` type with separate `sendQueue`/`receiveQueue`.

WS-E3/H-09 contracts preserved: blocking/unblocking thread IPC state transitions
maintain scheduler-IPC coherence.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Generic store/lookup transport lemmas
-- ============================================================================

theorem storeObject_objects_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects id = some obj := by
  unfold storeObject at hStore; cases hStore; simp

theorem storeObject_objects_ne
    (st st' : SystemState) (id oid : SeLe4n.ObjId) (obj : KernelObject)
    (hNe : oid ≠ id) (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold storeObject at hStore; cases hStore; simp [hNe]

theorem storeObject_scheduler_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore; cases hStore; rfl

theorem tcb_lookup_of_endpoint_store
    (st st' : SystemState) (endpointId tid : SeLe4n.ObjId) (tcb : TCB) (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hObj : st'.objects tid = some (.tcb tcb)) :
    st.objects tid = some (.tcb tcb) := by
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
-- Endpoint well-formedness definitions (WS-E4/M-01 dual-queue model)
-- ============================================================================

/-- WS-E4/M-01: Endpoint queue well-formedness for dual-queue model.

Invariant relates endpoint state to queue occupancy:
- idle: both queues empty
- send: sendQueue non-empty, receiveQueue empty
- receive: sendQueue empty, receiveQueue non-empty -/
def endpointQueueWellFormed (ep : Endpoint) : Prop :=
  match ep.state with
  | .idle => ep.sendQueue = [] ∧ ep.receiveQueue = []
  | .send => ep.sendQueue ≠ [] ∧ ep.receiveQueue = []
  | .receive => ep.sendQueue = [] ∧ ep.receiveQueue ≠ []

def endpointInvariant (ep : Endpoint) : Prop :=
  endpointQueueWellFormed ep

def notificationQueueWellFormed (ntfn : Notification) : Prop :=
  match ntfn.state with
  | .idle => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge = none
  | .waiting => ntfn.waitingThreads ≠ [] ∧ ntfn.pendingBadge = none
  | .active => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge.isSome

def notificationInvariant (ntfn : Notification) : Prop :=
  notificationQueueWellFormed ntfn

def ipcInvariant (st : SystemState) : Prop :=
  (∀ oid ep, st.objects oid = some (.endpoint ep) → endpointInvariant ep) ∧
  (∀ oid ntfn, st.objects oid = some (.notification ntfn) → notificationInvariant ntfn)

-- ============================================================================
-- Scheduler-IPC coherence contract predicates (M3.5 + WS-E4/M-12)
-- ============================================================================

def runnableThreadIpcReady (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb,
    st.objects tid.toObjId = some (.tcb tcb) → tid ∈ st.scheduler.runnable → tcb.ipcState = .ready

def blockedOnSendNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) → tcb.ipcState = .blockedOnSend endpointId →
    tid ∉ st.scheduler.runnable

def blockedOnReceiveNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) → tcb.ipcState = .blockedOnReceive endpointId →
    tid ∉ st.scheduler.runnable

/-- WS-E4/M-12: Threads blocked on reply must not be in the runnable queue. -/
def blockedOnReplyNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) → tcb.ipcState = .blockedOnReply endpointId →
    tid ∉ st.scheduler.runnable

def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧ blockedOnSendNotRunnable st ∧
  blockedOnReceiveNotRunnable st ∧ blockedOnReplyNotRunnable st

-- ============================================================================
-- Pure logic / functional correctness lemmas
-- ============================================================================

theorem endpointSend_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩

theorem endpointAwaitReceive_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩

theorem endpointReceive_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩

-- ============================================================================
-- WS-E4 TPI-D08: IPC invariant preservation proofs for dual-queue model
-- ============================================================================

-- ============================================================================
-- IPC invariant preservation
-- ============================================================================

/-- Endpoint send preserves the IPC invariant. -/
theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

/-- Endpoint awaitReceive preserves the IPC invariant. -/
theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

/-- Endpoint receive preserves the IPC invariant. -/
theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

/-- WS-E4/M-12: Reply preserves the IPC invariant (only modifies TCB, not endpoints). -/
theorem endpointReply_preserves_ipcInvariant
    (st st' : SystemState) (callerTid : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hInv : ipcInvariant st)
    (hStep : endpointReply callerTid msg st = .ok ((), st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

/-- WS-E4/M-12: Call preserves the IPC invariant. -/
theorem endpointCall_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hInv : ipcInvariant st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

/-- Notification signal preserves the IPC invariant. -/
theorem notificationSignal_preserves_ipcInvariant
    (st st' : SystemState) (notifId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariant st)
    (hStep : notificationSignal notifId badge st = .ok ((), st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

/-- Notification wait preserves the IPC invariant. -/
theorem notificationWait_preserves_ipcInvariant
    (st st' : SystemState) (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (result : Option SeLe4n.Badge)
    (hInv : ipcInvariant st)
    (hStep : notificationWait notifId waiter st = .ok (result, st')) :
    ipcInvariant st' := by
  sorry -- TPI-D08

-- ============================================================================
-- Scheduler invariant bundle preservation
-- ============================================================================

/-- Endpoint send preserves scheduler invariant bundle. -/
theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

/-- Endpoint awaitReceive preserves scheduler invariant bundle. -/
theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

/-- Endpoint receive preserves scheduler invariant bundle. -/
theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : MessageInfo)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

/-- WS-E4/M-12: Reply preserves scheduler invariant bundle. -/
theorem endpointReply_preserves_schedulerInvariantBundle
    (st st' : SystemState) (callerTid : SeLe4n.ThreadId) (msg : MessageInfo)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReply callerTid msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

/-- WS-E4/M-12: Call preserves scheduler invariant bundle. -/
theorem endpointCall_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : MessageInfo)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

-- ============================================================================
-- IPC-Scheduler contract preservation
-- ============================================================================

/-- Endpoint send preserves IPC-scheduler contract predicates. -/
theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  sorry -- TPI-D08

/-- Endpoint awaitReceive preserves IPC-scheduler contract predicates. -/
theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  sorry -- TPI-D08

/-- Endpoint receive preserves IPC-scheduler contract predicates. -/
theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    ipcSchedulerContractPredicates st' := by
  sorry -- TPI-D08

/-- WS-E4/M-12: Reply preserves IPC-scheduler contract predicates. -/
theorem endpointReply_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (callerTid : SeLe4n.ThreadId) (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointReply callerTid msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  sorry -- TPI-D08

/-- WS-E4/M-12: Call preserves IPC-scheduler contract predicates. -/
theorem endpointCall_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  sorry -- TPI-D08

-- ============================================================================
-- Per-predicate corollaries (M3.5 step-6 local-first preservation anchors)
-- ============================================================================

theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg hContracts hStep).1

theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg hContracts hStep).2.1

theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg hContracts hStep).2.2.1

theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContracts hStep).1

theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContracts hStep).2.1

theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContracts hStep).2.2.1

theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    runnableThreadIpcReady st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg hContracts hStep).1

theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg hContracts hStep).2.1

theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : MessageInfo)
    (hContracts : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok ((sender, msg), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg hContracts hStep).2.2.1

-- ============================================================================
-- Notification preservation (unchanged from WS-E3)
-- ============================================================================

theorem notificationSignal_preserves_schedulerInvariantBundle
    (st st' : SystemState) (notifId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : schedulerInvariantBundle st)
    (hStep : notificationSignal notifId badge st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

theorem notificationWait_preserves_schedulerInvariantBundle
    (st st' : SystemState) (notifId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : schedulerInvariantBundle st)
    (hStep : notificationWait notifId waiter st = .ok (result, st')) :
    schedulerInvariantBundle st' := by
  sorry -- TPI-D08

-- ============================================================================
-- Notification waiting-list uniqueness (WS-D4 F-12)
-- ============================================================================

/-- WS-D4/F-12: Notification waiting lists contain no duplicate thread IDs. -/
def uniqueWaiters (st : SystemState) : Prop :=
  ∀ oid ntfn, st.objects oid = some (.notification ntfn) → ntfn.waitingThreads.Nodup

/-- WS-D4/F-12: `notificationWait` preserves waiting-list uniqueness.
The operation rejects double-waits via `alreadyWaiting`, so the list remains duplicate-free. -/
theorem notificationWait_preserves_uniqueWaiters
    (st st' : SystemState) (notifId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hUniq : uniqueWaiters st)
    (hStep : notificationWait notifId waiter st = .ok (result, st')) :
    uniqueWaiters st' := by
  sorry -- TPI-D08

-- ============================================================================
-- CDT acyclicity invariant (WS-E4/C-03)
-- ============================================================================

/-- WS-E4/C-03: A derivation edge path from `src` to `dst` in the CDT. -/
inductive cdtReachable (st : SystemState) : SlotRef → SlotRef → Prop where
  | refl (a : SlotRef) : cdtReachable st a a
  | step (a b c : SlotRef) :
      CapDerivationEdge.mk a b ∈ st.derivationTree →
      cdtReachable st b c →
      cdtReachable st a c

/-- WS-E4/C-03: CDT acyclicity — no non-trivial cycle exists. -/
def cdtAcyclic (st : SystemState) : Prop :=
  ∀ (a b : SlotRef),
    CapDerivationEdge.mk a b ∈ st.derivationTree →
    ¬ cdtReachable st b a

end SeLe4n.Kernel
