import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

/-!
# IPC Invariant Preservation Proofs

WS-E4: Dual-queue endpoint model with separate send/receive queues, pending
messages, and reply queue. The preservation proofs track through the new
multi-path operations: blocking paths (enqueue sender/receiver), handshake
paths (immediate delivery), and reply paths.

WS-E3/H-09: The endpoint operations perform thread IPC state transitions
(blocking/unblocking) in addition to endpoint object updates. The preservation
proofs are genuinely substantive.
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
-- Endpoint well-formedness definitions (WS-E4: dual-queue model)
-- ============================================================================

def endpointQueueWellFormed (ep : Endpoint) : Prop :=
  match ep.state with
  | .idle => ep.sendQueue = [] ∧ ep.receiveQueue = []
  | .send => ep.sendQueue ≠ [] ∧ ep.pendingMessages.length = ep.sendQueue.length
  | .receive => ep.receiveQueue ≠ [] ∧ ep.sendQueue = []

def endpointObjectValid (ep : Endpoint) : Prop :=
  match ep.state with
  | .idle => ep.sendQueue = [] ∧ ep.receiveQueue = []
  | .send => ep.sendQueue ≠ []
  | .receive => ep.receiveQueue ≠ []

def endpointInvariant (ep : Endpoint) : Prop :=
  endpointQueueWellFormed ep ∧ endpointObjectValid ep

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
-- Scheduler-IPC coherence contract predicates (M3.5, WS-E4: +blockedOnReply)
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

theorem endpointObjectValid_of_queueWellFormed
    (ep : Endpoint)
    (hWf : endpointQueueWellFormed ep) :
    endpointObjectValid ep := by
  cases hState : ep.state <;>
    simp [endpointQueueWellFormed, endpointObjectValid, hState] at hWf ⊢
  · exact hWf
  · exact hWf.1
  · exact hWf.1

-- ============================================================================
-- Helper: scheduler unchanged through storeObject + storeTcbIpcState
-- ============================================================================

private theorem scheduler_unchanged_through_store_tcb
    (st st1 st2 : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStore : storeObject oid obj st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    st2.scheduler = st.scheduler := by
  rw [storeTcbIpcState_scheduler_eq st1 st2 tid ipc hTcb,
      storeObject_scheduler_eq st st1 oid obj hStore]

private theorem tcb_preserved_through_endpoint_store
    (st st1 : SystemState) (epId : SeLe4n.ObjId) (obj : KernelObject) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcbExists : st.objects tid.toObjId = some (.tcb tcb))
    (hEndpoint : ∃ ep, st.objects epId = some (.endpoint ep))
    (hStore : storeObject epId obj st = .ok ((), st1)) :
    st1.objects tid.toObjId = some (.tcb tcb) := by
  have hNe : tid.toObjId ≠ epId := by
    rcases hEndpoint with ⟨ep, hObj⟩; intro h; rw [h] at hTcbExists; simp_all
  rwa [storeObject_objects_ne st st1 epId tid.toObjId obj hNe hStore]

-- ============================================================================
-- Blocking path preserves IPC scheduler contracts
-- ============================================================================

private theorem blocking_path_preserves_contracts
    (st st1 st2 : SystemState) (epId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (epNew : Endpoint)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st1))
    (hTcbStep : storeTcbIpcState st1 target ipc = .ok st2)
    (hSchedEq : st2.scheduler = st.scheduler)
    (hReady : runnableThreadIpcReady st)
    (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hBlockReply : blockedOnReplyNotRunnable st) :
    ipcSchedulerContractPredicates (removeRunnable st2 target) := by
  have hRunnableEq := congrArg SchedulerState.runnable hSchedEq
  have deriveNeEp : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st1.objects tid.toObjId = some (.tcb tcb) → tid.toObjId ≠ epId := by
    intro tid tcb hTcbSt1 h; rw [h] at hTcbSt1
    have := storeObject_objects_eq st st1 epId (.endpoint epNew) hStore
    rw [this] at hTcbSt1; exact absurd hTcbSt1 (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tid tcb hTcbPost hRunPost
    have ⟨hRunSt2, hNe⟩ := (removeRunnable_mem st2 target tid).mp hRunPost
    have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
    have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
    have hNeEp := deriveNeEp tid tcb hTcbSt1
    have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
    exact hReady tid tcb hTcbPre (hRunnableEq ▸ hRunSt2)
  · intro tid tcb eid hTcbPost hIpcPost
    by_cases hNe : tid = target
    · subst hNe; exact removeRunnable_not_mem_self st2 _
    · have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      have hRunSt := ((removeRunnable_mem st2 target tid).mp hRunPost).1
      exact hBlockSend tid tcb eid hTcbPre hIpcPost (hRunnableEq ▸ hRunSt)
  · intro tid tcb eid hTcbPost hIpcPost
    by_cases hNe : tid = target
    · subst hNe; exact removeRunnable_not_mem_self st2 _
    · have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      have hRunSt := ((removeRunnable_mem st2 target tid).mp hRunPost).1
      exact hBlockRecv tid tcb eid hTcbPre hIpcPost (hRunnableEq ▸ hRunSt)
  · intro tid tcb eid hTcbPost hIpcPost
    by_cases hNe : tid = target
    · subst hNe; exact removeRunnable_not_mem_self st2 _
    · have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      have hRunSt := ((removeRunnable_mem st2 target tid).mp hRunPost).1
      exact hBlockReply tid tcb eid hTcbPre hIpcPost (hRunnableEq ▸ hRunSt)

-- ============================================================================
-- Handshake path preserves IPC scheduler contracts
-- ============================================================================

private theorem handshake_path_preserves_contracts
    (st st1 st2 : SystemState) (epId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (epNew : Endpoint)
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), st1))
    (hTcbStep : storeTcbIpcState st1 target .ready = .ok st2)
    (hSchedEq : st2.scheduler = st.scheduler)
    (hReady : runnableThreadIpcReady st)
    (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hBlockReply : blockedOnReplyNotRunnable st) :
    ipcSchedulerContractPredicates (ensureRunnable st2 target) := by
  have hRunnableEq := congrArg SchedulerState.runnable hSchedEq
  have deriveNeEp : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st1.objects tid.toObjId = some (.tcb tcb) → tid.toObjId ≠ epId := by
    intro tid tcb hTcbSt1 h; rw [h] at hTcbSt1
    have := storeObject_objects_eq st st1 epId (.endpoint epNew) hStore
    rw [this] at hTcbSt1; exact absurd hTcbSt1 (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tid tcb hTcbPost hRunPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · exact storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost)
    · have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hReady tid tcb hTcbPre (hRunnableEq ▸ hRun)
      · exact absurd hEq hNeTid
  · intro tid tcb eid hTcbPost hIpcPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · have := storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost); simp_all
    · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hBlockSend tid tcb eid hTcbPre hIpcPost (hRunnableEq ▸ hRun)
      · exact absurd hEq hNeTid
  · intro tid tcb eid hTcbPost hIpcPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · have := storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost); simp_all
    · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hBlockRecv tid tcb eid hTcbPre hIpcPost (hRunnableEq ▸ hRun)
      · exact absurd hEq hNeTid
  · intro tid tcb eid hTcbPost hIpcPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · have := storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost); simp_all
    · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 epId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hBlockReply tid tcb eid hTcbPre hIpcPost (hRunnableEq ▸ hRun)
      · exact absurd hEq hNeTid

-- ============================================================================
-- WS-E4: IPC preservation theorems (sorry stubs — TPI-D4)
-- ============================================================================

/-- WS-E4/TPI-D4: endpointSend preserves ipcInvariant. -/
theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ipcInvariant st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointAwaitReceive preserves ipcInvariant. -/
theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × IpcMessage)) (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    ipcInvariant st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointReceive preserves ipcInvariant. -/
theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × IpcMessage) (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    ipcInvariant st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointSend preserves schedulerInvariantBundle. -/
theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointAwaitReceive preserves schedulerInvariantBundle. -/
theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × IpcMessage)) (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    schedulerInvariantBundle st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointReceive preserves schedulerInvariantBundle. -/
theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × IpcMessage) (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    schedulerInvariantBundle st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointSend preserves ipcSchedulerContractPredicates. -/
theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointAwaitReceive preserves ipcSchedulerContractPredicates. -/
theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × IpcMessage))
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    ipcSchedulerContractPredicates st' := by sorry -- TPI-D4

/-- WS-E4/TPI-D4: endpointReceive preserves ipcSchedulerContractPredicates. -/
theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    ipcSchedulerContractPredicates st' := by sorry -- TPI-D4

-- ============================================================================
-- M3.5 step-6: per-predicate decomposition of bundled preservation theorems
-- (WS-E4: updated signatures for dual-queue model + blockedOnReply)
-- ============================================================================

/-- WS-E4/TPI-D4: endpointSend preserves runnableThreadIpcReady. -/
theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).1

/-- WS-E4/TPI-D4: endpointSend preserves blockedOnSendNotRunnable. -/
theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).2.1

/-- WS-E4/TPI-D4: endpointSend preserves blockedOnReceiveNotRunnable. -/
theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).2.2.1

/-- WS-E4/TPI-D4: endpointAwaitReceive preserves runnableThreadIpcReady. -/
theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × IpcMessage))
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    runnableThreadIpcReady st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver result
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).1

/-- WS-E4/TPI-D4: endpointAwaitReceive preserves blockedOnSendNotRunnable. -/
theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × IpcMessage))
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    blockedOnSendNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver result
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).2.1

/-- WS-E4/TPI-D4: endpointAwaitReceive preserves blockedOnReceiveNotRunnable. -/
theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × IpcMessage))
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver result
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).2.2.1

/-- WS-E4/TPI-D4: endpointReceive preserves runnableThreadIpcReady. -/
theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × IpcMessage)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    runnableThreadIpcReady st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId result
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).1

/-- WS-E4/TPI-D4: endpointReceive preserves blockedOnSendNotRunnable. -/
theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × IpcMessage)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    blockedOnSendNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId result
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).2.1

/-- WS-E4/TPI-D4: endpointReceive preserves blockedOnReceiveNotRunnable. -/
theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × IpcMessage)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) (hBlockReply : blockedOnReplyNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId result
    ⟨hReady, hBlockSend, hBlockRecv, hBlockReply⟩ hStep).2.2.1

-- ============================================================================
-- Notification uniqueness (F-12 / WS-D4, WS-E4)
-- ============================================================================

def uniqueWaiters (st : SystemState) : Prop :=
  ∀ oid ntfn, st.objects oid = some (.notification ntfn) → ntfn.waitingThreads.Nodup

/-- WS-E4/TPI-D4: notificationWait preserves uniqueWaiters. -/
theorem notificationWait_preserves_uniqueWaiters
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hInv : uniqueWaiters st)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    uniqueWaiters st' := by sorry -- TPI-D4

