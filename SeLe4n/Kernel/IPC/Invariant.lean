import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

/-!
# IPC Invariant Preservation Proofs

WS-E4: Updated for separate send/receive queue endpoint model.
Proofs verify that all endpoint operations preserve queue well-formedness
(at most one queue non-empty) and scheduler-IPC coherence.
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
-- Endpoint well-formedness definitions (WS-E4/M-01)
-- ============================================================================

/-- WS-E4/M-01: At most one queue is non-empty at any time. -/
def endpointQueueWellFormed (ep : Endpoint) : Prop :=
  ep.sendQueue = [] ∨ ep.receiveQueue = []

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

/-- WS-D4/F-12: Notification waiting list has no duplicate entries. -/
def uniqueWaiters (notifId : SeLe4n.ObjId) (st : SystemState) : Prop :=
  match st.objects notifId with
  | some (.notification ntfn) => ntfn.waitingThreads.Nodup
  | _ => True

-- ============================================================================
-- Scheduler-IPC coherence contract predicates (M3.5)
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

def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧ blockedOnSendNotRunnable st ∧ blockedOnReceiveNotRunnable st


-- ============================================================================
-- Pure logic / functional correctness lemmas
-- ============================================================================

theorem endpointSend_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
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
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩

-- ============================================================================
-- Result well-formedness: endpoint at endpointId is well-formed after operation
-- ============================================================================

theorem endpointSend_result_wellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ∀ ep, st.objects endpointId = some (.endpoint ep) → endpointQueueWellFormed ep)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  have hWf := hInv ep hObj
  cases hRecvQ : ep.receiveQueue with
  | cons receiver rest =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId (.endpoint { sendQueue := ep.sendQueue, receiveQueue := rest }) st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver .ready with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]
        intro ⟨_, hEq⟩; subst hEq
        rw [show (ensureRunnable st2 receiver).objects = st2.objects
          from ensureRunnable_preserves_objects st2 receiver]
        have hSendEmpty : ep.sendQueue = [] := by
          cases hWf with
          | inl h => exact h
          | inr h => simp [hRecvQ] at h
        exact ⟨_, storeTcbIpcState_preserves_endpoint pair.2 st2 receiver _ endpointId _
          (storeObject_objects_eq st pair.2 endpointId _ hStore) hTcb,
          Or.inl hSendEmpty⟩
  | nil =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId (.endpoint { sendQueue := ep.sendQueue ++ [sender], receiveQueue := [] }) st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender (.blockedOnSend endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]
        intro ⟨_, hEq⟩; subst hEq
        exact ⟨_, storeTcbIpcState_preserves_endpoint pair.2 st2 sender _ endpointId _
          (storeObject_objects_eq st pair.2 endpointId _ hStore) hTcb,
          by simp [endpointQueueWellFormed]⟩

theorem endpointAwaitReceive_result_wellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hSendQ : ep.sendQueue <;> simp [hSendQ] at hStep
  case nil =>
    revert hStep
    cases hStore : storeObject endpointId (.endpoint { sendQueue := [], receiveQueue := ep.receiveQueue ++ [receiver] }) st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver (.blockedOnReceive endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]
        intro ⟨_, hEq⟩; subst hEq
        exact ⟨_, storeTcbIpcState_preserves_endpoint pair.2 st2 receiver _ endpointId _
          (storeObject_objects_eq st pair.2 endpointId _ hStore) hTcb,
          by simp [endpointQueueWellFormed]⟩

theorem endpointReceive_result_wellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ∀ ep, st.objects endpointId = some (.endpoint ep) → endpointQueueWellFormed ep)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  have hWf := hInv ep hObj
  cases hSendQ : ep.sendQueue with
  | nil => simp [endpointReceive, hObj, hSendQ] at hStep
  | cons hd tl =>
    have hRecvEmpty : ep.receiveQueue = [] := by
      cases hWf with
      | inl h => simp [hSendQ] at h
      | inr h => exact h
    unfold endpointReceive at hStep
    simp only [hObj, hSendQ] at hStep
    revert hStep
    cases hStore : storeObject endpointId (.endpoint { sendQueue := tl, receiveQueue := ep.receiveQueue }) st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 hd .ready with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]
        intro ⟨hSenderEq, hStEq⟩
        subst hStEq; subst hSenderEq
        rw [show (ensureRunnable st2 hd).objects = st2.objects
          from ensureRunnable_preserves_objects st2 hd]
        exact ⟨_, storeTcbIpcState_preserves_endpoint pair.2 st2 hd _ endpointId _
          (storeObject_objects_eq st pair.2 endpointId _ hStore) hTcb,
          Or.inr hRecvEmpty⟩

-- ============================================================================
-- Backward preservation: other endpoints preserved through operations
-- ============================================================================

private theorem endpointSend_preserves_other_endpoint
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ep' : Endpoint) (hObjPost : st'.objects oid = some (.endpoint ep'))
    (hNe : oid ≠ endpointId) :
    st.objects oid = some (.endpoint ep') := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hRecvQ : ep.receiveQueue with
  | cons receiver rest =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver .ready with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.endpoint ep') := by rwa [ensureRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_endpoint_backward pair.2 st2 receiver _ oid ep' hTcb h2
        rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1
  | nil =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender (.blockedOnSend endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.endpoint ep') := by rwa [removeRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_endpoint_backward pair.2 st2 sender _ oid ep' hTcb h2
        rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1

private theorem endpointSend_preserves_notification
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ntfn : Notification) (hObjPost : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hRecvQ : ep.receiveQueue with
  | cons receiver rest =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver .ready with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.notification ntfn) := by rwa [ensureRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_notification_backward pair.2 st2 receiver _ oid ntfn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1
  | nil =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender (.blockedOnSend endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.notification ntfn) := by rwa [removeRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_notification_backward pair.2 st2 sender _ oid ntfn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1

-- ============================================================================
-- IPC Invariant preservation
-- ============================================================================

theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  refine ⟨?_, ?_⟩
  · intro oid ep' hObjPost
    by_cases hEq : oid = endpointId
    · obtain ⟨ep'', hObj', hWf⟩ := endpointSend_result_wellFormed st st' endpointId sender
        (fun ep hEpObj => (hEp endpointId ep hEpObj)) hStep
      rw [hEq] at hObjPost; rw [hObjPost] at hObj'; cases hObj'
      exact hWf
    · exact hEp oid ep' (endpointSend_preserves_other_endpoint st st' endpointId sender hStep oid ep' hObjPost hEq)
  · intro oid ntfn hObjPost
    exact hNtfn oid ntfn (endpointSend_preserves_notification st st' endpointId sender hStep oid ntfn hObjPost)

theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  refine ⟨?_, ?_⟩
  · intro oid ep' hObjPost
    by_cases hEq : oid = endpointId
    · obtain ⟨ep'', hObj', hWf⟩ := endpointAwaitReceive_result_wellFormed st st' endpointId receiver hStep
      rw [hEq] at hObjPost; rw [hObjPost] at hObj'; cases hObj'; exact hWf
    · -- Other endpoints preserved backward
      have hBackward : st.objects oid = some (.endpoint ep') := by
        simp [endpointAwaitReceive, hObj] at hStep
        cases hSendQ : ep.sendQueue <;> simp [hSendQ] at hStep
        case nil =>
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            cases hTcb : storeTcbIpcState pair.2 receiver _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
              have h2 : st2.objects oid = some (.endpoint ep') := by rwa [removeRunnable_preserves_objects] at hObjPost
              have h1 := storeTcbIpcState_endpoint_backward pair.2 st2 receiver _ oid ep' hTcb h2
              rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1
      exact hEp oid ep' hBackward
  · intro oid ntfn hObjPost
    simp [endpointAwaitReceive, hObj] at hStep
    cases hSendQ : ep.sendQueue <;> simp [hSendQ] at hStep
    case nil =>
      revert hStep
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver _ with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
          have h2 : st2.objects oid = some (.notification ntfn) := by rwa [removeRunnable_preserves_objects] at hObjPost
          have h1 := storeTcbIpcState_notification_backward pair.2 st2 receiver _ oid ntfn hTcb h2
          by_cases hEqId : oid = endpointId
          · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
          · rw [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h1
            exact hNtfn oid ntfn h1

private theorem endpointReceive_preserves_other_endpoint
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (ep' : Endpoint) (hObjPost : st'.objects oid = some (.endpoint ep'))
    (hNe : oid ≠ endpointId) :
    st.objects oid = some (.endpoint ep') := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hSendQ : ep.sendQueue with
  | nil => simp [endpointReceive, hObj, hSendQ] at hStep
  | cons hd tl =>
    unfold endpointReceive at hStep; simp only [hObj, hSendQ] at hStep
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 hd _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
        have h2 : st2.objects oid = some (.endpoint ep') := by rwa [ensureRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_endpoint_backward pair.2 st2 hd _ oid ep' hTcb h2
        rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1

private theorem endpointReceive_preserves_notification
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (ntfn : Notification) (hObjPost : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hSendQ : ep.sendQueue with
  | nil => simp [endpointReceive, hObj, hSendQ] at hStep
  | cons hd tl =>
    unfold endpointReceive at hStep; simp only [hObj, hSendQ] at hStep
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 hd _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
        have h2 : st2.objects oid = some (.notification ntfn) := by rwa [ensureRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_notification_backward pair.2 st2 hd _ oid ntfn hTcb h2
        by_cases hEqId : oid = endpointId
        · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h1

theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEp, hNtfn⟩
  refine ⟨?_, ?_⟩
  · intro oid ep' hObjPost
    by_cases hEq : oid = endpointId
    · obtain ⟨ep'', hObj', hWf⟩ := endpointReceive_result_wellFormed st st' endpointId sender
        (fun ep hEpObj => (hEp endpointId ep hEpObj)) hStep
      rw [hEq] at hObjPost; rw [hObjPost] at hObj'; cases hObj'
      exact hWf
    · exact hEp oid ep' (endpointReceive_preserves_other_endpoint st st' endpointId sender hStep oid ep' hObjPost hEq)
  · intro oid ntfn hObjPost
    exact hNtfn oid ntfn (endpointReceive_preserves_notification st st' endpointId sender hStep oid ntfn hObjPost)

-- ============================================================================
-- Scheduler invariant bundle preservation
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
    (hTcbExists : st.objects tid.toObjId = some (.tcb tcb))
    (hEndpoint : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId obj st = .ok ((), st1)) :
    st1.objects tid.toObjId = some (.tcb tcb) := by
  have hNe : tid.toObjId ≠ endpointId := by
    rcases hEndpoint with ⟨ep, hObj⟩; intro h; rw [h] at hTcbExists; simp_all
  rwa [storeObject_objects_ne st st1 endpointId tid.toObjId obj hNe hStore]

theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hRecvQ : ep.receiveQueue with
  | cons receiver rest =>
    -- Handshake path: store endpoint, unblock receiver, ensureRunnable
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver .ready with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st2 endpointId _ receiver _ hStore hTcb
        refine ⟨?_, ?_, ?_⟩
        · -- queueCurrentConsistent
          unfold queueCurrentConsistent
          rw [ensureRunnable_scheduler_current, hSchedEq]
          cases hCurr : st.scheduler.current with
          | none => trivial
          | some x =>
            have hMem : x ∈ st.scheduler.runnable := by
              have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
            exact ensureRunnable_mem_old st2 receiver x (hSchedEq ▸ hMem)
        · exact ensureRunnable_nodup st2 receiver (hSchedEq ▸ hRQU)
        · -- currentThreadValid
          show currentThreadValid (ensureRunnable st2 receiver)
          unfold currentThreadValid
          simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            simp only []
            have hCTV' : ∃ tcb, st.objects x.toObjId = some (.tcb tcb) := by
              simp [currentThreadValid, hCurr] at hCTV; exact hCTV
            rcases hCTV' with ⟨tcb, hTcbObj⟩
            have hNe1 : x.toObjId ≠ endpointId := by intro h; rw [h] at hTcbObj; simp_all
            by_cases hNeTid : x.toObjId = receiver.toObjId
            · have h1 : pair.2.objects receiver.toObjId = some (.tcb tcb) := by
                have := tcb_preserved_through_endpoint_store st pair.2 endpointId _ x tcb hTcbObj ⟨ep, hObj⟩ hStore
                rwa [hNeTid] at this
              have h2 := storeTcbIpcState_tcb_exists_at_target pair.2 st2 receiver _ hTcb ⟨tcb, h1⟩
              rwa [← hNeTid] at h2
            · have hNe2 : x.toObjId ≠ receiver.toObjId := hNeTid
              exact ⟨tcb, by
                rw [storeTcbIpcState_preserves_objects_ne pair.2 st2 receiver _ x.toObjId hNe2 hTcb,
                    storeObject_objects_ne st pair.2 endpointId x.toObjId _ hNe1 hStore]; exact hTcbObj⟩
  | nil =>
    -- Blocking path: store endpoint, block sender, removeRunnable
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender (.blockedOnSend endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st2 endpointId _ sender _ hStore hTcb
        have hCurrEq := congrArg SchedulerState.current hSchedEq
        refine ⟨?_, ?_, ?_⟩
        · -- queueCurrentConsistent
          unfold queueCurrentConsistent
          rw [removeRunnable_scheduler_current, hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            by_cases hEq : x = sender
            · subst hEq; simp
            · rw [if_neg (show ¬(some x = some sender) from fun h => hEq (Option.some.inj h))]
              show x ∈ (removeRunnable st2 sender).scheduler.runnable
              rw [removeRunnable_mem]
              have hMem : x ∈ st.scheduler.runnable := by
                have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
              exact ⟨hSchedEq ▸ hMem, hEq⟩
        · -- runQueueUnique
          exact removeRunnable_nodup st2 sender (hSchedEq ▸ hRQU)
        · -- currentThreadValid
          unfold currentThreadValid
          rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current, hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            by_cases hEq : x = sender
            · subst hEq; simp
            · rw [if_neg (show ¬(some x = some sender) from fun h => hEq (Option.some.inj h))]
              show ∃ tcb, st2.objects x.toObjId = some (.tcb tcb)
              have hCTV' : ∃ tcb, st.objects x.toObjId = some (.tcb tcb) := by
                simp [currentThreadValid, hCurr] at hCTV; exact hCTV
              rcases hCTV' with ⟨tcb, hTcbObj⟩
              have hNe1 : x.toObjId ≠ endpointId := by intro h; rw [h] at hTcbObj; simp_all
              have hNe2 : x.toObjId ≠ sender.toObjId := by
                intro h; exact hEq (threadId_toObjId_injective h)
              exact ⟨tcb, by
                rw [storeTcbIpcState_preserves_objects_ne pair.2 st2 sender _ x.toObjId hNe2 hTcb,
                    storeObject_objects_ne st pair.2 endpointId x.toObjId _ hNe1 hStore]; exact hTcbObj⟩

theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hSendQ : ep.sendQueue <;> simp [hSendQ] at hStep
  case nil =>
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st2 endpointId _ receiver _ hStore hTcb
        have hCurrEq := congrArg SchedulerState.current hSchedEq
        refine ⟨?_, ?_, ?_⟩
        · -- queueCurrentConsistent
          unfold queueCurrentConsistent
          rw [removeRunnable_scheduler_current, hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            by_cases hEq : x = receiver
            · subst hEq; simp
            · rw [if_neg (show ¬(some x = some receiver) from fun h => hEq (Option.some.inj h))]
              show x ∈ (removeRunnable st2 receiver).scheduler.runnable
              rw [removeRunnable_mem]
              have hMem : x ∈ st.scheduler.runnable := by
                have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
              exact ⟨hSchedEq ▸ hMem, hEq⟩
        · exact removeRunnable_nodup st2 receiver (hSchedEq ▸ hRQU)
        · -- currentThreadValid
          unfold currentThreadValid
          rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current, hCurrEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            by_cases hEq : x = receiver
            · subst hEq; simp
            · rw [if_neg (show ¬(some x = some receiver) from fun h => hEq (Option.some.inj h))]
              show ∃ tcb, st2.objects x.toObjId = some (.tcb tcb)
              have hCTV' : ∃ tcb, st.objects x.toObjId = some (.tcb tcb) := by
                simp [currentThreadValid, hCurr] at hCTV; exact hCTV
              rcases hCTV' with ⟨tcb, hTcbObj⟩
              have hNe1 : x.toObjId ≠ endpointId := by intro h; rw [h] at hTcbObj; simp_all
              have hNe2 : x.toObjId ≠ receiver.toObjId := by
                intro h; exact hEq (threadId_toObjId_injective h)
              exact ⟨tcb, by
                rw [storeTcbIpcState_preserves_objects_ne pair.2 st2 receiver _ x.toObjId hNe2 hTcb,
                    storeObject_objects_ne st pair.2 endpointId x.toObjId _ hNe1 hStore]; exact hTcbObj⟩

theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hSendQ : ep.sendQueue with
  | nil => simp [endpointReceive, hObj, hSendQ] at hStep
  | cons hd tl =>
    unfold endpointReceive at hStep; simp only [hObj, hSendQ] at hStep
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 hd _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨hSenderEq, hStEq⟩
        subst hStEq; subst hSenderEq
        have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st2 endpointId _ hd _ hStore hTcb
        refine ⟨?_, ?_, ?_⟩
        · -- queueCurrentConsistent
          unfold queueCurrentConsistent
          rw [ensureRunnable_scheduler_current, hSchedEq]
          cases hCurr : st.scheduler.current with
          | none => trivial
          | some x =>
            have hMem : x ∈ st.scheduler.runnable := by
              have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
            exact ensureRunnable_mem_old st2 hd x (hSchedEq ▸ hMem)
        · exact ensureRunnable_nodup st2 hd (hSchedEq ▸ hRQU)
        · -- currentThreadValid
          show currentThreadValid (ensureRunnable st2 hd)
          unfold currentThreadValid
          simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            simp only []
            have hCTV' : ∃ tcb, st.objects x.toObjId = some (.tcb tcb) := by
              simp [currentThreadValid, hCurr] at hCTV; exact hCTV
            rcases hCTV' with ⟨tcb, hTcbObj⟩
            have hNe1 : x.toObjId ≠ endpointId := by intro h; rw [h] at hTcbObj; simp_all
            by_cases hNeTid : x.toObjId = hd.toObjId
            · have h1 : pair.2.objects hd.toObjId = some (.tcb tcb) := by
                have := tcb_preserved_through_endpoint_store st pair.2 endpointId _ x tcb hTcbObj ⟨ep, hObj⟩ hStore
                rwa [hNeTid] at this
              have h2 := storeTcbIpcState_tcb_exists_at_target pair.2 st2 hd _ hTcb ⟨tcb, h1⟩
              rwa [← hNeTid] at h2
            · have hNe2 : x.toObjId ≠ hd.toObjId := hNeTid
              exact ⟨tcb, by
                rw [storeTcbIpcState_preserves_objects_ne pair.2 st2 hd _ x.toObjId hNe2 hTcb,
                    storeObject_objects_ne st pair.2 endpointId x.toObjId _ hNe1 hStore]; exact hTcbObj⟩

-- ============================================================================
-- CNode backward preservation through endpoint operations
-- ============================================================================

private theorem endpointSend_preserves_cnode
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (cn : CNode) (hObjPost : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hRecvQ : ep.receiveQueue with
  | cons receiver rest =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver .ready with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.cnode cn) := by rwa [ensureRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_cnode_backward pair.2 st2 receiver _ oid cn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1
  | nil =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.cnode cn) := by rwa [removeRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_cnode_backward pair.2 st2 sender _ oid cn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1

private theorem endpointAwaitReceive_preserves_cnode
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (cn : CNode) (hObjPost : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hSendQ : ep.sendQueue <;> simp [hSendQ] at hStep
  case nil =>
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
        have h2 : st2.objects oid = some (.cnode cn) := by rwa [removeRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_cnode_backward pair.2 st2 receiver _ oid cn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1

private theorem endpointReceive_preserves_cnode
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (cn : CNode) (hObjPost : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hSendQ : ep.sendQueue with
  | nil => simp [endpointReceive, hObj, hSendQ] at hStep
  | cons hd tl =>
    unfold endpointReceive at hStep; simp only [hObj, hSendQ] at hStep
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 hd _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩; subst hStEq
        have h2 : st2.objects oid = some (.cnode cn) := by rwa [ensureRunnable_preserves_objects] at hObjPost
        have h1 := storeTcbIpcState_cnode_backward pair.2 st2 hd _ oid cn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1

-- ============================================================================
-- ipcSchedulerContractPredicates preservation helpers
-- ============================================================================

/-- After storeTcbIpcState, the target thread's ipcState matches the requested value. -/
private theorem storeTcbIpcState_target_ipcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (tcb : TCB) (hTcbObj : st'.objects tid.toObjId = some (.tcb tcb)) :
    tcb.ipcState = ipc := by
  unfold storeTcbIpcState at hStep
  cases hLook : lookupTcb st tid with
  | none =>
    simp [hLook] at hStep; subst st'
    unfold lookupTcb at hLook
    cases hObj : st.objects tid.toObjId with
    | none => rw [hObj] at hTcbObj; cases hTcbObj
    | some obj => cases obj <;> simp_all
  | some tcb' =>
    simp only [hLook] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb' with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      have hObjEq := storeObject_objects_eq st pair.2 tid.toObjId
        (.tcb { tcb' with ipcState := ipc }) hStore
      rw [hObjEq] at hTcbObj; cases hTcbObj; rfl

/-- For non-target threads, TCBs are unchanged through endpoint store + storeTcbIpcState. -/
private theorem tcb_through_ep_tcb_chain
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (ipc : ThreadIpcState) (ep' : Endpoint)
    (hEp : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcbObj : st2.objects tid.toObjId = some (.tcb tcb))
    (hNe : tid.toObjId ≠ target.toObjId) :
    st.objects tid.toObjId = some (.tcb tcb) := by
  have h1 := storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNe hTcb
  rw [h1] at hTcbObj
  have hNe2 : tid.toObjId ≠ endpointId := by
    intro h; rcases hEp with ⟨ep, hEpObj⟩
    rw [h, storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore] at hTcbObj
    cases hTcbObj
  rwa [storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint ep') hNe2 hStore] at hTcbObj

-- ============================================================================
-- ipcSchedulerContractPredicates preservation: handshake chain
-- ============================================================================

/-- Contract predicates preserved through handshake chain:
    storeObject (endpoint) → storeTcbIpcState (target → .ready) → ensureRunnable (target). -/
private theorem ipcSchedulerContractPredicates_of_handshake
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId) (ep' : Endpoint)
    (hContract : ipcSchedulerContractPredicates st)
    (hEp : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target .ready = .ok st2) :
    ipcSchedulerContractPredicates (ensureRunnable st2 target) := by
  rcases hContract with ⟨hReady, hBlkSend, hBlkRecv⟩
  have hSchedEq := scheduler_unchanged_through_store_tcb st st1 st2 endpointId
    (.endpoint ep') target .ready hStore hTcb
  refine ⟨?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid tcb hTcbObj hRun
    rw [ensureRunnable_preserves_objects] at hTcbObj
    rcases ensureRunnable_mem_reverse st2 target tid hRun with hOld | rfl
    · rw [hSchedEq] at hOld
      by_cases hEq : tid.toObjId = target.toObjId
      · exact storeTcbIpcState_target_ipcState st1 st2 target .ready hTcb tcb (hEq ▸ hTcbObj)
      · exact hReady tid tcb
          (tcb_through_ep_tcb_chain st st1 st2 endpointId target .ready ep' hEp hStore hTcb
            tid tcb hTcbObj hEq) hOld
    · exact storeTcbIpcState_target_ipcState st1 st2 tid .ready hTcb tcb hTcbObj
  · -- blockedOnSendNotRunnable
    intro tid tcb epId hTcbObj hIpc hRun
    rw [ensureRunnable_preserves_objects] at hTcbObj
    rcases ensureRunnable_mem_reverse st2 target tid hRun with hOld | rfl
    · rw [hSchedEq] at hOld
      have hNeObj : tid.toObjId ≠ target.toObjId := by
        intro h; have := storeTcbIpcState_target_ipcState st1 st2 target .ready hTcb tcb (h ▸ hTcbObj)
        rw [this] at hIpc; cases hIpc
      exact absurd hOld (hBlkSend tid tcb epId
        (tcb_through_ep_tcb_chain st st1 st2 endpointId target .ready ep' hEp hStore hTcb
          tid tcb hTcbObj hNeObj) hIpc)
    · have := storeTcbIpcState_target_ipcState st1 st2 tid .ready hTcb tcb hTcbObj
      rw [this] at hIpc; cases hIpc
  · -- blockedOnReceiveNotRunnable
    intro tid tcb epId hTcbObj hIpc hRun
    rw [ensureRunnable_preserves_objects] at hTcbObj
    rcases ensureRunnable_mem_reverse st2 target tid hRun with hOld | rfl
    · rw [hSchedEq] at hOld
      have hNeObj : tid.toObjId ≠ target.toObjId := by
        intro h; have := storeTcbIpcState_target_ipcState st1 st2 target .ready hTcb tcb (h ▸ hTcbObj)
        rw [this] at hIpc; cases hIpc
      exact absurd hOld (hBlkRecv tid tcb epId
        (tcb_through_ep_tcb_chain st st1 st2 endpointId target .ready ep' hEp hStore hTcb
          tid tcb hTcbObj hNeObj) hIpc)
    · have := storeTcbIpcState_target_ipcState st1 st2 tid .ready hTcb tcb hTcbObj
      rw [this] at hIpc; cases hIpc

-- ============================================================================
-- ipcSchedulerContractPredicates preservation: blocking chain
-- ============================================================================

/-- Contract predicates preserved through blocking chain:
    storeObject (endpoint) → storeTcbIpcState (tid → ipc) → removeRunnable (tid). -/
private theorem ipcSchedulerContractPredicates_of_blocking
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (ep' : Endpoint)
    (hContract : ipcSchedulerContractPredicates st)
    (hEp : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    ipcSchedulerContractPredicates (removeRunnable st2 tid) := by
  rcases hContract with ⟨hReady, hBlkSend, hBlkRecv⟩
  have hSchedEq := scheduler_unchanged_through_store_tcb st st1 st2 endpointId
    (.endpoint ep') tid ipc hStore hTcb
  refine ⟨?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid' tcb hTcbObj hRun
    rw [removeRunnable_preserves_objects] at hTcbObj
    have ⟨hOld, hNe⟩ := (removeRunnable_mem st2 tid tid').mp hRun
    rw [hSchedEq] at hOld
    have hNeObj : tid'.toObjId ≠ tid.toObjId :=
      fun h => hNe (ThreadId.toObjId_injective tid' tid h)
    exact hReady tid' tcb
      (tcb_through_ep_tcb_chain st st1 st2 endpointId tid ipc ep' hEp hStore hTcb
        tid' tcb hTcbObj hNeObj) hOld
  · -- blockedOnSendNotRunnable
    intro tid' tcb epId hTcbObj hIpc hRun
    rw [removeRunnable_preserves_objects] at hTcbObj
    have ⟨hOld, hNe⟩ := (removeRunnable_mem st2 tid tid').mp hRun
    rw [hSchedEq] at hOld
    have hNeObj : tid'.toObjId ≠ tid.toObjId :=
      fun h => hNe (ThreadId.toObjId_injective tid' tid h)
    exact absurd hOld (hBlkSend tid' tcb epId
      (tcb_through_ep_tcb_chain st st1 st2 endpointId tid ipc ep' hEp hStore hTcb
        tid' tcb hTcbObj hNeObj) hIpc)
  · -- blockedOnReceiveNotRunnable
    intro tid' tcb epId hTcbObj hIpc hRun
    rw [removeRunnable_preserves_objects] at hTcbObj
    have ⟨hOld, hNe⟩ := (removeRunnable_mem st2 tid tid').mp hRun
    rw [hSchedEq] at hOld
    have hNeObj : tid'.toObjId ≠ tid.toObjId :=
      fun h => hNe (ThreadId.toObjId_injective tid' tid h)
    exact absurd hOld (hBlkRecv tid' tcb epId
      (tcb_through_ep_tcb_chain st st1 st2 endpointId tid ipc ep' hEp hStore hTcb
        tid' tcb hTcbObj hNeObj) hIpc)

-- ============================================================================
-- uniqueWaiters preservation
-- ============================================================================

/-- After storeObject stores a notification at `notifId`, a subsequent
`storeTcbIpcState` on `waiter` preserves that notification, because either
`waiter.toObjId ≠ notifId` (different slot) or `lookupTcb` returns `none`
(the object at `notifId` is a notification, not a TCB). -/
private theorem notification_survives_storeTcbIpcState
    (st stMid stTcb : SystemState) (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (ntfn' : Notification)
    (hStore : storeObject notifId (.notification ntfn') st = .ok ((), stMid))
    (hTcb : storeTcbIpcState stMid waiter ipc = .ok stTcb) :
    stTcb.objects notifId = some (.notification ntfn') := by
  have hObjMid := storeObject_objects_eq st stMid notifId (.notification ntfn') hStore
  by_cases hEq : waiter.toObjId = notifId
  · -- waiter.toObjId = notifId: lookupTcb finds notification (not TCB), returns none → st unchanged
    unfold storeTcbIpcState at hTcb
    unfold lookupTcb at hTcb
    rw [hEq, hObjMid] at hTcb
    simp at hTcb; subst hTcb; exact hObjMid
  · -- waiter.toObjId ≠ notifId: storeTcbIpcState doesn't touch notifId
    rw [storeTcbIpcState_preserves_objects_ne stMid stTcb waiter ipc notifId (Ne.symm hEq) hTcb]
    exact hObjMid

theorem notificationWait_preserves_uniqueWaiters
    (st st' : SystemState) (notifId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hUniq : uniqueWaiters notifId st)
    (hStep : notificationWait notifId waiter st = .ok (badge, st')) :
    uniqueWaiters notifId st' := by
  unfold uniqueWaiters
  unfold notificationWait at hStep
  cases hObj : st.objects notifId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | cnode _ | vspaceRoot _ => simp [hObj] at hStep
    | notification ntfn =>
      simp [hObj] at hStep
      unfold uniqueWaiters at hUniq; simp [hObj] at hUniq
      cases hBadge : ntfn.pendingBadge with
      | some b =>
        -- Badge path: resets notification to idle with empty waitingThreads
        simp [hBadge] at hStep; revert hStep
        cases hStore : storeObject notifId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            have hNtfn := notification_survives_storeTcbIpcState st pair.2 st2 notifId waiter _
              { state := .idle, waitingThreads := [], pendingBadge := none } hStore hTcb
            rw [hNtfn]; exact List.Pairwise.nil
      | none =>
        -- Wait path: appends waiter to waitingThreads (after duplicate check)
        simp [hBadge] at hStep
        split at hStep
        case isTrue hMem => simp at hStep
        case isFalse hNotMem =>
          revert hStep
          cases hStore : storeObject notifId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            cases hTcb : storeTcbIpcState pair.2 waiter _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
              have hNtfn := notification_survives_storeTcbIpcState st pair.2 st2 notifId waiter _
                { state := .waiting, waitingThreads := ntfn.waitingThreads ++ [waiter], pendingBadge := none } hStore hTcb
              rw [removeRunnable_preserves_objects, hNtfn]
              refine List.nodup_append.mpr ⟨hUniq, ?_, ?_⟩
              · exact List.nodup_cons.mpr ⟨by simp, List.Pairwise.nil⟩
              · intro a hA b hB; simp at hB; subst hB; exact fun h => hNotMem (h ▸ hA)

-- ============================================================================
-- ipcSchedulerContractPredicates preservation: per-operation
-- ============================================================================

theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hRecvQ : ep.receiveQueue with
  | cons receiver rest =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        exact ipcSchedulerContractPredicates_of_handshake st pair.2 st2 endpointId receiver _
          hContract ⟨ep, hObj⟩ hStore hTcb
  | nil =>
    simp [endpointSend, hObj, hRecvQ] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        exact ipcSchedulerContractPredicates_of_blocking st pair.2 st2 endpointId sender _ _
          hContract ⟨ep, hObj⟩ hStore hTcb

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hSendQ : ep.sendQueue <;> simp [hSendQ] at hStep
  case nil =>
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 receiver _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        exact ipcSchedulerContractPredicates_of_blocking st pair.2 st2 endpointId receiver _ _
          hContract ⟨ep, hObj⟩ hStore hTcb

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hSendQ : ep.sendQueue with
  | nil => simp [endpointReceive, hObj, hSendQ] at hStep
  | cons hd tl =>
    unfold endpointReceive at hStep; simp only [hObj, hSendQ] at hStep
    revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 hd _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨hSenderEq, hStEq⟩
        subst hStEq; subst hSenderEq
        exact ipcSchedulerContractPredicates_of_handshake st pair.2 st2 endpointId hd _
          hContract ⟨ep, hObj⟩ hStore hTcb

-- ============================================================================
-- M3.5 step-6 local-first preservation theorems (individual predicate level)
-- ============================================================================

theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep).1

theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep).2.1

theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep).2.2

theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContract hStep).1

theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContract hStep).2.1

theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContract hStep).2.2

theorem endpointReceive_preserves_runnableThreadIpcReady
    (st : SystemState) (st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep).1

theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st : SystemState) (st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep).2.1

theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st : SystemState) (st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep).2.2

end SeLe4n.Kernel
