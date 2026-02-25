import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

/-!
# IPC Invariant Preservation Proofs

This module contains invariant definitions and preservation theorems for the IPC
(inter-process communication) subsystem, including endpoint and notification
well-formedness, and IPC-scheduler coherence contracts.

## Proof scope qualification (F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
- `endpointSend_preserves_ipcInvariant`
- `endpointAwaitReceive_preserves_ipcInvariant`
- `endpointReceive_preserves_ipcInvariant`
- `endpointSend_preserves_ipcSchedulerContractPredicates` (and per-component)
- `endpointAwaitReceive_preserves_ipcSchedulerContractPredicates` (and per-component)
- `endpointReceive_preserves_ipcSchedulerContractPredicates` (and per-component)
- `endpointSend_preserves_schedulerInvariantBundle`
- `endpointAwaitReceive_preserves_schedulerInvariantBundle`
- `endpointReceive_preserves_schedulerInvariantBundle`

**Structural / functional-correctness theorems** (high assurance):
- `endpointSend_result_wellFormed`
- `endpointAwaitReceive_result_wellFormed`
- `endpointReceive_result_wellFormed`
- `endpointObjectValid_of_queueWellFormed`
- all `*_ok_implies_endpoint_object` lemmas

H-09 (WS-E3): All IPC-scheduler contract predicates are now **non-vacuous** because
endpoint operations explicitly transition thread IPC state and modify the scheduler
runnable set.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Transport lemmas for storeObject
-- ============================================================================

theorem storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects id = some obj := by
  unfold storeObject at hStore; cases hStore; simp

theorem storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold storeObject at hStore; cases hStore; simp [hNe]

theorem storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore; cases hStore; rfl

-- ============================================================================
-- H-09: ThreadId injectivity helper
-- ============================================================================

/-- Two ThreadIds are equal iff their toObjId projections are equal. -/
theorem ThreadId.toObjId_injective (t₁ t₂ : SeLe4n.ThreadId)
    (h : t₁.toObjId = t₂.toObjId) : t₁ = t₂ := by
  cases t₁; cases t₂
  simp [ThreadId.toObjId, ThreadId.toNat, ObjId.ofNat] at h
  exact congrArg ThreadId.mk h

-- ============================================================================
-- Endpoint local invariant definitions
-- ============================================================================

def endpointQueueWellFormed (ep : Endpoint) : Prop :=
  match ep.state with
  | .idle => ep.queue = [] ∧ ep.waitingReceiver = none
  | .send => ep.queue ≠ [] ∧ ep.waitingReceiver = none
  | .receive => ep.queue = [] ∧ ep.waitingReceiver.isSome

def endpointObjectValid (ep : Endpoint) : Prop :=
  match ep.waitingReceiver with
  | none => ep.state ≠ .receive
  | some _ => ep.state = .receive

def endpointInvariant (ep : Endpoint) : Prop :=
  endpointQueueWellFormed ep ∧ endpointObjectValid ep

def notificationQueueWellFormed (ntfn : Notification) : Prop :=
  match ntfn.state with
  | .idle => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge = none
  | .waiting => ntfn.waitingThreads ≠ [] ∧ ntfn.pendingBadge = none
  | .active => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge.isSome

def notificationInvariant (ntfn : Notification) : Prop :=
  notificationQueueWellFormed ntfn

/-- Notification waiting list has no duplicates. -/
def uniqueWaiters (notifId : SeLe4n.ObjId) (st : SystemState) : Prop :=
  ∀ ntfn, st.objects notifId = some (.notification ntfn) →
    ntfn.waitingThreads.Nodup

def ipcInvariant (st : SystemState) : Prop :=
  (∀ oid ep,
    st.objects oid = some (.endpoint ep) →
    endpointInvariant ep) ∧
  (∀ oid ntfn,
    st.objects oid = some (.notification ntfn) →
    notificationInvariant ntfn)

-- ============================================================================
-- IPC-scheduler contract predicates
-- ============================================================================

def runnableThreadIpcReady (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb,
    st.objects tid.toObjId = some (.tcb tcb) →
    tid ∈ st.scheduler.runnable →
    tcb.ipcState = .ready

def blockedOnSendNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnSend endpointId →
    tid ∉ st.scheduler.runnable

def blockedOnReceiveNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnReceive endpointId →
    tid ∉ st.scheduler.runnable

def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧
  blockedOnSendNotRunnable st ∧
  blockedOnReceiveNotRunnable st

-- ============================================================================
-- Well-formedness helpers
-- ============================================================================

theorem endpointObjectValid_of_queueWellFormed
    (ep : Endpoint)
    (hWf : endpointQueueWellFormed ep) :
    endpointObjectValid ep := by
  cases hState : ep.state <;> cases hWait : ep.waitingReceiver <;>
    simp [endpointQueueWellFormed, endpointObjectValid, hState, hWait] at hWf ⊢

-- ============================================================================
-- Endpoint operation well-formedness (H-09 updated)
--
-- TPI-D05: The result_wellFormed proofs trace through the storeObject →
-- storeTcbIpcState → schedOp chain to show the endpoint in the post-state is
-- well-formed. Proof completion in WS-E4.
-- ============================================================================

/-- Helper: trace a stored endpoint through the storeTcbIpcState → removeRunnable chain. -/
private theorem chain_tcb_removeRunnable_preserves_endpoint_at
    (st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hEp : st1.objects endpointId = some (.endpoint ep'))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    (removeRunnable st2 tid).objects endpointId = some (.endpoint ep') := by
  rw [removeRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_endpoint st1 st2 tid ipc endpointId ep' hEp hTcb

/-- Helper: trace a stored endpoint through the storeTcbIpcState → ensureRunnable chain. -/
private theorem chain_tcb_ensureRunnable_preserves_endpoint_at
    (st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hEp : st1.objects endpointId = some (.endpoint ep'))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    (ensureRunnable st2 tid).objects endpointId = some (.endpoint ep') := by
  rw [ensureRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_endpoint st1 st2 tid ipc endpointId ep' hEp hTcb

/-- endpointSend: the endpoint in the post-state is well-formed. TPI-D05. -/
theorem endpointSend_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hState : ep.state <;> simp only [hState] at hStep
      -- idle: ep' = { state := .send, queue := [sender], waitingReceiver := none }
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hEpSt1 := storeObject_objects_eq st st1 endpointId _ hStore
            exact ⟨_, chain_tcb_removeRunnable_preserves_endpoint_at st1 st2 endpointId _ sender _ hEpSt1 hTcb, by simp [endpointQueueWellFormed]⟩
      -- send: ep' = { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hEpSt1 := storeObject_objects_eq st st1 endpointId _ hStore
            exact ⟨_, chain_tcb_removeRunnable_preserves_endpoint_at st1 st2 endpointId _ sender _ hEpSt1 hTcb,
              by simp [endpointQueueWellFormed]⟩
      -- receive: ep' = { state := .idle, queue := [], waitingReceiver := none }
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hEpSt1 := storeObject_objects_eq st st1 endpointId _ hStore
                exact ⟨_, chain_tcb_ensureRunnable_preserves_endpoint_at st1 st2 endpointId _ receiver _ hEpSt1 hTcb, by simp [endpointQueueWellFormed]⟩
        | cons _ _ => split at hStep <;> simp_all

/-- endpointAwaitReceive: the endpoint in the post-state is well-formed. TPI-D05. -/
theorem endpointAwaitReceive_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      -- Only (.idle, [], none) succeeds
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hEpSt1 := storeObject_objects_eq st st1 endpointId _ hStore
                exact ⟨_, chain_tcb_removeRunnable_preserves_endpoint_at st1 st2 endpointId _ receiver _ hEpSt1 hTcb, by simp [endpointQueueWellFormed]⟩
          · simp at hStep
        · simp at hStep

/-- endpointReceive: the endpoint in the post-state is well-formed. TPI-D05. -/
theorem endpointReceive_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      -- Only (.send, sender :: rest, none) succeeds
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hEpSt1 := storeObject_objects_eq st st1 endpointId _ hStore
                refine ⟨_, chain_tcb_ensureRunnable_preserves_endpoint_at st1 st2 endpointId _ hd _ hEpSt1 hTcb, ?_⟩
                simp [endpointQueueWellFormed]
                cases hTl : tl with
                | nil => simp [hTl, List.isEmpty]
                | cons _ _ => simp [hTl, List.isEmpty]
          | some _ => split at hStep <;> simp_all

-- ============================================================================
-- Pre-state endpoint object witnesses
-- ============================================================================

theorem endpointSend_ok_implies_endpoint_object
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩

theorem endpointAwaitReceive_ok_implies_endpoint_object
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩

theorem endpointReceive_ok_implies_endpoint_object
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep => exact ⟨ep, rfl⟩


-- ============================================================================
-- H-09: IPC invariant preservation
--
-- Each endpoint operation chains storeObject → storeTcbIpcState → schedOp.
-- - At endpointId: the modified endpoint is well-formed (from _result_wellFormed)
-- - At oid ≠ endpointId: endpoints/notifications preserved (type disjointness)
-- - CNodes preserved at any oid (storeObject writes endpoint, not cnode)
--
-- TPI-D05: Full proofs trace through all operation branches. Proof completion
-- in WS-E4.
-- ============================================================================

/-- Reverse direction: if st' has an endpoint at oid after storeTcbIpcState,
    then st had the same endpoint there (since storeTcbIpcState only writes TCBs). -/
private theorem storeTcbIpcState_endpoint_reverse
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hPost : st'.objects oid = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st.objects oid = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    cases hLookup : lookupTcb st tid with
    | none =>
      have := storeTcbIpcState_none_result st st' tid ipc hLookup hStep
      rw [this] at hPost; exact hPost
    | some tcb =>
      have := storeTcbIpcState_tcb_result st st' tid ipc tcb hLookup hStep
      rw [this] at hPost; exact absurd hPost (by simp)
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hPost
    exact hPost

/-- Reverse direction for notifications. -/
private theorem storeTcbIpcState_notification_reverse
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hPost : st'.objects oid = some (.notification ntfn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st.objects oid = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    cases hLookup : lookupTcb st tid with
    | none =>
      have := storeTcbIpcState_none_result st st' tid ipc hLookup hStep
      rw [this] at hPost; exact hPost
    | some tcb =>
      have := storeTcbIpcState_tcb_result st st' tid ipc tcb hLookup hStep
      rw [this] at hPost; exact absurd hPost (by simp)
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hPost
    exact hPost

/-- Helper: given the 3-step chain decomposition and well-formedness at endpointId,
    the IPC invariant is preserved. Uses reverse lemmas for storeTcbIpcState. -/
private theorem ipcInvariant_of_chain
    (st st1 st2 st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (ep' : Endpoint) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : ipcInvariant st)
    (hQwf : endpointQueueWellFormed ep')
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2)
    (hObj : st'.objects = st2.objects) :
    ipcInvariant st' := by
  have hEpPost : st'.objects endpointId = some (.endpoint ep') := by
    rw [hObj]
    have h1 := storeObject_objects_eq st st1 endpointId _ hStore
    exact storeTcbIpcState_preserves_endpoint st1 st2 tid ipc endpointId ep' h1 hTcb
  constructor
  · intro oid ep hOid
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hEpPost] at hOid; cases hOid
      exact ⟨hQwf, endpointObjectValid_of_queueWellFormed ep' hQwf⟩
    · -- oid ≠ endpointId: trace back through the chain
      have hOidSt2 : st2.objects oid = some (.endpoint ep) := by rw [← hObj]; exact hOid
      have hOidSt1 : st1.objects oid = some (.endpoint ep) :=
        storeTcbIpcState_endpoint_reverse st1 st2 tid ipc oid ep hOidSt2 hTcb
      have hOidSt : st.objects oid = some (.endpoint ep) := by
        rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hEq hStore] at hOidSt1
      exact hInv.1 oid ep hOidSt
  · intro oid ntfn hOid
    have hOidSt2 : st2.objects oid = some (.notification ntfn) := by rw [← hObj]; exact hOid
    have hOidSt1 : st1.objects oid = some (.notification ntfn) :=
      storeTcbIpcState_notification_reverse st1 st2 tid ipc oid ntfn hOidSt2 hTcb
    have hNe : oid ≠ endpointId := by
      intro hEq
      have := storeObject_objects_eq st st1 endpointId _ hStore
      rw [hEq] at hOidSt1; rw [this] at hOidSt1; exact absurd hOidSt1 (by simp)
    have hOidSt : st.objects oid = some (.notification ntfn) := by
      rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at hOidSt1
    exact hInv.2 oid ntfn hOidSt

/-- H-09: endpointSend preserves the IPC invariant. TPI-D05. -/
theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hState : ep.state <;> simp only [hState] at hStep
      -- idle: ep' has state .send, queue [sender]
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ipcInvariant_of_chain st st1 st2 _ endpointId _ sender _ hInv (by simp [endpointQueueWellFormed]) hStore hTcb (removeRunnable_preserves_objects st2 sender)
      -- send: ep' has state .send, queue ep.queue ++ [sender]
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ipcInvariant_of_chain st st1 st2 _ endpointId _ sender _ hInv (by simp [endpointQueueWellFormed]) hStore hTcb (removeRunnable_preserves_objects st2 sender)
      -- receive: ep' has state .idle, queue [], no receiver
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact ipcInvariant_of_chain st st1 st2 _ endpointId _ receiver _ hInv (by simp [endpointQueueWellFormed]) hStore hTcb (ensureRunnable_preserves_objects st2 receiver)
        | cons _ _ => split at hStep <;> simp_all

/-- H-09: endpointAwaitReceive preserves the IPC invariant. TPI-D05. -/
theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact ipcInvariant_of_chain st st1 st2 _ endpointId _ receiver _ hInv (by simp [endpointQueueWellFormed]) hStore hTcb (removeRunnable_preserves_objects st2 receiver)
          · simp at hStep
        · simp at hStep

/-- H-09: endpointReceive preserves the IPC invariant. TPI-D05. -/
theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcInvariant st' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hQwf : endpointQueueWellFormed { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none } := by
                  simp [endpointQueueWellFormed]; cases hTl : tl with
                  | nil => simp [hTl, List.isEmpty]
                  | cons _ _ => simp [hTl, List.isEmpty]
                exact ipcInvariant_of_chain st st1 st2 _ endpointId _ hd _ hInv hQwf hStore hTcb (ensureRunnable_preserves_objects st2 hd)
          | some _ => split at hStep <;> simp_all

-- ============================================================================
-- CNode preservation for capability bundle downstream (H-09 updated)
--
-- Used by Capability/Invariant.lean to transfer cspaceSlotUnique through
-- endpoint operations. TPI-D05: proof completion in WS-E4.
-- ============================================================================

/-- Helper: storeObject on an endpoint ID preserves CNode objects at a different location.
    The proof derives `cnodeId ≠ endpointId` from `hObj` and `hCn` (type disjointness). -/
private theorem storeObject_endpoint_preserves_cnode
    (st st1 : SystemState) (endpointId cnodeId : SeLe4n.ObjId) (ep' : Endpoint) (cn : CNode)
    (hObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1)) :
    st1.objects cnodeId = some (.cnode cn) := by
  have hNe : cnodeId ≠ endpointId := by
    intro hEq; rcases hObj with ⟨ep, hEp⟩; rw [hEq] at hCn; simp [hEp] at hCn
  rw [storeObject_objects_ne st st1 endpointId cnodeId (.endpoint ep') hNe hStore]; exact hCn

/-- Helper: the 3-step chain (storeObject → storeTcbIpcState → removeRunnable) preserves CNodes. -/
private theorem chain_store_tcb_removeRunnable_preserves_cnode
    (st st1 st2 : SystemState) (endpointId cnodeId : SeLe4n.ObjId)
    (ep' : Endpoint) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (cn : CNode)
    (hObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    (removeRunnable st2 tid).objects cnodeId = some (.cnode cn) := by
  rw [removeRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_cnode st1 st2 tid ipc cnodeId cn
    (storeObject_endpoint_preserves_cnode st st1 endpointId cnodeId ep' cn hObj hCn hStore) hTcb

/-- Helper: the 3-step chain (storeObject → storeTcbIpcState → ensureRunnable) preserves CNodes. -/
private theorem chain_store_tcb_ensureRunnable_preserves_cnode
    (st st1 st2 : SystemState) (endpointId cnodeId : SeLe4n.ObjId)
    (ep' : Endpoint) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (cn : CNode)
    (hObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    (ensureRunnable st2 tid).objects cnodeId = some (.cnode cn) := by
  rw [ensureRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_cnode st1 st2 tid ipc cnodeId cn
    (storeObject_endpoint_preserves_cnode st st1 endpointId cnodeId ep' cn hObj hCn hStore) hTcb

/-- endpointSend preserves CNode objects at all locations. -/
theorem endpointSend_preserves_cnode_objects
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (cnodeId : SeLe4n.ObjId)
    (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects cnodeId = some (.cnode cn) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep
      -- idle branch: storeObject → storeTcbIpcState → removeRunnable
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_store_tcb_removeRunnable_preserves_cnode st st1 st2 endpointId cnodeId _ _ _ cn hEpObj hCn hStore hTcb
      -- send branch: storeObject → storeTcbIpcState → removeRunnable
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_store_tcb_removeRunnable_preserves_cnode st st1 st2 endpointId cnodeId _ _ _ cn hEpObj hCn hStore hTcb
      -- receive branch: depends on ep.queue and ep.waitingReceiver
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_store_tcb_ensureRunnable_preserves_cnode st st1 st2 endpointId cnodeId _ _ _ cn hEpObj hCn hStore hTcb
        | cons _ _ => split at hStep <;> simp_all

/-- endpointAwaitReceive preserves CNode objects at all locations. -/
theorem endpointAwaitReceive_preserves_cnode_objects
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (cnodeId : SeLe4n.ObjId)
    (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st'.objects cnodeId = some (.cnode cn) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      -- endpointAwaitReceive matches (ep.state, ep.queue, ep.waitingReceiver)
      -- Only (.idle, [], none) succeeds
      cases hState : ep.state <;> simp only [hState] at hStep <;>
        try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_store_tcb_removeRunnable_preserves_cnode st st1 st2 endpointId cnodeId _ _ _ cn hEpObj hCn hStore hTcb
          · simp at hStep
        · simp at hStep

/-- endpointReceive preserves CNode objects at all locations. -/
theorem endpointReceive_preserves_cnode_objects
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (cnodeId : SeLe4n.ObjId)
    (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st'.objects cnodeId = some (.cnode cn) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      -- endpointReceive matches (ep.state, ep.queue, ep.waitingReceiver)
      -- Only (.send, sender :: rest, none) succeeds
      cases hState : ep.state <;> simp only [hState] at hStep <;>
        try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨hSnd, hEq⟩ := hStep; subst hEq
                exact chain_store_tcb_ensureRunnable_preserves_cnode st st1 st2 endpointId cnodeId _ _ _ cn hEpObj hCn hStore hTcb
          | some _ => split at hStep <;> simp_all

-- ============================================================================
-- H-09 chain helpers: currentThreadValid through storeObject→storeTcbIpcState
-- ============================================================================

/-- After storeObject(endpoint)→storeTcbIpcState, any TCB at the current thread is preserved
    (possibly with modified ipcState). Used by both removeRunnable and ensureRunnable proofs. -/
private theorem chain_preserves_currentThreadValid
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hCTV : currentThreadValid st)
    (hSchedEq : st2.scheduler = st.scheduler)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    ∀ tid', st.scheduler.current = some tid' →
      ∃ tcb : TCB, st2.objects tid'.toObjId = some (.tcb tcb) := by
  intro tid' hCur
  simp only [currentThreadValid, hCur] at hCTV
  rcases hCTV with ⟨tcb, hTcbObj⟩
  have hNe : tid'.toObjId ≠ endpointId := by
    intro h; rcases hEpObj with ⟨ep, hEp⟩; rw [h] at hTcbObj; simp [hEp] at hTcbObj
  have hSt1 : st1.objects tid'.toObjId = some (.tcb tcb) := by
    rw [storeObject_objects_ne st st1 endpointId tid'.toObjId (.endpoint ep') hNe hStore]; exact hTcbObj
  by_cases hNeT : tid'.toObjId = tid.toObjId
  · -- tid' and tid share ObjId: storeTcbIpcState may modify this TCB
    cases hLookup : lookupTcb st1 tid with
    | none =>
      have := storeTcbIpcState_none_result st1 st2 tid ipc hLookup hTcb
      rw [this]; exact ⟨tcb, hSt1⟩
    | some tcb0 =>
      have := storeTcbIpcState_tcb_result st1 st2 tid ipc tcb0 hLookup hTcb
      rw [← hNeT] at this; exact ⟨{ tcb0 with ipcState := ipc }, this⟩
  · -- Different ObjId: storeTcbIpcState preserves objects
    rw [storeTcbIpcState_preserves_objects_ne st1 st2 tid ipc tid'.toObjId hNeT hTcb]
    exact ⟨tcb, hSt1⟩

-- ============================================================================
-- H-09 chain helpers: scheduler invariant components through removeRunnable
-- ============================================================================

/-- The storeObject→storeTcbIpcState→removeRunnable chain preserves schedulerInvariantBundle. -/
private theorem chain_removeRunnable_preserves_schedulerInvariantBundle
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : schedulerInvariantBundle st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    schedulerInvariantBundle (removeRunnable st2 tid) := by
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent
    show queueCurrentConsistent (removeRunnable st2 tid).scheduler
    simp only [queueCurrentConsistent, removeRunnable, hSchedEq]
    by_cases hCurTid : st.scheduler.current = some tid
    · simp [hCurTid]
    · simp only [hCurTid, ↓reduceIte]
      cases hCur : st.scheduler.current with
      | none => simp [hCur]
      | some tid' =>
        simp only [hCur]
        simp only [queueCurrentConsistent, hCur] at hQCC
        have hNe : tid' ≠ tid := by intro h; subst h; exact hCurTid hCur
        exact List.mem_filter.mpr ⟨hQCC, by simp [hNe]⟩
  · -- runQueueUnique
    show runQueueUnique (removeRunnable st2 tid).scheduler
    simp only [runQueueUnique, removeRunnable, hSchedEq]
    exact hRQU.filter _
  · -- currentThreadValid
    show currentThreadValid (removeRunnable st2 tid)
    simp only [currentThreadValid, removeRunnable, hSchedEq]
    by_cases hCurTid : st.scheduler.current = some tid
    · simp [hCurTid]
    · simp only [hCurTid, ↓reduceIte]
      cases hCur : st.scheduler.current with
      | none => simp [hCur]
      | some tid' =>
        simp only [hCur]
        exact chain_preserves_currentThreadValid st st1 st2 endpointId ep' tid ipc
            hCTV hSchedEq hEpObj hStore hTcb tid' hCur

/-- The storeObject→storeTcbIpcState→ensureRunnable chain preserves schedulerInvariantBundle. -/
private theorem chain_ensureRunnable_preserves_schedulerInvariantBundle
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : schedulerInvariantBundle st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    schedulerInvariantBundle (ensureRunnable st2 tid) := by
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  -- currentThreadValid through the chain (objects at current thread preserved)
  have hCtv2 : ∀ tid', st.scheduler.current = some tid' →
      ∃ tcb : TCB, st2.objects tid'.toObjId = some (.tcb tcb) :=
    chain_preserves_currentThreadValid st st1 st2 endpointId ep' tid ipc
      hCTV hSchedEq hEpObj hStore hTcb
  simp only [ensureRunnable, hSchedEq]
  split
  · -- tid ∈ runnable: scheduler unchanged, result is st2
    show schedulerInvariantBundle st2
    refine ⟨hSchedEq ▸ hQCC, hSchedEq ▸ hRQU, ?_⟩
    show currentThreadValid st2
    simp only [currentThreadValid, hSchedEq]
    cases hCur : st.scheduler.current with
    | none => simp [hCur]
    | some tid' => simp only [hCur]; exact hCtv2 tid' hCur
  · -- tid ∉ runnable: runnable extended by [tid]
    rename_i hNotMem
    refine ⟨?_, ?_, ?_⟩
    · -- queueCurrentConsistent
      simp only [queueCurrentConsistent]
      cases hCur : st.scheduler.current with
      | none => simp [hCur]
      | some tid' =>
        simp only [hCur]
        simp only [queueCurrentConsistent, hCur] at hQCC
        exact List.mem_append_left _ hQCC
    · -- runQueueUnique
      simp only [runQueueUnique]
      refine List.nodup_append.mpr ⟨hRQU, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      intro hEq; subst hEq; exact hNotMem ha
    · -- currentThreadValid
      simp only [currentThreadValid]
      cases hCur : st.scheduler.current with
      | none => simp [hCur]
      | some tid' => simp only [hCur]; exact hCtv2 tid' hCur

-- ============================================================================
-- Scheduler invariant bundle preservation (H-09 updated)
-- ============================================================================

/-- H-09: endpointSend preserves the scheduler invariant bundle. -/
theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep
      -- idle
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_schedulerInvariantBundle st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      -- send
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_schedulerInvariantBundle st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      -- receive
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_schedulerInvariantBundle st st1 st2 endpointId _ receiver _ hInv hEpObj hStore hTcb
        | cons _ _ => split at hStep <;> simp_all

/-- H-09: endpointAwaitReceive preserves the scheduler invariant bundle. -/
theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_removeRunnable_preserves_schedulerInvariantBundle st st1 st2 endpointId _ receiver _ hInv hEpObj hStore hTcb
          · simp at hStep
        · simp at hStep

/-- H-09: endpointReceive preserves the scheduler invariant bundle. -/
theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_schedulerInvariantBundle st st1 st2 endpointId _ hd _ hInv hEpObj hStore hTcb
          | some _ => split at hStep <;> simp_all

-- ============================================================================
-- H-09 chain helpers: IPC-scheduler contract predicates through chains
-- ============================================================================

/-- Helper: trace a TCB back through the storeObject→storeTcbIpcState chain for tid' ≠ tid. -/
private theorem chain_tcb_at_ne
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid tid' : SeLe4n.ThreadId) (ipc : ThreadIpcState) (tcb : TCB)
    (hNe : tid' ≠ tid)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2)
    (hPost : st2.objects tid'.toObjId = some (.tcb tcb)) :
    st.objects tid'.toObjId = some (.tcb tcb) := by
  have hObjNe : tid'.toObjId ≠ tid.toObjId := by
    intro h; exact hNe (ThreadId.toObjId_injective tid' tid h)
  have hSt1 : st1.objects tid'.toObjId = some (.tcb tcb) := by
    rwa [storeTcbIpcState_preserves_objects_ne st1 st2 tid ipc tid'.toObjId hObjNe hTcb] at hPost
  have hEpNe : tid'.toObjId ≠ endpointId := by
    intro h
    have := storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
    rw [← h] at this; simp [this] at hSt1
  rwa [storeObject_objects_ne st st1 endpointId tid'.toObjId (.endpoint ep') hEpNe hStore] at hSt1

/-- The removeRunnable chain preserves runnableThreadIpcReady. -/
private theorem chain_removeRunnable_preserves_runnableThreadIpcReady
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : runnableThreadIpcReady st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    runnableThreadIpcReady (removeRunnable st2 tid) := by
  intro tid' tcb' hObj' hMem'
  rw [removeRunnable_preserves_objects] at hObj'
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  simp only [removeRunnable_scheduler, hSchedEq] at hMem'
  have hMemFilt := List.mem_filter.mp hMem'
  have hNe : tid' ≠ tid := by
    intro h; simp [h, beq_self_eq_true, decide_true] at hMemFilt
  have hOrigTcb := chain_tcb_at_ne st st1 st2 endpointId ep' tid tid' ipc tcb' hNe hEpObj hStore hTcb hObj'
  have hOrigMem : tid' ∈ st.scheduler.runnable := hMemFilt.1
  exact hInv tid' tcb' hOrigTcb hOrigMem

/-- The removeRunnable chain preserves blockedOnSendNotRunnable. -/
private theorem chain_removeRunnable_preserves_blockedOnSendNotRunnable
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : blockedOnSendNotRunnable st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    blockedOnSendNotRunnable (removeRunnable st2 tid) := by
  intro tid' tcb' epId hObj' hIpc'
  rw [removeRunnable_preserves_objects] at hObj'
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  simp only [removeRunnable_scheduler, hSchedEq]
  by_cases hEq : tid' = tid
  · -- tid' = tid: tid is filtered out from runnable
    subst hEq
    intro hMem
    exact absurd (List.mem_filter.mp hMem).2 (by simp)
  · -- tid' ≠ tid: TCB unchanged, was blockedOnSend, not in original runnable
    have hOrigTcb := chain_tcb_at_ne st st1 st2 endpointId ep' tid tid' ipc tcb' hEq hEpObj hStore hTcb hObj'
    have hNotMem := hInv tid' tcb' epId hOrigTcb hIpc'
    intro hMem
    exact hNotMem (List.mem_filter.mp hMem).1

/-- The removeRunnable chain preserves blockedOnReceiveNotRunnable. -/
private theorem chain_removeRunnable_preserves_blockedOnReceiveNotRunnable
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : blockedOnReceiveNotRunnable st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid ipc = .ok st2) :
    blockedOnReceiveNotRunnable (removeRunnable st2 tid) := by
  intro tid' tcb' epId hObj' hIpc'
  rw [removeRunnable_preserves_objects] at hObj'
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid ipc hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  simp only [removeRunnable_scheduler, hSchedEq]
  by_cases hEq : tid' = tid
  · subst hEq
    intro hMem
    exact absurd (List.mem_filter.mp hMem).2 (by simp)
  · have hOrigTcb := chain_tcb_at_ne st st1 st2 endpointId ep' tid tid' ipc tcb' hEq hEpObj hStore hTcb hObj'
    have hNotMem := hInv tid' tcb' epId hOrigTcb hIpc'
    intro hMem
    exact hNotMem (List.mem_filter.mp hMem).1

/-- The ensureRunnable chain preserves runnableThreadIpcReady (when ipc = .ready). -/
private theorem chain_ensureRunnable_preserves_runnableThreadIpcReady
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid .ready = .ok st2) :
    runnableThreadIpcReady (ensureRunnable st2 tid) := by
  intro tid' tcb' hObj' hMem'
  rw [ensureRunnable_preserves_objects] at hObj'
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid .ready hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  by_cases hEq : tid' = tid
  · -- tid' = tid: storeTcbIpcState set ipcState = .ready
    rw [hEq] at hObj'
    cases hLookup : lookupTcb st1 tid with
    | none =>
      have hSame := storeTcbIpcState_none_result st1 st2 tid .ready hLookup hTcb
      rw [hSame] at hObj'
      unfold lookupTcb at hLookup
      simp [hObj'] at hLookup
    | some tcb0 =>
      have hResult := storeTcbIpcState_tcb_result st1 st2 tid .ready tcb0 hLookup hTcb
      rw [hResult] at hObj'; cases hObj'
      rfl
  · -- tid' ≠ tid: TCB unchanged
    have hOrigTcb := chain_tcb_at_ne st st1 st2 endpointId ep' tid tid' .ready tcb' hEq hEpObj hStore hTcb hObj'
    simp only [ensureRunnable_scheduler, hSchedEq] at hMem'
    split at hMem'
    · exact hInv tid' tcb' hOrigTcb hMem'
    · rw [List.mem_append] at hMem'
      cases hMem' with
      | inl h => exact hInv tid' tcb' hOrigTcb h
      | inr h => simp at h; exact absurd h hEq

/-- The ensureRunnable chain preserves blockedOnSendNotRunnable (when ipc = .ready). -/
private theorem chain_ensureRunnable_preserves_blockedOnSendNotRunnable
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid .ready = .ok st2) :
    blockedOnSendNotRunnable (ensureRunnable st2 tid) := by
  intro tid' tcb' epId hObj' hIpc'
  rw [ensureRunnable_preserves_objects] at hObj'
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid .ready hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  by_cases hEq : tid' = tid
  · -- tid' = tid: storeTcbIpcState set ipcState = .ready, but hIpc' says blockedOnSend
    rw [hEq] at hObj'
    cases hLookup : lookupTcb st1 tid with
    | none =>
      have hSame := storeTcbIpcState_none_result st1 st2 tid .ready hLookup hTcb
      rw [hSame] at hObj'
      unfold lookupTcb at hLookup
      simp [hObj'] at hLookup
    | some tcb0 =>
      have hResult := storeTcbIpcState_tcb_result st1 st2 tid .ready tcb0 hLookup hTcb
      rw [hResult] at hObj'; cases hObj'
      simp at hIpc'
  · -- tid' ≠ tid: TCB unchanged, was blockedOnSend, not in original runnable
    have hOrigTcb := chain_tcb_at_ne st st1 st2 endpointId ep' tid tid' .ready tcb' hEq hEpObj hStore hTcb hObj'
    have hNotMem := hInv tid' tcb' epId hOrigTcb hIpc'
    simp only [ensureRunnable_scheduler, hSchedEq]
    split
    · exact hNotMem
    · rw [List.mem_append]; intro h; cases h with
      | inl h => exact hNotMem h
      | inr h => simp at h; exact absurd h hEq

/-- The ensureRunnable chain preserves blockedOnReceiveNotRunnable (when ipc = .ready). -/
private theorem chain_ensureRunnable_preserves_blockedOnReceiveNotRunnable
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 tid .ready = .ok st2) :
    blockedOnReceiveNotRunnable (ensureRunnable st2 tid) := by
  intro tid' tcb' epId hObj' hIpc'
  rw [ensureRunnable_preserves_objects] at hObj'
  have hSchedEq : st2.scheduler = st.scheduler := by
    rw [storeTcbIpcState_preserves_scheduler st1 st2 tid .ready hTcb,
        storeObject_scheduler_eq st st1 endpointId (.endpoint ep') hStore]
  by_cases hEq : tid' = tid
  · rw [hEq] at hObj'
    cases hLookup : lookupTcb st1 tid with
    | none =>
      have hSame := storeTcbIpcState_none_result st1 st2 tid .ready hLookup hTcb
      rw [hSame] at hObj'
      unfold lookupTcb at hLookup
      simp [hObj'] at hLookup
    | some tcb0 =>
      have hResult := storeTcbIpcState_tcb_result st1 st2 tid .ready tcb0 hLookup hTcb
      rw [hResult] at hObj'; cases hObj'
      simp at hIpc'
  · have hOrigTcb := chain_tcb_at_ne st st1 st2 endpointId ep' tid tid' .ready tcb' hEq hEpObj hStore hTcb hObj'
    have hNotMem := hInv tid' tcb' epId hOrigTcb hIpc'
    simp only [ensureRunnable_scheduler, hSchedEq]
    split
    · exact hNotMem
    · rw [List.mem_append]; intro h; cases h with
      | inl h => exact hNotMem h
      | inr h => simp at h; exact absurd h hEq

-- ============================================================================
-- IPC-scheduler contract preservation (H-09 updated, non-vacuous)
--
-- TPI-D04: These are the first non-vacuous IPC-scheduler proofs. Before H-09,
-- endpoint operations did not modify thread IPC state, making the predicates
-- trivially preserved. Now they are substantive.
-- ============================================================================

-- ============================================================================
-- Per-component IPC-scheduler predicate preservation (H-09)
--
-- TPI-D04: Individual predicate preservation through the multi-step chain.
-- These decompose ipcSchedulerContractPredicates into its three sub-predicates.
-- ============================================================================

/-- H-09: endpointSend preserves runnableThreadIpcReady. TPI-D04. -/
theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep
      -- idle
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_runnableThreadIpcReady st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      -- send
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_runnableThreadIpcReady st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      -- receive
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_runnableThreadIpcReady st st1 st2 endpointId _ receiver hInv hEpObj hStore hTcb
        | cons _ _ => split at hStep <;> simp_all

/-- H-09: endpointSend preserves blockedOnSendNotRunnable. TPI-D04. -/
theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_blockedOnSendNotRunnable st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_blockedOnSendNotRunnable st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_blockedOnSendNotRunnable st st1 st2 endpointId _ receiver hInv hEpObj hStore hTcb
        | cons _ _ => split at hStep <;> simp_all

/-- H-09: endpointSend preserves blockedOnReceiveNotRunnable. TPI-D04. -/
theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_blockedOnReceiveNotRunnable st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      · revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
          cases hTcb : storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
          | error e => simp [hTcb] at hStep
          | ok st2 =>
            simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact chain_removeRunnable_preserves_blockedOnReceiveNotRunnable st st1 st2 endpointId _ sender _ hInv hEpObj hStore hTcb
      · cases hQueue : ep.queue with
        | nil =>
          cases hWR : ep.waitingReceiver with
          | none => simp [hQueue, hWR] at hStep
          | some receiver =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_blockedOnReceiveNotRunnable st st1 st2 endpointId _ receiver hInv hEpObj hStore hTcb
        | cons _ _ => split at hStep <;> simp_all

/-- H-09: endpointAwaitReceive preserves runnableThreadIpcReady. TPI-D04. -/
theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_removeRunnable_preserves_runnableThreadIpcReady st st1 st2 endpointId _ receiver _ hInv hEpObj hStore hTcb
          · simp at hStep
        · simp at hStep

/-- H-09: endpointAwaitReceive preserves blockedOnSendNotRunnable. TPI-D04. -/
theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_removeRunnable_preserves_blockedOnSendNotRunnable st st1 st2 endpointId _ receiver _ hInv hEpObj hStore hTcb
          · simp at hStep
        · simp at hStep

/-- H-09: endpointAwaitReceive preserves blockedOnReceiveNotRunnable. TPI-D04. -/
theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue <;> simp only [hQueue] at hStep
        · cases hWR : ep.waitingReceiver <;> simp only [hWR] at hStep
          · revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_removeRunnable_preserves_blockedOnReceiveNotRunnable st st1 st2 endpointId _ receiver _ hInv hEpObj hStore hTcb
          · simp at hStep
        · simp at hStep

/-- H-09: endpointReceive preserves runnableThreadIpcReady. TPI-D04. -/
theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_runnableThreadIpcReady st st1 st2 endpointId _ hd hInv hEpObj hStore hTcb
          | some _ => split at hStep <;> simp_all

/-- H-09: endpointReceive preserves blockedOnSendNotRunnable. TPI-D04. -/
theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_blockedOnSendNotRunnable st st1 st2 endpointId _ hd hInv hEpObj hStore hTcb
          | some _ => split at hStep <;> simp_all

/-- H-09: endpointReceive preserves blockedOnReceiveNotRunnable. TPI-D04. -/
theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hEpObj : ∃ ep, st.objects endpointId = some (.endpoint ep) := ⟨ep, hObj⟩
      cases hState : ep.state <;> simp only [hState] at hStep <;> try simp at hStep
      · cases hQueue : ep.queue with
        | nil => split at hStep <;> simp_all
        | cons hd tl =>
          cases hWR : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId (.endpoint { state := if tl = [] then .idle else .send, queue := tl, waitingReceiver := none }) st with
            | error e => simp
            | ok pair =>
              obtain ⟨⟨⟩, st1⟩ := pair; simp only at hStore ⊢; intro hStep
              cases hTcb : storeTcbIpcState st1 hd .ready with
              | error e => simp [hTcb] at hStep
              | ok st2 =>
                simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact chain_ensureRunnable_preserves_blockedOnReceiveNotRunnable st st1 st2 endpointId _ hd hInv hEpObj hStore hTcb
          | some _ => split at hStep <;> simp_all

-- ============================================================================
-- IPC-scheduler contract bundle preservation (H-09)
--
-- TPI-D04: Combine per-component proofs into the full bundle.
-- ============================================================================

/-- H-09: endpointSend preserves ipcSchedulerContractPredicates. TPI-D04. -/
theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨h1, h2, h3⟩ := hInv
  exact ⟨endpointSend_preserves_runnableThreadIpcReady st st' endpointId sender h1 hStep,
         endpointSend_preserves_blockedOnSendNotRunnable st st' endpointId sender h2 hStep,
         endpointSend_preserves_blockedOnReceiveNotRunnable st st' endpointId sender h3 hStep⟩

/-- H-09: endpointAwaitReceive preserves ipcSchedulerContractPredicates. TPI-D04. -/
theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨h1, h2, h3⟩ := hInv
  exact ⟨endpointAwaitReceive_preserves_runnableThreadIpcReady st st' endpointId receiver h1 hStep,
         endpointAwaitReceive_preserves_blockedOnSendNotRunnable st st' endpointId receiver h2 hStep,
         endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable st st' endpointId receiver h3 hStep⟩

/-- H-09: endpointReceive preserves ipcSchedulerContractPredicates. TPI-D04. -/
theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨h1, h2, h3⟩ := hInv
  exact ⟨endpointReceive_preserves_runnableThreadIpcReady st st' endpointId sender h1 hStep,
         endpointReceive_preserves_blockedOnSendNotRunnable st st' endpointId sender h2 hStep,
         endpointReceive_preserves_blockedOnReceiveNotRunnable st st' endpointId sender h3 hStep⟩

-- ============================================================================
-- M3.5 step-5 helper lemmas: TCB/runnable witnesses through endpoint stores
--
-- TPI-D04: These lemmas show that storeObject on an endpoint ID preserves TCB
-- lookups and runnable-queue membership at other object IDs, since endpoints
-- and TCBs are type-disjoint objects.
-- ============================================================================

/-- After storing an endpoint object, a TCB lookup at a different ID is unchanged. TPI-D04. -/
theorem tcb_lookup_of_endpoint_store
    (st st' : SystemState) (epId tcbId : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : tcbId ≠ epId)
    (hStore : storeObject epId (.endpoint ep) st = .ok ((), st')) :
    st'.objects tcbId = st.objects tcbId := by
  exact storeObject_objects_ne st st' epId tcbId (.endpoint ep) hNe hStore

/-- After storing an endpoint object, runnable-queue membership is unchanged. TPI-D04. -/
theorem runnable_membership_of_endpoint_store
    (st st' : SystemState) (epId : SeLe4n.ObjId) (ep : Endpoint) (tid : SeLe4n.ThreadId)
    (hStore : storeObject epId (.endpoint ep) st = .ok ((), st'))
    (hMem : tid ∈ st.scheduler.runnable) :
    tid ∈ st'.scheduler.runnable := by
  have hSched := storeObject_scheduler_eq st st' epId (.endpoint ep) hStore
  rw [hSched]; exact hMem

/-- After storing an endpoint object, non-membership in runnable queue is unchanged. TPI-D04. -/
theorem not_runnable_membership_of_endpoint_store
    (st st' : SystemState) (epId : SeLe4n.ObjId) (ep : Endpoint) (tid : SeLe4n.ThreadId)
    (hStore : storeObject epId (.endpoint ep) st = .ok ((), st'))
    (hNotMem : tid ∉ st.scheduler.runnable) :
    tid ∉ st'.scheduler.runnable := by
  have hSched := storeObject_scheduler_eq st st' epId (.endpoint ep) hStore
  rw [hSched]; exact hNotMem

-- ============================================================================
-- Notification invariant preservation
-- ============================================================================

/-- Notification wait-path preserves waiter list membership. -/
theorem notificationWait_preserves_uniqueWaiters
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (hStep : notificationWait notifId waiter st = .ok (none, st')) :
    ∀ ntfn', st'.objects notifId = some (.notification ntfn') →
      waiter ∈ ntfn'.waitingThreads := by
  rcases notificationWait_wait_path_notification st st' notifId waiter hStep with
    ⟨ntfnPre, ntfnPost, _hPre, _hNoBadge, _hNotMem, hPost, hWaiters⟩
  intro ntfn' hObj'
  rw [hPost] at hObj'
  cases hObj'
  simp [hWaiters]

end SeLe4n.Kernel
