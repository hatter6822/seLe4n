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

H-09 (WS-E3): Public endpoint operations now compose a Core endpoint-object step
with IPC state effects (storeTcbIpcState + blockThread/ensureRunnable). Proofs track
invariants through each phase. Core operation proofs (suffixed `Core`) follow the
original single-storeObject pattern; public operation proofs compose Core proofs with
effects-frame lemmas.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Section 1: Transport lemmas unique to invariant proofs
--
-- Note: storeObject_objects_eq/ne/scheduler_eq are in Model/State.lean.
-- storeTcbIpcState_preserves_objects_ne, storeTcbIpcState_scheduler_eq,
-- storeTcbIpcState_preserves_notification, blockThread_preserves_objects,
-- ensureRunnable_preserves_objects, removeRunnable_preserves_objects,
-- applyBlockEffect_preserves_objects_ne, applyUnblockEffect_preserves_objects_ne
-- are in IPC/Operations.lean.
-- ============================================================================

/-- `storeTcbIpcState` preserves endpoint objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_endpoint
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (eid : SeLe4n.ObjId)
    (ep : Endpoint)
    (hEp : st.objects eid = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects eid = some (.endpoint ep) := by
  by_cases hEq : eid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep
    subst hStep
    exact hEp
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc eid hEq hStep]
    exact hEp

/-- Local lookup helper for endpoint transitions:
if an endpoint-object store succeeds, any TCB lookup in the post-state
comes from the pre-state. -/
theorem tcb_lookup_of_endpoint_store
    (st st' : SystemState)
    (endpointId tid : SeLe4n.ObjId)
    (tcb : TCB)
    (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hObj : st'.objects tid = some (.tcb tcb)) :
    st.objects tid = some (.tcb tcb) := by
  by_cases hEq : tid = endpointId
  · have hObjAtEndpoint : st'.objects endpointId = some (.tcb tcb) := by
      simpa [hEq] using hObj
    rw [storeObject_objects_eq st st' endpointId (.endpoint ep') hStore] at hObjAtEndpoint
    cases hObjAtEndpoint
  · rw [storeObject_objects_ne st st' endpointId tid (.endpoint ep') hEq hStore] at hObj
    exact hObj

/-- Scheduler-local helper for endpoint transitions:
endpoint-object stores do not alter runnable-set membership goals. -/
theorem runnable_membership_of_endpoint_store
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId)
    (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hRun : tid ∈ st'.scheduler.runnable) :
    tid ∈ st.scheduler.runnable := by
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore
  simpa [hSchedEq] using hRun

/-- Scheduler-local helper for endpoint transitions:
endpoint-object stores do not alter non-runnable goals. -/
theorem not_runnable_membership_of_endpoint_store
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId)
    (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hNotRun : tid ∉ st.scheduler.runnable) :
    tid ∉ st'.scheduler.runnable := by
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore
  simpa [hSchedEq] using hNotRun

-- ============================================================================
-- Section 2: Scheduler effect helpers
-- ============================================================================

/-- `blockThread` only shrinks the runnable set. -/
private theorem blockThread_runnable_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (blockThread st tid).scheduler.runnable = st.scheduler.runnable.filter (· ≠ tid) := by
  unfold blockThread removeRunnable
  dsimp only
  split
  · -- some case: split the if
    split <;> simp
  · -- none case
    simp

private theorem blockThread_runnable_subset
    (st : SystemState) (tid tid' : SeLe4n.ThreadId)
    (hRun : tid' ∈ (blockThread st tid).scheduler.runnable) :
    tid' ∈ st.scheduler.runnable ∧ tid' ≠ tid := by
  rw [blockThread_runnable_eq] at hRun
  rw [List.mem_filter] at hRun
  exact ⟨hRun.1, of_decide_eq_true hRun.2⟩

/-- `blockThread` removes `tid` from the runnable set. -/
private theorem blockThread_not_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∉ (blockThread st tid).scheduler.runnable := by
  intro hMem
  have ⟨_, hNe⟩ := blockThread_runnable_subset st tid tid hMem
  exact hNe rfl

/-- Any thread runnable before is runnable after `ensureRunnable`. -/
private theorem ensureRunnable_runnable_superset
    (st : SystemState) (tid tid' : SeLe4n.ThreadId)
    (hRun : tid' ∈ st.scheduler.runnable) :
    tid' ∈ (ensureRunnable st tid).scheduler.runnable := by
  unfold ensureRunnable
  split
  · exact hRun
  · simp; exact Or.inl hRun

/-- The target thread is runnable after `ensureRunnable`. -/
private theorem ensureRunnable_target_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∈ (ensureRunnable st tid).scheduler.runnable := by
  unfold ensureRunnable
  split
  · assumption
  · simp

/-- After `ensureRunnable`, any runnable thread was either already runnable or is the target. -/
private theorem ensureRunnable_runnable_cases
    (st : SystemState) (tid tid' : SeLe4n.ThreadId)
    (hRun : tid' ∈ (ensureRunnable st tid).scheduler.runnable) :
    tid' ∈ st.scheduler.runnable ∨ tid' = tid := by
  unfold ensureRunnable at hRun
  split at hRun
  · exact Or.inl hRun
  · simp at hRun
    rcases hRun with hOld | hNew
    · exact Or.inl hOld
    · exact Or.inr hNew

/-- `storeTcbIpcState` writes the specified ipcState to the target TCB
(when the TCB exists). -/
private theorem storeTcbIpcState_updates_target
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (tcb : TCB)
    (hTcbPre : st.objects tid.toObjId = some (.tcb tcb))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects tid.toObjId = some (.tcb { tcb with ipcState := ipc }) := by
  unfold storeTcbIpcState at hStep
  have hLookup : lookupTcb st tid = some tcb := by
    unfold lookupTcb; simp [hTcbPre]
  simp only [hLookup] at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hStore] at hStep
  | ok pair =>
    simp only [hStore] at hStep
    have hEq : pair.snd = st' := Except.ok.inj hStep
    subst hEq
    exact storeObject_objects_eq st pair.2 tid.toObjId
      (.tcb { tcb with ipcState := ipc }) hStore

-- ============================================================================
-- Section 3: Invariant definitions
-- ============================================================================

/-- Endpoint-local queue/state well-formedness for the M3.5 handshake scaffold.

Policy for this slice stays deterministic and ownership-explicit:
- `idle` endpoints have an empty sender queue and no waiting receiver,
- `send` endpoints have a non-empty sender queue and no waiting receiver,
- `receive` endpoints have an empty sender queue and one waiting receiver identity. -/
def endpointQueueWellFormed (ep : Endpoint) : Prop :=
  match ep.state with
  | .idle => ep.queue = [] ∧ ep.waitingReceiver = none
  | .send => ep.queue ≠ [] ∧ ep.waitingReceiver = none
  | .receive => ep.queue = [] ∧ ep.waitingReceiver.isSome

/-- Endpoint/object validity component for the active IPC slice. -/
def endpointObjectValid (ep : Endpoint) : Prop :=
  match ep.waitingReceiver with
  | none => ep.state ≠ .receive
  | some _ => ep.state = .receive

/-- IPC invariant component bundle for one endpoint object. -/
def endpointInvariant (ep : Endpoint) : Prop :=
  endpointQueueWellFormed ep ∧ endpointObjectValid ep

/-- Notification-local queue/state consistency for WS-B6. -/
def notificationQueueWellFormed (ntfn : Notification) : Prop :=
  match ntfn.state with
  | .idle => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge = none
  | .waiting => ntfn.waitingThreads ≠ [] ∧ ntfn.pendingBadge = none
  | .active => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge.isSome

/-- Notification safety bundle for IPC completeness. -/
def notificationInvariant (ntfn : Notification) : Prop :=
  notificationQueueWellFormed ntfn

/-- Global IPC seed invariant entrypoint. -/
def ipcInvariant (st : SystemState) : Prop :=
  (∀ oid ep,
    st.objects oid = some (.endpoint ep) →
    endpointInvariant ep) ∧
  (∀ oid ntfn,
    st.objects oid = some (.notification ntfn) →
    notificationInvariant ntfn)

/-- Scheduler contract predicate #1 for M3.5: runnable threads are explicitly IPC-ready. -/
def runnableThreadIpcReady (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb,
    st.objects tid.toObjId = some (.tcb tcb) →
    tid ∈ st.scheduler.runnable →
    tcb.ipcState = .ready

/-- Scheduler contract predicate #2 for M3.5: send-blocked threads are not runnable. -/
def blockedOnSendNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnSend endpointId →
    tid ∉ st.scheduler.runnable

/-- Scheduler contract predicate #3 for M3.5: receive-blocked threads are not runnable. -/
def blockedOnReceiveNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnReceive endpointId →
    tid ∉ st.scheduler.runnable

/-- Targeted scheduler/IPC coherence contract for the M3.5 step-3 slice. -/
def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧
  blockedOnSendNotRunnable st ∧
  blockedOnReceiveNotRunnable st

-- ============================================================================
-- Section 4: Core decomposition lemmas
-- Core operations = old operations = exactly one storeObject
-- ============================================================================

/-- Core send is exactly one endpoint-object update. -/
theorem endpointSendCore_ok_as_storeObject
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st') := by
  unfold endpointSendCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state with
          | idle =>
              simp [hObj, hState, storeObject] at hStep
              refine ⟨{ state := .send, queue := [sender], waitingReceiver := none }, ?_⟩
              simp [storeObject, hStep]
          | send =>
              simp [hObj, hState, storeObject] at hStep
              refine ⟨{ state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }, ?_⟩
              simp [storeObject, hStep]
          | receive =>
              cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
                simp [hObj, hState, hQueue, hWait, storeObject] at hStep
              case nil.some receiver =>
                refine ⟨{ state := .idle, queue := [], waitingReceiver := none }, ?_⟩
                simp [storeObject, hStep]

/-- Core await-receive is exactly one endpoint-object update. -/
theorem endpointAwaitReceiveCore_ok_as_storeObject
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st') := by
  unfold endpointAwaitReceiveCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
            simp [hObj, hState, hQueue, hWait, storeObject] at hStep
          case idle.nil.none =>
            refine ⟨{ state := .receive, queue := [], waitingReceiver := some receiver }, ?_⟩
            simp [storeObject, hStep]

/-- Core receive is exactly one endpoint-object update. -/
theorem endpointReceiveCore_ok_as_storeObject
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st') := by
  unfold endpointReceiveCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> simp [hObj, hState] at hStep
          case send =>
            cases hQueue : ep.queue with
            | nil =>
                cases hWait : ep.waitingReceiver <;>
                  simp [hQueue, hWait] at hStep
            | cons head tail =>
                cases hWait : ep.waitingReceiver with
                | none =>
                    simp [hQueue, hWait, storeObject] at hStep
                    rcases hStep with ⟨_, hStore⟩
                    let nextState : EndpointState := if tail.isEmpty then .idle else .send
                    refine ⟨{ state := nextState, queue := tail, waitingReceiver := none }, ?_⟩
                    simp [storeObject, nextState, hStore]
                | some receiver =>
                    simp [hQueue, hWait] at hStep

theorem endpointObjectValid_of_queueWellFormed
    (ep : Endpoint)
    (hWf : endpointQueueWellFormed ep) :
    endpointObjectValid ep := by
  cases hState : ep.state <;> cases hWait : ep.waitingReceiver <;>
    simp [endpointQueueWellFormed, endpointObjectValid, hState, hWait] at hWf ⊢

-- ============================================================================
-- Section 5: Core operation result well-formedness
-- ============================================================================

theorem endpointSendCore_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointSendCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state with
          | idle =>
              simp [hObj, hState, storeObject] at hStep
              cases hStep
              refine ⟨{ state := .send, queue := [sender], waitingReceiver := none }, ?_, ?_⟩
              · simp
              · simp [endpointQueueWellFormed]
          | send =>
              simp [hObj, hState, storeObject] at hStep
              cases hStep
              refine ⟨{ state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }, ?_, ?_⟩
              · simp
              · simp [endpointQueueWellFormed]
          | receive =>
              cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
                simp [hObj, hState, hQueue, hWait, storeObject] at hStep
              case nil.some receiver =>
                refine ⟨{ state := .idle, queue := [], waitingReceiver := none }, ?_, ?_⟩
                · cases hStep
                  simp
                · simp [endpointQueueWellFormed]

theorem endpointAwaitReceiveCore_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointAwaitReceiveCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
            simp [hObj, hState, hQueue, hWait, storeObject] at hStep
          case idle.nil.none =>
            refine ⟨{ state := .receive, queue := [], waitingReceiver := some receiver }, ?_, ?_⟩
            · cases hStep
              simp
            · simp [endpointQueueWellFormed]

theorem endpointReceiveCore_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointReceiveCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> simp [hObj, hState] at hStep
          case send =>
            cases hQueue : ep.queue with
            | nil =>
                cases hWait : ep.waitingReceiver <;>
                  simp [hQueue, hWait] at hStep
            | cons head tail =>
                cases hWait : ep.waitingReceiver with
                | none =>
                    simp [hQueue, hWait, storeObject] at hStep
                    rcases hStep with ⟨hSender, hStoreEq⟩
                    let nextState : EndpointState := if tail.isEmpty then .idle else .send
                    refine ⟨{ state := nextState, queue := tail, waitingReceiver := none }, ?_, ?_⟩
                    · cases hStoreEq
                      simp [nextState]
                    · cases hTail : tail with
                      | nil => simp [endpointQueueWellFormed, nextState, hTail]
                      | cons t ts => simp [endpointQueueWellFormed, nextState, hTail]
                | some receiver =>
                    simp [hQueue, hWait] at hStep

-- ============================================================================
-- Section 6: Core preserves other objects + ok_implies_endpoint_object
-- ============================================================================

theorem endpointSendCore_preserves_other_objects
    (st st' : SystemState)
    (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hNe : oid ≠ endpointId)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  rcases endpointSendCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  exact storeObject_objects_ne st st' endpointId oid (.endpoint ep') hNe hStore

theorem endpointAwaitReceiveCore_preserves_other_objects
    (st st' : SystemState)
    (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hNe : oid ≠ endpointId)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  rcases endpointAwaitReceiveCore_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  exact storeObject_objects_ne st st' endpointId oid (.endpoint ep') hNe hStore

theorem endpointReceiveCore_preserves_other_objects
    (st st' : SystemState)
    (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hNe : oid ≠ endpointId)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    st'.objects oid = st.objects oid := by
  rcases endpointReceiveCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  exact storeObject_objects_ne st st' endpointId oid (.endpoint ep') hNe hStore

theorem endpointSendCore_ok_implies_endpoint_object
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointSendCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep => exact ⟨ep, rfl⟩

theorem endpointAwaitReceiveCore_ok_implies_endpoint_object
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointAwaitReceiveCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep => exact ⟨ep, rfl⟩

theorem endpointReceiveCore_ok_implies_endpoint_object
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointReceiveCore at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep => exact ⟨ep, rfl⟩

-- ============================================================================
-- Section 7: Core preserves scheduler invariant bundle
-- ============================================================================

/-- Shared preservation helper for core endpoint operations that perform one endpoint-object store. -/
theorem endpoint_store_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (hInv : schedulerInvariantBundle st)
    (hStore : ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hEndpointObj : ∃ ep, st.objects endpointId = some (.endpoint ep))
    (hPreserveOther : ∀ oid, oid ≠ endpointId → st'.objects oid = st.objects oid) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  rcases hStore with ⟨ep', hStoreEq⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStoreEq
  have hCurEq : st'.scheduler.current = st.scheduler.current := by simp [hSchedEq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hSchedEq] using hQueue
  · simpa [hSchedEq] using hRunq
  · cases hCurrent : st.scheduler.current with
    | none =>
        simp [currentThreadValid, hCurEq, hCurrent]
    | some tid =>
        have hCurSome : ∃ tcb : TCB, st.objects tid.toObjId = some (.tcb tcb) := by
          simpa [currentThreadValid, hCurrent] using hCur
        rcases hCurSome with ⟨tcb, hTcbObj⟩
        have hTidNe : tid.toObjId ≠ endpointId := by
          intro hEq
          subst hEq
          rcases hEndpointObj with ⟨ep, hEpObj⟩
          rw [hEpObj] at hTcbObj
          cases hTcbObj
        have hTcbObj' : st'.objects tid.toObjId = some (.tcb tcb) := by
          rw [hPreserveOther tid.toObjId hTidNe]
          exact hTcbObj
        simp [currentThreadValid, hCurEq, hCurrent, hTcbObj']

theorem endpointSendCore_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    schedulerInvariantBundle st' :=
  endpoint_store_preserves_schedulerInvariantBundle st st' endpointId hInv
    (endpointSendCore_ok_as_storeObject st st' endpointId sender hStep)
    (endpointSendCore_ok_implies_endpoint_object st st' endpointId sender hStep)
    (fun oid hNe => endpointSendCore_preserves_other_objects st st' endpointId oid sender hNe hStep)

theorem endpointAwaitReceiveCore_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' :=
  endpoint_store_preserves_schedulerInvariantBundle st st' endpointId hInv
    (endpointAwaitReceiveCore_ok_as_storeObject st st' endpointId receiver hStep)
    (endpointAwaitReceiveCore_ok_implies_endpoint_object st st' endpointId receiver hStep)
    (fun oid hNe => endpointAwaitReceiveCore_preserves_other_objects st st' endpointId oid receiver hNe hStep)

theorem endpointReceiveCore_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    schedulerInvariantBundle st' :=
  endpoint_store_preserves_schedulerInvariantBundle st st' endpointId hInv
    (endpointReceiveCore_ok_as_storeObject st st' endpointId sender hStep)
    (endpointReceiveCore_ok_implies_endpoint_object st st' endpointId sender hStep)
    (fun oid hNe => endpointReceiveCore_preserves_other_objects st st' endpointId oid sender hNe hStep)

-- ============================================================================
-- Section 8: Core preserves IPC scheduler contract predicates
-- ============================================================================

theorem endpointSendCore_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  rcases endpointSendCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb hObj hRun
  exact hInv tid tcb
    (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj)
    (runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hRun)

theorem endpointSendCore_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointSendCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore
    (hInv tid tcb endpoint (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj) hBlocked)

theorem endpointSendCore_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointSendCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore
    (hInv tid tcb endpoint (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj) hBlocked)

theorem endpointSendCore_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  exact ⟨endpointSendCore_preserves_runnableThreadIpcReady st st' endpointId sender hReady hStep,
         endpointSendCore_preserves_blockedOnSendNotRunnable st st' endpointId sender hBlockedSend hStep,
         endpointSendCore_preserves_blockedOnReceiveNotRunnable st st' endpointId sender hBlockedReceive hStep⟩

-- Parallel contract proofs for AwaitReceive and Receive (Core)

theorem endpointAwaitReceiveCore_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  rcases endpointAwaitReceiveCore_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  refine ⟨?_, ?_, ?_⟩
  · intro tid tcb hObj hRun
    exact hReady tid tcb
      (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj)
      (runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hRun)
  · intro tid tcb endpoint hObj hBlocked
    exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore
      (hBlockedSend tid tcb endpoint (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj) hBlocked)
  · intro tid tcb endpoint hObj hBlocked
    exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore
      (hBlockedReceive tid tcb endpoint (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj) hBlocked)

theorem endpointReceiveCore_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  rcases endpointReceiveCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  refine ⟨?_, ?_, ?_⟩
  · intro tid tcb hObj hRun
    exact hReady tid tcb
      (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj)
      (runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hRun)
  · intro tid tcb endpoint hObj hBlocked
    exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore
      (hBlockedSend tid tcb endpoint (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj) hBlocked)
  · intro tid tcb endpoint hObj hBlocked
    exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore
      (hBlockedReceive tid tcb endpoint (tcb_lookup_of_endpoint_store st st' endpointId tid.toObjId tcb ep' hStore hObj) hBlocked)

-- ============================================================================
-- Section 9: Core preserves ipcInvariant
-- ============================================================================

theorem endpointSendCore_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointSendCore endpointId sender st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  rcases endpointSendCore_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    by_cases hEq : oid = endpointId
    · subst hEq
      rw [hStored] at hObj; cases hObj
      exact ⟨hWfNew, endpointObjectValid_of_queueWellFormed epNew hWfNew⟩
    · exact hEndpointInv oid ep (by rwa [endpointSendCore_preserves_other_objects st st' endpointId oid sender hEq hStep] at hObj)
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
    · exact hNotificationInv oid ntfn (by rwa [endpointSendCore_preserves_other_objects st st' endpointId oid sender hEq hStep] at hObj)

theorem endpointAwaitReceiveCore_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceiveCore endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  rcases endpointAwaitReceiveCore_result_wellFormed st st' endpointId receiver hStep with ⟨epNew, hStored, hWfNew⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
      exact ⟨hWfNew, endpointObjectValid_of_queueWellFormed epNew hWfNew⟩
    · exact hEndpointInv oid ep (by rwa [endpointAwaitReceiveCore_preserves_other_objects st st' endpointId oid receiver hEq hStep] at hObj)
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
    · exact hNotificationInv oid ntfn (by rwa [endpointAwaitReceiveCore_preserves_other_objects st st' endpointId oid receiver hEq hStep] at hObj)

theorem endpointReceiveCore_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceiveCore endpointId st = .ok (sender, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  rcases endpointReceiveCore_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
      exact ⟨hWfNew, endpointObjectValid_of_queueWellFormed epNew hWfNew⟩
    · exact hEndpointInv oid ep (by rwa [endpointReceiveCore_preserves_other_objects st st' endpointId oid sender hEq hStep] at hObj)
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
    · exact hNotificationInv oid ntfn (by rwa [endpointReceiveCore_preserves_other_objects st st' endpointId oid sender hEq hStep] at hObj)

-- ============================================================================
-- Section 10: Effects frame lemmas
--
-- Effects (storeTcbIpcState + blockThread/ensureRunnable) preserve endpoint
-- and notification objects, enabling compositional public-operation proofs.
-- ============================================================================

/-- applyBlockEffect preserves endpoint objects: storeTcbIpcState only writes TCBs,
blockThread only modifies the scheduler. -/
private theorem applyBlockEffect_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (eid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects eid = some (.endpoint ep))
    (hStep : applyBlockEffect st tid ipc = .ok st') :
    st'.objects eid = some (.endpoint ep) := by
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [blockThread_preserves_objects]
    exact storeTcbIpcState_preserves_endpoint st stMid tid ipc eid ep hEp hTcb

/-- applyUnblockEffect preserves endpoint objects. -/
private theorem applyUnblockEffect_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (eid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects eid = some (.endpoint ep))
    (hStep : applyUnblockEffect st tid = .ok st') :
    st'.objects eid = some (.endpoint ep) := by
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [ensureRunnable_preserves_objects]
    exact storeTcbIpcState_preserves_endpoint st stMid tid .ready eid ep hEp hTcb

/-- applyBlockEffect preserves notification objects. -/
private theorem applyBlockEffect_preserves_notification
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects nid = some (.notification ntfn))
    (hStep : applyBlockEffect st tid ipc = .ok st') :
    st'.objects nid = some (.notification ntfn) := by
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [blockThread_preserves_objects]
    exact storeTcbIpcState_preserves_notification st stMid tid ipc nid ntfn hNtfn hTcb

/-- applyUnblockEffect preserves notification objects. -/
private theorem applyUnblockEffect_preserves_notification
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects nid = some (.notification ntfn))
    (hStep : applyUnblockEffect st tid = .ok st') :
    st'.objects nid = some (.notification ntfn) := by
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [ensureRunnable_preserves_objects]
    exact storeTcbIpcState_preserves_notification st stMid tid .ready nid ntfn hNtfn hTcb

/-- CNode preservation through effects: CNode objects are never TCBs, so storeTcbIpcState
is a no-op for them, and blockThread/ensureRunnable don't touch objects. -/
private theorem applyBlockEffect_preserves_cnode
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (cid : SeLe4n.ObjId) (cn : CNode)
    (hCn : st.objects cid = some (.cnode cn))
    (hStep : applyBlockEffect st tid ipc = .ok st') :
    st'.objects cid = some (.cnode cn) := by
  by_cases hEq : cid = tid.toObjId
  · subst hEq
    unfold applyBlockEffect at hStep
    cases hTcb : storeTcbIpcState st tid ipc with
    | error e => simp [hTcb] at hStep
    | ok stMid =>
      simp only [hTcb] at hStep
      have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
      subst hEq
      rw [blockThread_preserves_objects]
      unfold storeTcbIpcState at hTcb
      have hLookup : lookupTcb st tid = none := by
        unfold lookupTcb; simp [hCn]
      simp [hLookup] at hTcb
      subst hTcb
      exact hCn
  · rw [applyBlockEffect_preserves_objects_ne st st' tid ipc cid hEq hStep]
    exact hCn

private theorem applyUnblockEffect_preserves_cnode
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (cid : SeLe4n.ObjId) (cn : CNode)
    (hCn : st.objects cid = some (.cnode cn))
    (hStep : applyUnblockEffect st tid = .ok st') :
    st'.objects cid = some (.cnode cn) := by
  by_cases hEq : cid = tid.toObjId
  · subst hEq
    unfold applyUnblockEffect at hStep
    cases hTcb : storeTcbIpcState st tid .ready with
    | error e => simp [hTcb] at hStep
    | ok stMid =>
      simp only [hTcb] at hStep
      have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
      subst hEq
      rw [ensureRunnable_preserves_objects]
      unfold storeTcbIpcState at hTcb
      have hLookup : lookupTcb st tid = none := by
        unfold lookupTcb; simp [hCn]
      simp [hLookup] at hTcb
      subst hTcb
      exact hCn
  · rw [applyUnblockEffect_preserves_objects_ne st st' tid cid hEq hStep]
    exact hCn

/-- Backward endpoint preservation through applyBlockEffect: if the final state has an
endpoint at oid, the pre-state had it too. storeTcbIpcState only writes TCBs, so an
endpoint in the result must have been there before. -/
private theorem applyBlockEffect_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : applyBlockEffect st tid ipc = .ok st')
    (hObj : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [blockThread_preserves_objects] at hObj
    -- Now hObj : stMid.objects oid = some (.endpoint ep)
    by_cases hNe : oid = tid.toObjId
    · subst hNe
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hTcb; subst hTcb; exact hObj
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
        | error e => simp [hStore] at hTcb
        | ok pair =>
          simp only [hStore] at hTcb
          have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
          subst hPairEq
          rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := ipc }) hStore] at hObj
          cases hObj
    · exact by rw [storeTcbIpcState_preserves_objects_ne st stMid tid ipc oid hNe hTcb] at hObj; exact hObj

private theorem applyUnblockEffect_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : applyUnblockEffect st tid = .ok st')
    (hObj : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [ensureRunnable_preserves_objects] at hObj
    by_cases hNe : oid = tid.toObjId
    · subst hNe
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hTcb; subst hTcb; exact hObj
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready }) st with
        | error e => simp [hStore] at hTcb
        | ok pair =>
          simp only [hStore] at hTcb
          have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
          subst hPairEq
          rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hObj
          cases hObj
    · exact by rw [storeTcbIpcState_preserves_objects_ne st stMid tid .ready oid hNe hTcb] at hObj; exact hObj

/-- Backward notification preservation through applyBlockEffect. -/
private theorem applyBlockEffect_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : applyBlockEffect st tid ipc = .ok st')
    (hObj : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [blockThread_preserves_objects] at hObj
    by_cases hNe : oid = tid.toObjId
    · subst hNe
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hTcb; subst hTcb; exact hObj
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
        | error e => simp [hStore] at hTcb
        | ok pair =>
          simp only [hStore] at hTcb
          have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
          subst hPairEq
          rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := ipc }) hStore] at hObj
          cases hObj
    · exact by rw [storeTcbIpcState_preserves_objects_ne st stMid tid ipc oid hNe hTcb] at hObj; exact hObj

private theorem applyUnblockEffect_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : applyUnblockEffect st tid = .ok st')
    (hObj : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    rw [ensureRunnable_preserves_objects] at hObj
    by_cases hNe : oid = tid.toObjId
    · subst hNe
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hTcb; subst hTcb; exact hObj
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready }) st with
        | error e => simp [hStore] at hTcb
        | ok pair =>
          simp only [hStore] at hTcb
          have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
          subst hPairEq
          rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hObj
          cases hObj
    · exact by rw [storeTcbIpcState_preserves_objects_ne st stMid tid .ready oid hNe hTcb] at hObj; exact hObj

-- ============================================================================
-- Section 11: Public operation proofs
--
-- H-09 (WS-E3): Public operations = Core step + IPC effects. Proofs compose
-- Core-step preservation + effects frame lemmas.
-- ============================================================================

/-- Public send: if the operation succeeds, there was an endpoint at endpointId. -/
theorem endpointSend_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    exact endpointSendCore_ok_implies_endpoint_object st st' endpointId sender hStep
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      exact endpointSendCore_ok_implies_endpoint_object st pair.2 endpointId sender hCore

theorem endpointAwaitReceive_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointAwaitReceive at hStep
  cases hCore : endpointAwaitReceiveCore endpointId receiver st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    exact endpointAwaitReceiveCore_ok_implies_endpoint_object st pair.2 endpointId receiver hCore

theorem endpointReceive_ok_implies_endpoint_object
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep, st.objects endpointId = some (.endpoint ep) := by
  unfold endpointReceive at hStep
  cases hCore : endpointReceiveCore endpointId st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    exact endpointReceiveCore_ok_implies_endpoint_object st pair.2 endpointId pair.1 hCore

/-- Public send preserves endpoint objects at oid ≠ endpointId. -/
theorem endpointSend_preserves_endpoint_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : oid ≠ endpointId) (hObj : st.objects oid = some (.endpoint ep))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects oid = some (.endpoint ep) := by
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    rw [endpointSendCore_preserves_other_objects st st' endpointId oid sender hNe hStep]
    exact hObj
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      simp only [hCore] at hStep
      have hCorePres : pair.2.objects oid = some (.endpoint ep) := by
        rw [endpointSendCore_preserves_other_objects st pair.2 endpointId oid sender hNe hCore]
        exact hObj
      cases effect with
      | blockSender s eid =>
        cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
        | error e => simp [hBlock] at hStep
        | ok stFinal =>
          simp only [hBlock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyBlockEffect_preserves_endpoint pair.2 stFinal s (.blockedOnSend eid) oid ep hCorePres hBlock
      | unblockReceiver r =>
        cases hUnblock : applyUnblockEffect pair.2 r with
        | error e => simp [hUnblock] at hStep
        | ok stFinal =>
          simp only [hUnblock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyUnblockEffect_preserves_endpoint pair.2 stFinal r oid ep hCorePres hUnblock

/-- Public send preserves notification objects. -/
theorem endpointSend_preserves_notification_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ntfn : Notification) (hObj : st.objects oid = some (.notification ntfn))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects oid = some (.notification ntfn) := by
  have hNe : oid ≠ endpointId := by
    intro hEq; subst hEq
    rcases endpointSend_ok_implies_endpoint_object st st' oid sender hStep with ⟨ep, hEpObj⟩
    rw [hObj] at hEpObj; cases hEpObj
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    rw [endpointSendCore_preserves_other_objects st st' endpointId oid sender hNe hStep]
    exact hObj
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      simp only [hCore] at hStep
      have hCorePres : pair.2.objects oid = some (.notification ntfn) := by
        rw [endpointSendCore_preserves_other_objects st pair.2 endpointId oid sender hNe hCore]
        exact hObj
      cases effect with
      | blockSender s eid =>
        cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
        | error e => simp [hBlock] at hStep
        | ok stFinal =>
          simp only [hBlock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyBlockEffect_preserves_notification pair.2 stFinal s (.blockedOnSend eid) oid ntfn hCorePres hBlock
      | unblockReceiver r =>
        cases hUnblock : applyUnblockEffect pair.2 r with
        | error e => simp [hUnblock] at hStep
        | ok stFinal =>
          simp only [hUnblock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyUnblockEffect_preserves_notification pair.2 stFinal r oid ntfn hCorePres hUnblock

/-- Public send result has a well-formed endpoint at endpointId. -/
theorem endpointSend_result_wellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    exact endpointSendCore_result_wellFormed st st' endpointId sender hStep
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      simp only [hCore] at hStep
      rcases endpointSendCore_result_wellFormed st pair.2 endpointId sender hCore with ⟨epNew, hStored, hWf⟩
      cases effect with
      | blockSender s eid =>
        cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
        | error e => simp [hBlock] at hStep
        | ok stFinal =>
          simp only [hBlock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact ⟨epNew, applyBlockEffect_preserves_endpoint pair.2 stFinal s (.blockedOnSend eid)
            endpointId epNew hStored hBlock, hWf⟩
      | unblockReceiver r =>
        cases hUnblock : applyUnblockEffect pair.2 r with
        | error e => simp [hUnblock] at hStep
        | ok stFinal =>
          simp only [hUnblock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact ⟨epNew, applyUnblockEffect_preserves_endpoint pair.2 stFinal r
            endpointId epNew hStored hUnblock, hWf⟩

/-- Public send preserves ipcInvariant. -/
theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  rcases endpointSend_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
      exact ⟨hWfNew, endpointObjectValid_of_queueWellFormed epNew hWfNew⟩
    · -- Backward: endpoint at oid in st' means endpoint at oid in st
      -- Decompose through public operation structure
      have hPre : st.objects oid = some (.endpoint ep) := by
        unfold endpointSend at hStep
        cases hEffect : endpointSendEffect endpointId sender st with
        | none =>
          simp only [hEffect] at hStep
          rw [endpointSendCore_preserves_other_objects st st' endpointId oid sender hEq hStep] at hObj
          exact hObj
        | some effect =>
          simp only [hEffect] at hStep
          cases hCore : endpointSendCore endpointId sender st with
          | error e => simp [hCore] at hStep
          | ok pair =>
            simp only [hCore] at hStep
            have hCorePres : pair.2.objects oid = st.objects oid :=
              endpointSendCore_preserves_other_objects st pair.2 endpointId oid sender hEq hCore
            cases effect with
            | blockSender s eid =>
              cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
              | error e => simp [hBlock] at hStep
              | ok stFinal =>
                simp only [hBlock] at hStep
                have hEqSt : stFinal = st' := by cases hStep; rfl
                subst hEqSt
                rw [← hCorePres]
                exact applyBlockEffect_endpoint_backward pair.2 stFinal s (.blockedOnSend eid) oid ep hBlock hObj
            | unblockReceiver r =>
              cases hUnblock : applyUnblockEffect pair.2 r with
              | error e => simp [hUnblock] at hStep
              | ok stFinal =>
                simp only [hUnblock] at hStep
                have hEqSt : stFinal = st' := by cases hStep; rfl
                subst hEqSt
                rw [← hCorePres]
                exact applyUnblockEffect_endpoint_backward pair.2 stFinal r oid ep hUnblock hObj
      exact hEndpointInv oid ep hPre
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · subst hEq; rw [hStored] at hObj; cases hObj
    · have hPre : st.objects oid = some (.notification ntfn) := by
        unfold endpointSend at hStep
        cases hEffect : endpointSendEffect endpointId sender st with
        | none =>
          simp only [hEffect] at hStep
          rw [endpointSendCore_preserves_other_objects st st' endpointId oid sender hEq hStep] at hObj
          exact hObj
        | some effect =>
          simp only [hEffect] at hStep
          cases hCore : endpointSendCore endpointId sender st with
          | error e => simp [hCore] at hStep
          | ok pair =>
            simp only [hCore] at hStep
            have hCorePres : pair.2.objects oid = st.objects oid :=
              endpointSendCore_preserves_other_objects st pair.2 endpointId oid sender hEq hCore
            cases effect with
            | blockSender s eid =>
              cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
              | error e => simp [hBlock] at hStep
              | ok stFinal =>
                simp only [hBlock] at hStep
                have hEqSt : stFinal = st' := by cases hStep; rfl
                subst hEqSt
                rw [← hCorePres]
                exact applyBlockEffect_notification_backward pair.2 stFinal s (.blockedOnSend eid) oid ntfn hBlock hObj
            | unblockReceiver r =>
              cases hUnblock : applyUnblockEffect pair.2 r with
              | error e => simp [hUnblock] at hStep
              | ok stFinal =>
                simp only [hUnblock] at hStep
                have hEqSt : stFinal = st' := by cases hStep; rfl
                subst hEqSt
                rw [← hCorePres]
                exact applyUnblockEffect_notification_backward pair.2 stFinal r oid ntfn hUnblock hObj
      exact hNotificationInv oid ntfn hPre

-- AwaitReceive and Receive ipcInvariant preservation follow the same pattern.
-- The public operation = Core + applyBlockEffect/applyUnblockEffect.

theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  -- AwaitReceive always applies block effect to receiver
  unfold endpointAwaitReceive at hStep
  cases hCore : endpointAwaitReceiveCore endpointId receiver st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hBlock : applyBlockEffect pair.2 receiver (.blockedOnReceive endpointId) with
    | error e => simp [hBlock] at hStep
    | ok stFinal =>
      simp only [hBlock] at hStep
      have hEq : stFinal = st' := by cases hStep; rfl
      subst hEq
      have hCoreIpc := endpointAwaitReceiveCore_preserves_ipcInvariant st pair.2 endpointId receiver ⟨hEndpointInv, hNotificationInv⟩ hCore
      rcases hCoreIpc with ⟨hEpCore, hNtfnCore⟩
      refine ⟨?_, ?_⟩
      · intro oid ep hObj
        exact hEpCore oid ep (applyBlockEffect_endpoint_backward pair.2 stFinal receiver (.blockedOnReceive endpointId) oid ep hBlock hObj)
      · intro oid ntfn hObj
        exact hNtfnCore oid ntfn (applyBlockEffect_notification_backward pair.2 stFinal receiver (.blockedOnReceive endpointId) oid ntfn hBlock hObj)

theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  unfold endpointReceive at hStep
  cases hCore : endpointReceiveCore endpointId st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hUnblock : applyUnblockEffect pair.2 pair.1 with
    | error e => simp [hUnblock] at hStep
    | ok stFinal =>
      simp only [hUnblock] at hStep
      have ⟨hSenderEq, hStEq⟩ : pair.1 = sender ∧ stFinal = st' := by
        cases hStep; exact ⟨rfl, rfl⟩
      subst hSenderEq; subst hStEq
      have hCoreIpc := endpointReceiveCore_preserves_ipcInvariant st pair.2 endpointId pair.1 ⟨hEndpointInv, hNotificationInv⟩ hCore
      rcases hCoreIpc with ⟨hEpCore, hNtfnCore⟩
      refine ⟨?_, ?_⟩
      · intro oid ep hObj
        exact hEpCore oid ep (applyUnblockEffect_endpoint_backward pair.2 stFinal pair.1 oid ep hUnblock hObj)
      · intro oid ntfn hObj
        exact hNtfnCore oid ntfn (applyUnblockEffect_notification_backward pair.2 stFinal pair.1 oid ntfn hUnblock hObj)

-- ============================================================================
-- Section 12: Public operation preserves schedulerInvariantBundle
--
-- H-09 (WS-E3): The scheduler invariant bundle is preserved through the effects
-- because blockThread maintains queueCurrentConsistent by design and preserves
-- runQueueUnique (filter preserves Nodup). ensureRunnable checks membership
-- before appending, preserving Nodup. Both preserve currentThreadValid since
-- they only modify the scheduler, not the object store.
-- ============================================================================

/-- blockThread preserves schedulerInvariantBundle. -/
private theorem blockThread_preserves_schedulerInvariantBundle
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st) :
    schedulerInvariantBundle (blockThread st tid) := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  unfold blockThread removeRunnable
  dsimp only
  cases hCurrent : st.scheduler.current with
  | none =>
    refine ⟨?_, ?_, ?_⟩
    · simp [queueCurrentConsistent]
    · exact hRunq.sublist List.filter_sublist
    · simp [currentThreadValid]
  | some cur =>
    by_cases hEqCur : cur = tid
    · -- blockThread clears current
      simp only [hEqCur, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · simp [queueCurrentConsistent]
      · exact hRunq.sublist List.filter_sublist
      · simp [currentThreadValid]
    · -- current unchanged
      simp only [show (cur = tid) = False from propext ⟨hEqCur, False.elim⟩, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · -- queueCurrentConsistent: cur was in st.runnable (by hQueue), cur ≠ tid, so cur is in filtered list
        unfold queueCurrentConsistent; dsimp
        rw [List.mem_filter]
        have hCurIn : cur ∈ st.scheduler.runnable := by
          simpa [queueCurrentConsistent, hCurrent] using hQueue
        exact ⟨hCurIn, by rw [decide_eq_true_eq]; exact hEqCur⟩
      · exact hRunq.sublist List.filter_sublist
      · -- currentThreadValid: objects unchanged by blockThread, current = some cur
        unfold currentThreadValid; dsimp
        simpa [currentThreadValid, hCurrent] using hCur

/-- ensureRunnable preserves schedulerInvariantBundle. -/
private theorem ensureRunnable_preserves_schedulerInvariantBundle
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st) :
    schedulerInvariantBundle (ensureRunnable st tid) := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  unfold ensureRunnable
  split
  · exact ⟨hQueue, hRunq, hCur⟩
  · rename_i hNotMem
    refine ⟨?_, ?_, ?_⟩
    · -- queueCurrentConsistent: current unchanged, was in runnable → is in extended runnable
      unfold queueCurrentConsistent; dsimp
      cases hCurrent : st.scheduler.current with
      | none => trivial
      | some cur =>
        have hCurIn : cur ∈ st.scheduler.runnable := by
          simpa [queueCurrentConsistent, hCurrent] using hQueue
        exact List.mem_append_left _ hCurIn
    · -- runQueueUnique: tid ∉ runnable, so append preserves Nodup
      unfold runQueueUnique; dsimp
      rw [List.nodup_append]
      exact ⟨hRunq,
        .cons (fun _ h => absurd h List.not_mem_nil) .nil,
        fun x hx y hy => by
          rw [List.mem_singleton] at hy; subst hy
          exact fun heq => hNotMem (heq ▸ hx)⟩
    · -- currentThreadValid: objects unchanged
      exact hCur

/-- storeTcbIpcState preserves schedulerInvariantBundle (scheduler unchanged, TCB still exists). -/
private theorem storeTcbIpcState_preserves_schedulerInvariantBundle
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : schedulerInvariantBundle st)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  have hSchedEq := storeTcbIpcState_scheduler_eq st st' tid ipc hStep
  refine ⟨?_, ?_, ?_⟩
  · simpa [hSchedEq] using hQueue
  · simpa [hSchedEq] using hRunq
  · cases hCurrent : st.scheduler.current with
    | none =>
      have : st'.scheduler.current = none := by simp [hSchedEq, hCurrent]
      simp [currentThreadValid, this]
    | some cur =>
      have hCurEq : st'.scheduler.current = some cur := by simp [hSchedEq, hCurrent]
      simp [currentThreadValid, hCurEq]
      -- Need: ∃ tcb, st'.objects cur.toObjId = some (.tcb tcb)
      have ⟨tcb, hTcbPre⟩ : ∃ tcb, st.objects cur.toObjId = some (.tcb tcb) := by
        simpa [currentThreadValid, hCurrent] using hCur
      by_cases hNe : cur.toObjId = tid.toObjId
      · -- The current thread IS the modified thread — TCB still exists (just ipcState changed)
        rw [hNe] at hTcbPre ⊢
        exact ⟨{ tcb with ipcState := ipc }, storeTcbIpcState_updates_target st st' tid ipc tcb hTcbPre hStep⟩
      · exact ⟨tcb, by rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc cur.toObjId hNe hStep]; exact hTcbPre⟩

/-- applyBlockEffect preserves schedulerInvariantBundle. -/
private theorem applyBlockEffect_preserves_schedulerInvariantBundle
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : schedulerInvariantBundle st)
    (hStep : applyBlockEffect st tid ipc = .ok st') :
    schedulerInvariantBundle st' := by
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    exact blockThread_preserves_schedulerInvariantBundle stMid tid
      (storeTcbIpcState_preserves_schedulerInvariantBundle st stMid tid ipc hInv hTcb)

/-- applyUnblockEffect preserves schedulerInvariantBundle. -/
private theorem applyUnblockEffect_preserves_schedulerInvariantBundle
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : applyUnblockEffect st tid = .ok st') :
    schedulerInvariantBundle st' := by
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    exact ensureRunnable_preserves_schedulerInvariantBundle stMid tid
      (storeTcbIpcState_preserves_schedulerInvariantBundle st stMid tid .ready hInv hTcb)

theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    exact endpointSendCore_preserves_schedulerInvariantBundle st st' endpointId sender hInv hStep
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      simp only [hCore] at hStep
      have hCoreInv := endpointSendCore_preserves_schedulerInvariantBundle st pair.2 endpointId sender hInv hCore
      cases effect with
      | blockSender s eid =>
        cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
        | error e => simp [hBlock] at hStep
        | ok stFinal =>
          simp only [hBlock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyBlockEffect_preserves_schedulerInvariantBundle pair.2 stFinal s (.blockedOnSend eid) hCoreInv hBlock
      | unblockReceiver r =>
        cases hUnblock : applyUnblockEffect pair.2 r with
        | error e => simp [hUnblock] at hStep
        | ok stFinal =>
          simp only [hUnblock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyUnblockEffect_preserves_schedulerInvariantBundle pair.2 stFinal r hCoreInv hUnblock

theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointAwaitReceive at hStep
  cases hCore : endpointAwaitReceiveCore endpointId receiver st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hBlock : applyBlockEffect pair.2 receiver (.blockedOnReceive endpointId) with
    | error e => simp [hBlock] at hStep
    | ok stFinal =>
      simp only [hBlock] at hStep
      have hEq : stFinal = st' := by cases hStep; rfl
      subst hEq
      exact applyBlockEffect_preserves_schedulerInvariantBundle pair.2 stFinal receiver (.blockedOnReceive endpointId)
        (endpointAwaitReceiveCore_preserves_schedulerInvariantBundle st pair.2 endpointId receiver hInv hCore) hBlock

theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReceive at hStep
  cases hCore : endpointReceiveCore endpointId st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hUnblock : applyUnblockEffect pair.2 pair.1 with
    | error e => simp [hUnblock] at hStep
    | ok stFinal =>
      simp only [hUnblock] at hStep
      have ⟨hSenderEq, hStEq⟩ : pair.1 = sender ∧ stFinal = st' := by cases hStep; exact ⟨rfl, rfl⟩
      subst hSenderEq; subst hStEq
      exact applyUnblockEffect_preserves_schedulerInvariantBundle pair.2 stFinal pair.1
        (endpointReceiveCore_preserves_schedulerInvariantBundle st pair.2 endpointId pair.1 hInv hCore) hUnblock

-- ============================================================================
-- Section 13: Public operation preserves ipcSchedulerContractPredicates
--
-- H-09 (WS-E3): The contract predicates relate TCB ipcState to runnable status.
-- The Core step preserves these (scheduler and TCBs unchanged for non-endpoint IDs).
-- The effects intentionally modify both TCB ipcState and runnable membership
-- in a coordinated way that preserves the predicates:
-- - blockThread removes from runnable, storeTcbIpcState sets blocking ipcState
-- - ensureRunnable adds to runnable, storeTcbIpcState sets .ready ipcState
-- ============================================================================

/-- applyBlockEffect preserves ipcSchedulerContractPredicates. -/
private theorem applyBlockEffect_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : applyBlockEffect st tid ipc = .ok st') :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = blockThread stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    have hSchedPre := storeTcbIpcState_scheduler_eq st stMid tid ipc hTcb
    refine ⟨?_, ?_, ?_⟩
    · -- runnableThreadIpcReady
      intro tid' tcb' hObj hRun
      have ⟨hRunMid, hNe⟩ := blockThread_runnable_subset stMid tid tid' hRun
      -- tid' is runnable in stMid (which has same scheduler as st) and tid' ≠ tid
      have hRunPre : tid' ∈ st.scheduler.runnable := by simpa [hSchedPre] using hRunMid
      -- tid'.toObjId ≠ tid.toObjId (since tid' ≠ tid)
      have hObjIdNe : tid'.toObjId ≠ tid.toObjId := by
        intro h; apply hNe
        cases tid'; cases tid; simp [ThreadId.toObjId, ObjId.ofNat, ThreadId.toNat] at h ⊢; exact h
      -- blockThread preserves objects
      rw [blockThread_preserves_objects] at hObj
      -- TCB at tid' unchanged by storeTcbIpcState (different ObjId)
      have hObjPre : st.objects tid'.toObjId = some (.tcb tcb') := by
        rwa [storeTcbIpcState_preserves_objects_ne st stMid tid ipc tid'.toObjId hObjIdNe hTcb] at hObj
      exact hReady tid' tcb' hObjPre hRunPre
    · -- blockedOnSendNotRunnable
      intro tid' tcb' eid' hObj hBlocked
      rw [blockThread_preserves_objects] at hObj
      intro hRun
      have ⟨hRunMid, hNe⟩ := blockThread_runnable_subset stMid tid tid' hRun
      have hRunPre : tid' ∈ st.scheduler.runnable := by simpa [hSchedPre] using hRunMid
      have hObjIdNe : tid'.toObjId ≠ tid.toObjId := by
        intro h; apply hNe
        cases tid'; cases tid; simp [ThreadId.toObjId, ObjId.ofNat, ThreadId.toNat] at h ⊢; exact h
      have hObjPre : st.objects tid'.toObjId = some (.tcb tcb') := by
        rwa [storeTcbIpcState_preserves_objects_ne st stMid tid ipc tid'.toObjId hObjIdNe hTcb] at hObj
      exact hBlockedSend tid' tcb' eid' hObjPre hBlocked hRunPre
    · -- blockedOnReceiveNotRunnable
      intro tid' tcb' eid' hObj hBlocked
      rw [blockThread_preserves_objects] at hObj
      intro hRun
      have ⟨hRunMid, hNe⟩ := blockThread_runnable_subset stMid tid tid' hRun
      have hRunPre : tid' ∈ st.scheduler.runnable := by simpa [hSchedPre] using hRunMid
      have hObjIdNe : tid'.toObjId ≠ tid.toObjId := by
        intro h; apply hNe
        cases tid'; cases tid; simp [ThreadId.toObjId, ObjId.ofNat, ThreadId.toNat] at h ⊢; exact h
      have hObjPre : st.objects tid'.toObjId = some (.tcb tcb') := by
        rwa [storeTcbIpcState_preserves_objects_ne st stMid tid ipc tid'.toObjId hObjIdNe hTcb] at hObj
      exact hBlockedReceive tid' tcb' eid' hObjPre hBlocked hRunPre

/-- applyUnblockEffect preserves ipcSchedulerContractPredicates. -/
private theorem applyUnblockEffect_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : ipcSchedulerContractPredicates st)
    (hIpc : ipc = .ready)
    (hStep : applyUnblockEffect st tid = .ok st') :
    ipcSchedulerContractPredicates st' := by
  subst hIpc
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : st' = ensureRunnable stMid tid := (Except.ok.inj hStep).symm
    subst hEq
    have hSchedPre := storeTcbIpcState_scheduler_eq st stMid tid .ready hTcb
    refine ⟨?_, ?_, ?_⟩
    · -- runnableThreadIpcReady
      intro tid' tcb' hObj hRun
      rw [ensureRunnable_preserves_objects] at hObj
      rcases ensureRunnable_runnable_cases stMid tid tid' hRun with hOld | hNew
      · -- tid' was already runnable
        have hRunPre : tid' ∈ st.scheduler.runnable := by simpa [hSchedPre] using hOld
        by_cases hNe : tid'.toObjId = tid.toObjId
        · -- tid' and tid have same ObjId — TCB was modified to .ready
          rw [hNe] at hObj
          unfold storeTcbIpcState at hTcb
          cases hLookup : lookupTcb st tid with
          | none =>
            simp [hLookup] at hTcb; subst hTcb
            rw [← hNe] at hObj; exact hReady tid' tcb' hObj hRunPre
          | some tcb =>
            simp only [hLookup] at hTcb
            cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready }) st with
            | error e => simp [hStore] at hTcb
            | ok pair =>
              simp only [hStore] at hTcb
              have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
              subst hPairEq
              rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hObj
              cases hObj; rfl
        · -- tid' has different ObjId — TCB unchanged
          have hObjPre : st.objects tid'.toObjId = some (.tcb tcb') := by
            rwa [storeTcbIpcState_preserves_objects_ne st stMid tid .ready tid'.toObjId hNe hTcb] at hObj
          exact hReady tid' tcb' hObjPre hRunPre
      · -- tid' = tid (the newly runnable thread)
        subst hNew
        -- The TCB at tid in stMid has ipcState = .ready (set by storeTcbIpcState)
        unfold storeTcbIpcState at hTcb
        cases hLookup : lookupTcb st tid' with
        | none =>
          simp [hLookup] at hTcb; subst hTcb
          -- lookupTcb = none contradicts hObj: if st has a TCB at tid'.toObjId, lookupTcb returns some
          exfalso; simp [lookupTcb, hObj] at hLookup
        | some tcb =>
          simp only [hLookup] at hTcb
          cases hStore : storeObject tid'.toObjId (.tcb { tcb with ipcState := .ready }) st with
          | error e => simp [hStore] at hTcb
          | ok pair =>
            simp only [hStore] at hTcb
            have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
            subst hPairEq
            rw [storeObject_objects_eq st pair.2 tid'.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hObj
            cases hObj; rfl
    · -- blockedOnSendNotRunnable
      intro tid' tcb' eid' hObj hBlocked
      rw [ensureRunnable_preserves_objects] at hObj
      by_cases hNe : tid'.toObjId = tid.toObjId
      · -- Same ObjId as modified thread — TCB has .ready state, not .blockedOnSend
        rw [hNe] at hObj
        unfold storeTcbIpcState at hTcb
        cases hLookup : lookupTcb st tid with
        | none => simp [hLookup] at hTcb; subst hTcb
                  exfalso; simp [lookupTcb, hObj] at hLookup
        | some tcb =>
          simp only [hLookup] at hTcb
          cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready }) st with
          | error e => simp [hStore] at hTcb
          | ok pair =>
            simp only [hStore] at hTcb
            have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
            subst hPairEq
            rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hObj
            cases hObj; simp at hBlocked
      · -- Different ObjId — TCB unchanged
        intro hRun
        rcases ensureRunnable_runnable_cases stMid tid tid' hRun with hOld | hNew
        · have hRunPre : tid' ∈ st.scheduler.runnable := by simpa [hSchedPre] using hOld
          have hObjPre : st.objects tid'.toObjId = some (.tcb tcb') := by
            rwa [storeTcbIpcState_preserves_objects_ne st stMid tid .ready tid'.toObjId hNe hTcb] at hObj
          exact hBlockedSend tid' tcb' eid' hObjPre hBlocked hRunPre
        · -- tid' = tid but tid'.toObjId ≠ tid.toObjId — contradiction
          subst hNew; exact absurd rfl hNe
    · -- blockedOnReceiveNotRunnable — same structure as blockedOnSendNotRunnable
      intro tid' tcb' eid' hObj hBlocked
      rw [ensureRunnable_preserves_objects] at hObj
      by_cases hNe : tid'.toObjId = tid.toObjId
      · rw [hNe] at hObj
        unfold storeTcbIpcState at hTcb
        cases hLookup : lookupTcb st tid with
        | none => simp [hLookup] at hTcb; subst hTcb
                  exfalso; simp [lookupTcb, hObj] at hLookup
        | some tcb =>
          simp only [hLookup] at hTcb
          cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready }) st with
          | error e => simp [hStore] at hTcb
          | ok pair =>
            simp only [hStore] at hTcb
            have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
            subst hPairEq
            rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hObj
            cases hObj; simp at hBlocked
      · intro hRun
        rcases ensureRunnable_runnable_cases stMid tid tid' hRun with hOld | hNew
        · have hRunPre : tid' ∈ st.scheduler.runnable := by simpa [hSchedPre] using hOld
          have hObjPre : st.objects tid'.toObjId = some (.tcb tcb') := by
            rwa [storeTcbIpcState_preserves_objects_ne st stMid tid .ready tid'.toObjId hNe hTcb] at hObj
          exact hBlockedReceive tid' tcb' eid' hObjPre hBlocked hRunPre
        · subst hNew; exact absurd rfl hNe

-- Section 14: Public operation _preserves_ipcSchedulerContractPredicates
-- Compose Core proofs + effects frame lemmas following the same pattern
-- as the schedulerInvariantBundle proofs in Section 12.

theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    exact endpointSendCore_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      simp only [hCore] at hStep
      have hCoreInv := endpointSendCore_preserves_ipcSchedulerContractPredicates
        st pair.2 endpointId sender hInv hCore
      cases effect with
      | blockSender s eid =>
        cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
        | error e => simp [hBlock] at hStep
        | ok stFinal =>
          simp only [hBlock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyBlockEffect_preserves_ipcSchedulerContractPredicates
            pair.2 stFinal s (.blockedOnSend eid) hCoreInv hBlock
      | unblockReceiver r =>
        cases hUnblock : applyUnblockEffect pair.2 r with
        | error e => simp [hUnblock] at hStep
        | ok stFinal =>
          simp only [hUnblock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          exact applyUnblockEffect_preserves_ipcSchedulerContractPredicates
            pair.2 stFinal r .ready hCoreInv rfl hUnblock

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  unfold endpointAwaitReceive at hStep
  cases hCore : endpointAwaitReceiveCore endpointId receiver st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hBlock : applyBlockEffect pair.2 receiver (.blockedOnReceive endpointId) with
    | error e => simp [hBlock] at hStep
    | ok stFinal =>
      simp only [hBlock] at hStep
      have hEq : stFinal = st' := by cases hStep; rfl
      subst hEq
      exact applyBlockEffect_preserves_ipcSchedulerContractPredicates pair.2 stFinal
        receiver (.blockedOnReceive endpointId)
        (endpointAwaitReceiveCore_preserves_ipcSchedulerContractPredicates
          st pair.2 endpointId receiver hInv hCore) hBlock

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  unfold endpointReceive at hStep
  cases hCore : endpointReceiveCore endpointId st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hUnblock : applyUnblockEffect pair.2 pair.1 with
    | error e => simp [hUnblock] at hStep
    | ok stFinal =>
      simp only [hUnblock] at hStep
      have ⟨hSenderEq, hStEq⟩ : pair.1 = sender ∧ stFinal = st' := by cases hStep; exact ⟨rfl, rfl⟩
      rw [← hStEq]
      exact applyUnblockEffect_preserves_ipcSchedulerContractPredicates pair.2 stFinal pair.1 .ready
        (endpointReceiveCore_preserves_ipcSchedulerContractPredicates
          st pair.2 endpointId pair.1 hInv hCore) rfl hUnblock

/-- Corollary: endpointSend preserves runnableThreadIpcReady
(extracted from ipcSchedulerContractPredicates for backward compatibility). -/
theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep).1

/-- Corollary: endpointSend preserves blockedOnSendNotRunnable
(extracted from ipcSchedulerContractPredicates for backward compatibility). -/
theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep).2.1

/-- Corollary: endpointSend preserves blockedOnReceiveNotRunnable
(extracted from ipcSchedulerContractPredicates for backward compatibility). -/
theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep).2.2

/-- Corollary: endpointAwaitReceive preserves runnableThreadIpcReady. -/
theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hInv hStep).1

/-- Corollary: endpointAwaitReceive preserves blockedOnSendNotRunnable. -/
theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hInv hStep).2.1

/-- Corollary: endpointAwaitReceive preserves blockedOnReceiveNotRunnable. -/
theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hInv hStep).2.2

/-- Corollary: endpointReceive preserves runnableThreadIpcReady. -/
theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep).1

/-- Corollary: endpointReceive preserves blockedOnSendNotRunnable. -/
theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep).2.1

/-- Corollary: endpointReceive preserves blockedOnReceiveNotRunnable. -/
theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hInv hStep).2.2

-- ============================================================================
-- Section 15: CNode backward preservation
--
-- IPC operations only store `.endpoint` and `.tcb` objects.
-- Any `.cnode` in the post-state was present unchanged in the pre-state.
-- These lemmas support Capability/Invariant.lean's cspaceSlotUnique proofs.
-- ============================================================================

/-- Helper: applyBlockEffect only stores .tcb objects, so CNode lookups are backward-preserved. -/
private theorem applyBlockEffect_cnode_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : applyBlockEffect st tid ipc = .ok st')
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCnode : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  by_cases hEq : oid = tid.toObjId
  · -- oid = tid.toObjId: trace through storeTcbIpcState + blockThread
    unfold applyBlockEffect at hStep
    cases hTcb : storeTcbIpcState st tid ipc with
    | error e => simp [hTcb] at hStep
    | ok stMid =>
      simp only [hTcb] at hStep
      have hBt : blockThread stMid tid = st' := by cases hStep; rfl
      subst hBt
      rw [blockThread_preserves_objects] at hCnode
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st tid with
      | none =>
        -- storeTcbIpcState was a no-op: stMid = st, CNode unchanged
        simp only [hLookup] at hTcb
        have hMidEq : st = stMid := Except.ok.inj hTcb
        rw [← hMidEq] at hCnode
        exact hCnode
      | some tcb =>
        -- storeTcbIpcState stored .tcb at tid.toObjId: contradicts .cnode
        simp only [hLookup] at hTcb
        cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
        | error e => simp [hStore] at hTcb
        | ok pair =>
          simp only [hStore] at hTcb
          have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
          subst hPairEq
          rw [hEq] at hCnode
          rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := ipc }) hStore] at hCnode
          cases hCnode
  · rwa [applyBlockEffect_preserves_objects_ne st st' tid ipc oid hEq hStep] at hCnode

/-- Helper: applyUnblockEffect only stores .tcb objects, so CNode lookups are backward-preserved. -/
private theorem applyUnblockEffect_cnode_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hStep : applyUnblockEffect st tid = .ok st')
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCnode : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  by_cases hEq : oid = tid.toObjId
  · unfold applyUnblockEffect at hStep
    cases hTcb : storeTcbIpcState st tid .ready with
    | error e => simp [hTcb] at hStep
    | ok stMid =>
      simp only [hTcb] at hStep
      have hBt : ensureRunnable stMid tid = st' := by cases hStep; rfl
      subst hBt
      rw [ensureRunnable_preserves_objects] at hCnode
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st tid with
      | none =>
        simp only [hLookup] at hTcb
        have hMidEq : st = stMid := Except.ok.inj hTcb
        rw [← hMidEq] at hCnode
        exact hCnode
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready }) st with
        | error e => simp [hStore] at hTcb
        | ok pair =>
          simp only [hStore] at hTcb
          have hPairEq : pair.snd = stMid := Except.ok.inj hTcb
          subst hPairEq
          rw [hEq] at hCnode
          rw [storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := .ready }) hStore] at hCnode
          cases hCnode
  · rwa [applyUnblockEffect_preserves_objects_ne st st' tid oid hEq hStep] at hCnode

/-- CNode backward preservation for endpointSend.
Any CNode in st' was present unchanged in st. -/
theorem endpointSend_cnode_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCnode : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  unfold endpointSend at hStep
  cases hEffect : endpointSendEffect endpointId sender st with
  | none =>
    simp only [hEffect] at hStep
    -- Core only: single storeObject at endpointId with .endpoint
    rcases endpointSendCore_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
    by_cases hEq : oid = endpointId
    · exfalso; rw [hEq, storeObject_objects_eq st st' endpointId (.endpoint ep') hStore] at hCnode; cases hCnode
    · rwa [storeObject_objects_ne st st' endpointId oid (.endpoint ep') hEq hStore] at hCnode
  | some effect =>
    simp only [hEffect] at hStep
    cases hCore : endpointSendCore endpointId sender st with
    | error e => simp [hCore] at hStep
    | ok pair =>
      simp only [hCore] at hStep
      rcases endpointSendCore_ok_as_storeObject st pair.2 endpointId sender hCore with ⟨ep', hStoreCore⟩
      cases effect with
      | blockSender s eid =>
        cases hBlock : applyBlockEffect pair.2 s (.blockedOnSend eid) with
        | error e => simp [hBlock] at hStep
        | ok stFinal =>
          simp only [hBlock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          have hCnodeMid := applyBlockEffect_cnode_backward pair.2 stFinal s (.blockedOnSend eid) hBlock oid cn hCnode
          by_cases hEq2 : oid = endpointId
          · exfalso; rw [hEq2, storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStoreCore] at hCnodeMid; cases hCnodeMid
          · rwa [storeObject_objects_ne st pair.2 endpointId oid (.endpoint ep') hEq2 hStoreCore] at hCnodeMid
      | unblockReceiver r =>
        cases hUnblock : applyUnblockEffect pair.2 r with
        | error e => simp [hUnblock] at hStep
        | ok stFinal =>
          simp only [hUnblock] at hStep
          have hEq : stFinal = st' := by cases hStep; rfl
          subst hEq
          have hCnodeMid := applyUnblockEffect_cnode_backward pair.2 stFinal r hUnblock oid cn hCnode
          by_cases hEq2 : oid = endpointId
          · exfalso; rw [hEq2, storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStoreCore] at hCnodeMid; cases hCnodeMid
          · rwa [storeObject_objects_ne st pair.2 endpointId oid (.endpoint ep') hEq2 hStoreCore] at hCnodeMid

/-- CNode backward preservation for endpointAwaitReceive. -/
theorem endpointAwaitReceive_cnode_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCnode : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  unfold endpointAwaitReceive at hStep
  cases hCore : endpointAwaitReceiveCore endpointId receiver st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    rcases endpointAwaitReceiveCore_ok_as_storeObject st pair.2 endpointId receiver hCore with ⟨ep', hStoreCore⟩
    cases hBlock : applyBlockEffect pair.2 receiver (.blockedOnReceive endpointId) with
    | error e => simp [hBlock] at hStep
    | ok stFinal =>
      simp only [hBlock] at hStep
      have hEq : stFinal = st' := by cases hStep; rfl
      subst hEq
      have hCnodeMid := applyBlockEffect_cnode_backward pair.2 stFinal receiver (.blockedOnReceive endpointId)
        hBlock oid cn hCnode
      by_cases hEq2 : oid = endpointId
      · exfalso; rw [hEq2, storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStoreCore] at hCnodeMid; cases hCnodeMid
      · rwa [storeObject_objects_ne st pair.2 endpointId oid (.endpoint ep') hEq2 hStoreCore] at hCnodeMid

/-- CNode backward preservation for endpointReceive. -/
theorem endpointReceive_cnode_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCnode : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  unfold endpointReceive at hStep
  cases hCore : endpointReceiveCore endpointId st with
  | error e => simp [hCore] at hStep
  | ok pair =>
    simp only [hCore] at hStep
    cases hUnblock : applyUnblockEffect pair.2 pair.1 with
    | error e => simp [hUnblock] at hStep
    | ok stFinal =>
      simp only [hUnblock] at hStep
      have ⟨hSenderEq, hStEq⟩ : pair.1 = sender ∧ stFinal = st' := by cases hStep; exact ⟨rfl, rfl⟩
      subst hStEq
      rcases endpointReceiveCore_ok_as_storeObject st pair.2 endpointId pair.1 hCore with ⟨ep', hStoreCore⟩
      have hCnodeMid := applyUnblockEffect_cnode_backward pair.2 stFinal pair.1 hUnblock oid cn hCnode
      by_cases hEq2 : oid = endpointId
      · exfalso; rw [hEq2, storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStoreCore] at hCnodeMid; cases hCnodeMid
      · rwa [storeObject_objects_ne st pair.2 endpointId oid (.endpoint ep') hEq2 hStoreCore] at hCnodeMid

-- ============================================================================
-- Section 16: F-12 Notification waiting-list uniqueness invariant (WS-D4, TPI-D06)
-- ============================================================================

/-- The waiting list of the notification at `notifId` contains no duplicate thread IDs.

WS-D4/F-12: This invariant is preserved by the double-wait check in `notificationWait`,
which rejects any attempt to add a thread that is already in the waiting list. -/
def uniqueWaiters (notifId : SeLe4n.ObjId) (st : SystemState) : Prop :=
  ∀ ntfn, st.objects notifId = some (.notification ntfn) → ntfn.waitingThreads.Nodup

/-- Helper: appending a non-member to a Nodup list preserves Nodup. -/
private theorem list_nodup_append_singleton [DecidableEq α]
    (l : List α) (a : α) (hNodup : l.Nodup) (hNotMem : a ∉ l) :
    (l ++ [a]).Nodup := by
  rw [List.nodup_append]
  exact ⟨hNodup,
    .cons (fun _ h => absurd h List.not_mem_nil) .nil,
    fun x hxl y hya => by
      rw [List.mem_singleton] at hya; subst hya
      exact fun heq => hNotMem (heq ▸ hxl)⟩

/-- After `notificationWait` succeeds, the waiting list contains no duplicate thread IDs.

Proof strategy:
- **Badge-consumed path**: the waiting list is reset to `[]`, trivially `Nodup`.
- **Wait path**: the double-wait guard ensures `waiter ∉ ntfn.waitingThreads`,
  so `ntfn.waitingThreads ++ [waiter]` is `Nodup` by `list_nodup_append_singleton`.
  The decomposition lemmas `notificationWait_badge_path_notification` and
  `notificationWait_wait_path_notification` track the notification object through
  `storeTcbIpcState` and `removeRunnable`. -/
theorem notificationWait_preserves_uniqueWaiters
    (waiter : SeLe4n.ThreadId)
    (notifId : SeLe4n.ObjId)
    (st st' : SystemState)
    (result : Option SeLe4n.Badge)
    (hWait : notificationWait notifId waiter st = .ok (result, st'))
    (hUniq : uniqueWaiters notifId st) :
    uniqueWaiters notifId st' := by
  intro ntfn' hLookup
  cases hResult : result with
  | some badge =>
    subst hResult
    rcases notificationWait_badge_path_notification st st' notifId waiter badge hWait with
      ⟨ntfnPost, hPost, hEmpty⟩
    rw [hPost] at hLookup
    cases hLookup
    rw [hEmpty]
    exact List.nodup_nil
  | none =>
    subst hResult
    rcases notificationWait_wait_path_notification st st' notifId waiter hWait with
      ⟨ntfnPre, ntfnPost, hPreObj, _, hNotMem, hPostObj, hAppend⟩
    rw [hPostObj] at hLookup
    cases hLookup
    rw [hAppend]
    have hPreNodup := hUniq ntfnPre hPreObj
    exact list_nodup_append_singleton ntfnPre.waitingThreads waiter hPreNodup hNotMem

end SeLe4n.Kernel
