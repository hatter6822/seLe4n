import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/- Local store/lookup transport lemmas (M3.5 step-5).
These lemmas keep endpoint-transition preservation proofs concrete and non-duplicative. -/

/-- Generic object-store update lemma: writing at `id` makes that slot resolve to `obj`. -/
theorem storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects id = some obj := by
  unfold storeObject at hStore
  cases hStore
  simp

/-- Generic object-store update lemma: writing at `id` preserves all other object lookups. -/
theorem storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold storeObject at hStore
  cases hStore
  simp [hNe]

theorem storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore
  cases hStore
  rfl

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
    (endpointId tid : SeLe4n.ObjId)
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
    (endpointId tid : SeLe4n.ObjId)
    (ep' : Endpoint)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st'))
    (hNotRun : tid ∉ st.scheduler.runnable) :
    tid ∉ st'.scheduler.runnable := by
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore
  simpa [hSchedEq] using hNotRun


/-- Local transition helper: successful send is exactly one endpoint-object update. -/
theorem endpointSend_ok_as_storeObject
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st') := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
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

/-- Local transition helper: successful await-receive is exactly one endpoint-object update. -/
theorem endpointAwaitReceive_ok_as_storeObject
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st') := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
            simp [hObj, hState, hQueue, hWait, storeObject] at hStep
          case idle.nil.none =>
            refine ⟨{ state := .receive, queue := [], waitingReceiver := some receiver }, ?_⟩
            simp [storeObject, hStep]

/-- Local transition helper: successful receive is exactly one endpoint-object update. -/
theorem endpointReceive_ok_as_storeObject
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep', storeObject endpointId (.endpoint ep') st = .ok ((), st') := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
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

/-- Endpoint/object validity component for the active IPC slice.

Ownership discipline for the waiting counterpart identity:
- no waiting receiver implies endpoint is not in `.receive`,
- a waiting receiver id implies endpoint is in `.receive`. -/
def endpointObjectValid (ep : Endpoint) : Prop :=
  match ep.waitingReceiver with
  | none => ep.state ≠ .receive
  | some _ => ep.state = .receive

/-- IPC invariant component bundle for one endpoint object. -/
def endpointInvariant (ep : Endpoint) : Prop :=
  endpointQueueWellFormed ep ∧ endpointObjectValid ep

/-- Global IPC seed invariant entrypoint. -/
def ipcInvariant (st : SystemState) : Prop :=
  ∀ oid ep,
    st.objects oid = some (.endpoint ep) →
    endpointInvariant ep

/-- Scheduler contract predicate #1 for M3.5: runnable threads are explicitly IPC-ready. -/
def runnableThreadIpcReady (st : SystemState) : Prop :=
  ∀ tid tcb,
    st.objects tid = some (.tcb tcb) →
    tid ∈ st.scheduler.runnable →
    tcb.ipcState = .ready

/-- Scheduler contract predicate #2 for M3.5: send-blocked threads are not runnable. -/
def blockedOnSendNotRunnable (st : SystemState) : Prop :=
  ∀ tid tcb endpointId,
    st.objects tid = some (.tcb tcb) →
    tcb.ipcState = .blockedOnSend endpointId →
    tid ∉ st.scheduler.runnable

/-- Scheduler contract predicate #3 for M3.5: receive-blocked threads are not runnable. -/
def blockedOnReceiveNotRunnable (st : SystemState) : Prop :=
  ∀ tid tcb endpointId,
    st.objects tid = some (.tcb tcb) →
    tcb.ipcState = .blockedOnReceive endpointId →
    tid ∉ st.scheduler.runnable

/-- Targeted scheduler/IPC coherence contract for the M3.5 step-3 slice.

This intentionally avoids over-generalized abstraction: it names exactly the three obligations
needed by current endpoint-waiting semantics. -/
def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧
  blockedOnSendNotRunnable st ∧
  blockedOnReceiveNotRunnable st

theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  rcases endpointSend_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb hObj hRun
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hRunOrig : tid ∈ st.scheduler.runnable :=
    runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hRun
  exact hInv tid tcb hObjOrig hRunOrig

theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointSend_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hNotRun : tid ∉ st.scheduler.runnable := hInv tid tcb endpoint hObjOrig hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hNotRun

theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointSend_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hNotRun : tid ∉ st.scheduler.runnable := hInv tid tcb endpoint hObjOrig hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hNotRun

theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointSend_preserves_runnableThreadIpcReady st st' endpointId sender hReady hStep
  · exact endpointSend_preserves_blockedOnSendNotRunnable st st' endpointId sender hBlockedSend hStep
  · exact endpointSend_preserves_blockedOnReceiveNotRunnable st st' endpointId sender hBlockedReceive hStep

theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  rcases endpointAwaitReceive_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  intro tid tcb hObj hRun
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hRunOrig : tid ∈ st.scheduler.runnable :=
    runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hRun
  exact hInv tid tcb hObjOrig hRunOrig

theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointAwaitReceive_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hNotRun : tid ∉ st.scheduler.runnable := hInv tid tcb endpoint hObjOrig hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hNotRun

theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointAwaitReceive_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hNotRun : tid ∉ st.scheduler.runnable := hInv tid tcb endpoint hObjOrig hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hNotRun

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointAwaitReceive_preserves_runnableThreadIpcReady st st' endpointId receiver hReady hStep
  · exact endpointAwaitReceive_preserves_blockedOnSendNotRunnable st st' endpointId receiver hBlockedSend hStep
  · exact endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable st st' endpointId receiver hBlockedReceive hStep

theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' := by
  rcases endpointReceive_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb hObj hRun
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hRunOrig : tid ∈ st.scheduler.runnable :=
    runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hRun
  exact hInv tid tcb hObjOrig hRunOrig

theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointReceive_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hNotRun : tid ∉ st.scheduler.runnable := hInv tid tcb endpoint hObjOrig hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hNotRun

theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointReceive_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  intro tid tcb endpoint hObj hBlocked
  have hObjOrig : st.objects tid = some (.tcb tcb) :=
    tcb_lookup_of_endpoint_store st st' endpointId tid tcb ep' hStore hObj
  have hNotRun : tid ∉ st.scheduler.runnable := hInv tid tcb endpoint hObjOrig hBlocked
  exact not_runnable_membership_of_endpoint_store st st' endpointId tid ep' hStore hNotRun

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointReceive_preserves_runnableThreadIpcReady st st' endpointId sender hReady hStep
  · exact endpointReceive_preserves_blockedOnSendNotRunnable st st' endpointId sender hBlockedSend hStep
  · exact endpointReceive_preserves_blockedOnReceiveNotRunnable st st' endpointId sender hBlockedReceive hStep

theorem endpointObjectValid_of_queueWellFormed
    (ep : Endpoint)
    (hWf : endpointQueueWellFormed ep) :
    endpointObjectValid ep := by
  cases hState : ep.state <;> cases hWait : ep.waitingReceiver <;>
    simp [endpointQueueWellFormed, endpointObjectValid, hState, hWait] at hWf ⊢

theorem endpointSend_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
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

theorem endpointAwaitReceive_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
            simp [hObj, hState, hQueue, hWait, storeObject] at hStep
          case idle.nil.none =>
            refine ⟨{ state := .receive, queue := [], waitingReceiver := some receiver }, ?_, ?_⟩
            · cases hStep
              simp
            · simp [endpointQueueWellFormed]

theorem endpointReceive_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
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

theorem endpointSend_preserves_other_objects
    (st st' : SystemState)
    (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hNe : oid ≠ endpointId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  rcases endpointSend_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  exact storeObject_objects_ne st st' endpointId oid (.endpoint ep') hNe hStore

theorem endpointAwaitReceive_preserves_other_objects
    (st st' : SystemState)
    (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hNe : oid ≠ endpointId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  rcases endpointAwaitReceive_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  exact storeObject_objects_ne st st' endpointId oid (.endpoint ep') hNe hStore

theorem endpointReceive_preserves_other_objects
    (st st' : SystemState)
    (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hNe : oid ≠ endpointId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st'.objects oid = st.objects oid := by
  rcases endpointReceive_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  exact storeObject_objects_ne st st' endpointId oid (.endpoint ep') hNe hStore

theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcInvariant st' := by
  intro oid ep hObj
  rcases endpointSend_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
  by_cases hEq : oid = endpointId
  · subst hEq
    have hCast : ep = epNew := by
      rw [hStored] at hObj
      cases hObj
      rfl
    have hObjValidNew : endpointObjectValid epNew :=
      endpointObjectValid_of_queueWellFormed epNew hWfNew
    simpa [endpointInvariant, hCast] using And.intro hWfNew hObjValidNew
  · have hUnchanged : st'.objects oid = st.objects oid := by
      exact endpointSend_preserves_other_objects st st' endpointId oid sender hEq hStep
    have hOrig : st.objects oid = some (.endpoint ep) := by simpa [hUnchanged] using hObj
    exact hInv oid ep hOrig

theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  intro oid ep hObj
  rcases endpointAwaitReceive_result_wellFormed st st' endpointId receiver hStep with ⟨epNew, hStored, hWfNew⟩
  by_cases hEq : oid = endpointId
  · subst hEq
    have hCast : ep = epNew := by
      rw [hStored] at hObj
      cases hObj
      rfl
    have hObjValidNew : endpointObjectValid epNew :=
      endpointObjectValid_of_queueWellFormed epNew hWfNew
    simpa [endpointInvariant, hCast] using And.intro hWfNew hObjValidNew
  · have hUnchanged : st'.objects oid = st.objects oid := by
      exact endpointAwaitReceive_preserves_other_objects st st' endpointId oid receiver hEq hStep
    have hOrig : st.objects oid = some (.endpoint ep) := by simpa [hUnchanged] using hObj
    exact hInv oid ep hOrig

theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcInvariant st' := by
  intro oid ep hObj
  rcases endpointReceive_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
  by_cases hEq : oid = endpointId
  · subst hEq
    have hCast : ep = epNew := by
      rw [hStored] at hObj
      cases hObj
      rfl
    have hObjValidNew : endpointObjectValid epNew :=
      endpointObjectValid_of_queueWellFormed epNew hWfNew
    simpa [endpointInvariant, hCast] using And.intro hWfNew hObjValidNew
  · have hUnchanged : st'.objects oid = st.objects oid := by
      exact endpointReceive_preserves_other_objects st st' endpointId oid sender hEq hStep
    have hOrig : st.objects oid = some (.endpoint ep) := by simpa [hUnchanged] using hObj
    exact hInv oid ep hOrig

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
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | endpoint ep =>
          refine ⟨ep, rfl⟩

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
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | endpoint ep =>
          refine ⟨ep, rfl⟩

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
      | tcb tcb => simp [hObj] at hStep
      | cnode cn => simp [hObj] at hStep
      | endpoint ep =>
          refine ⟨ep, rfl⟩

theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  rcases endpointSend_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore
  have hCurEq : st'.scheduler.current = st.scheduler.current := by simp [hSchedEq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hSchedEq] using hQueue
  · simpa [hSchedEq] using hRunq
  · cases hCurrent : st.scheduler.current with
    | none =>
        simp [currentThreadValid, hCurEq, hCurrent]
    | some tid =>
        have hCurSome : ∃ tcb : TCB, st.objects tid = some (.tcb tcb) := by
          simpa [currentThreadValid, hCurrent] using hCur
        rcases hCurSome with ⟨tcb, hTcbObj⟩
        have hTidNe : tid ≠ endpointId := by
          intro hEq
          subst hEq
          rcases endpointSend_ok_implies_endpoint_object st st' tid sender hStep with ⟨ep, hEpObj⟩
          rw [hEpObj] at hTcbObj
          cases hTcbObj
        have hTcbObj' : st'.objects tid = some (.tcb tcb) := by
          rw [endpointSend_preserves_other_objects st st' endpointId tid sender hTidNe hStep]
          exact hTcbObj
        simp [currentThreadValid, hCurEq, hCurrent, hTcbObj']

theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  rcases endpointAwaitReceive_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore
  have hCurEq : st'.scheduler.current = st.scheduler.current := by simp [hSchedEq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hSchedEq] using hQueue
  · simpa [hSchedEq] using hRunq
  · cases hCurrent : st.scheduler.current with
    | none =>
        simp [currentThreadValid, hCurEq, hCurrent]
    | some tid =>
        have hCurSome : ∃ tcb : TCB, st.objects tid = some (.tcb tcb) := by
          simpa [currentThreadValid, hCurrent] using hCur
        rcases hCurSome with ⟨tcb, hTcbObj⟩
        have hTidNe : tid ≠ endpointId := by
          intro hEq
          subst hEq
          rcases endpointAwaitReceive_ok_implies_endpoint_object st st' tid receiver hStep with ⟨ep, hEpObj⟩
          rw [hEpObj] at hTcbObj
          cases hTcbObj
        have hTcbObj' : st'.objects tid = some (.tcb tcb) := by
          rw [endpointAwaitReceive_preserves_other_objects st st' endpointId tid receiver hTidNe hStep]
          exact hTcbObj
        simp [currentThreadValid, hCurEq, hCurrent, hTcbObj']

theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  rcases endpointReceive_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' endpointId (.endpoint ep') hStore
  have hCurEq : st'.scheduler.current = st.scheduler.current := by simp [hSchedEq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hSchedEq] using hQueue
  · simpa [hSchedEq] using hRunq
  · cases hCurrent : st.scheduler.current with
    | none =>
        simp [currentThreadValid, hCurEq, hCurrent]
    | some tid =>
        have hCurSome : ∃ tcb : TCB, st.objects tid = some (.tcb tcb) := by
          simpa [currentThreadValid, hCurrent] using hCur
        rcases hCurSome with ⟨tcb, hTcbObj⟩
        have hTidNe : tid ≠ endpointId := by
          intro hEq
          subst hEq
          rcases endpointReceive_ok_implies_endpoint_object st st' tid sender hStep with ⟨ep, hEpObj⟩
          rw [hEpObj] at hTcbObj
          cases hTcbObj
        have hTcbObj' : st'.objects tid = some (.tcb tcb) := by
          rw [endpointReceive_preserves_other_objects st st' endpointId tid sender hTidNe hStep]
          exact hTcbObj
        simp [currentThreadValid, hCurEq, hCurrent, hTcbObj']


end SeLe4n.Kernel
