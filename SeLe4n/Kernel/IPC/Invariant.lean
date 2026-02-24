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

All theorems in this module are substantive: they prove invariant preservation over
state that is actually modified by successful endpoint operations. There are no
error-case preservation theorems in this module.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- ThreadId.toObjId is injective: equal ObjIds imply equal ThreadIds. -/
private theorem threadId_toObjId_inj {a b : SeLe4n.ThreadId}
    (h : a.toObjId = b.toObjId) : a = b := by
  cases a; cases b
  simp [SeLe4n.ThreadId.toObjId, SeLe4n.ObjId.ofNat, SeLe4n.ThreadId.toNat] at h
  subst h; rfl

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


/-- H-09/WS-E3: Successful send contains an intermediate storeObject for the endpoint,
    followed by storeTcbIpcState and removeRunnable on blocking paths, or just a
    storeObject on the handshake path. The final state's endpoint object is determined
    by this storeObject step. -/
theorem endpointSend_preserves_endpoint_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (epOther : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : epOther ≠ endpointId)
    (hPre : st.objects epOther = some (.endpoint ep)) :
    st'.objects epOther = some (.endpoint ep) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state with
      | idle =>
        simp only [hObj, hState] at hStep
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 sender _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have h1 := storeObject_objects_ne st pair.2 endpointId epOther _ hNe hStore
            have h2 := storeTcbIpcState_preserves_endpoint pair.2 st2 sender _ epOther ep
              (h1 ▸ hPre) hTcb
            rw [removeRunnable_preserves_objects st2 sender]; exact h2
      | send =>
        simp only [hObj, hState] at hStep
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 sender _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have h1 := storeObject_objects_ne st pair.2 endpointId epOther _ hNe hStore
            have h2 := storeTcbIpcState_preserves_endpoint pair.2 st2 sender _ epOther ep
              (h1 ▸ hPre) hTcb
            rw [removeRunnable_preserves_objects st2 sender]; exact h2
      | receive =>
        cases hQueue : epOld.queue <;> cases hWait : epOld.waitingReceiver <;>
          simp [hObj, hState, hQueue, hWait] at hStep
        case nil.some receiver =>
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            exact storeObject_objects_ne st st' endpointId epOther _ hNe hStore ▸ hPre

/-- H-09/WS-E3: Successful await-receive preserves endpoint objects at other IDs. -/
theorem endpointAwaitReceive_preserves_endpoint_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (epOther : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : epOther ≠ endpointId)
    (hPre : st.objects epOther = some (.endpoint ep)) :
    st'.objects epOther = some (.endpoint ep) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> cases hQueue : epOld.queue <;>
        cases hWait : epOld.waitingReceiver <;>
        simp [hObj, hState, hQueue, hWait] at hStep
      case idle.nil.none =>
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 receiver _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have h1 := storeObject_objects_ne st pair.2 endpointId epOther _ hNe hStore
            have h2 := storeTcbIpcState_preserves_endpoint pair.2 st2 receiver _ epOther ep
              (h1 ▸ hPre) hTcb
            rw [removeRunnable_preserves_objects st2 receiver]; exact h2

/-- H-09/WS-E3: Successful receive preserves endpoint objects at other IDs. -/
theorem endpointReceive_preserves_endpoint_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (epOther : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : epOther ≠ endpointId)
    (hPre : st.objects epOther = some (.endpoint ep)) :
    st'.objects epOther = some (.endpoint ep) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> simp [hObj, hState] at hStep
      case send =>
        cases hQueue : epOld.queue with
        | nil =>
          cases hWait : epOld.waitingReceiver <;> simp [hQueue, hWait] at hStep
        | cons head tail =>
          cases hWait : epOld.waitingReceiver with
          | none =>
            simp only [hQueue, hWait] at hStep
            revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              intro hStep; revert hStep
              cases hTcb : storeTcbIpcState pair.2 head .ready with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have h1 := storeObject_objects_ne st pair.2 endpointId epOther _ hNe hStore
                have h2 := storeTcbIpcState_preserves_endpoint pair.2 st2 head .ready epOther ep
                  (h1 ▸ hPre) hTcb
                rw [ensureRunnable_preserves_objects st2 head]; exact h2
          | some _ => simp [hQueue, hWait] at hStep

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

/-- Targeted scheduler/IPC coherence contract for the M3.5 step-3 slice.

This intentionally avoids over-generalized abstraction: it names exactly the three obligations
needed by current endpoint-waiting semantics. -/
def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧
  blockedOnSendNotRunnable st ∧
  blockedOnReceiveNotRunnable st

/-- H-09/WS-E3: Endpoint send preserves runnableThreadIpcReady.

    In the blocking case (idle/send), the sender is removed from runnable and has
    ipcState set to blockedOnSend. All other threads' objects and runnable status
    are unchanged, so the pre-state invariant transfers. In the handshake case
    (receive→idle), it is a pure endpoint store with no IPC state changes. -/
theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedRecv⟩
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      cases hState : ep.state with
      | idle | send =>
        all_goals (
          simp only [hObj, hState] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            intro hStep; revert hStep
            cases hTcb : storeTcbIpcState pair.2 sender _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              have hSchedEp := storeObject_scheduler_eq st pair.2 endpointId _ hStore
              have hSchedTcb := storeTcbIpcState_scheduler_eq pair.2 st2 sender _ hTcb
              refine ⟨?_, ?_, ?_⟩
              -- runnableThreadIpcReady
              · intro tid tcb hObjTid hRunTid
                simp [removeRunnable] at hRunTid
                have hRunSt : tid ∈ st.scheduler.runnable := by
                  rw [hSchedTcb, hSchedEp] at hRunTid; exact hRunTid.1
                have hNeSender : tid ≠ sender := by
                  rw [hSchedTcb, hSchedEp] at hRunTid; exact hRunTid.2
                have hObjTidSt2 : st2.objects tid.toObjId = some (.tcb tcb) := by
                  rwa [removeRunnable_preserves_objects st2 sender] at hObjTid
                have hTidObjNe : tid.toObjId ≠ sender.toObjId := by
                  intro h; exact hNeSender (threadId_toObjId_inj h)
                have hObjTidPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                  rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 sender _ tid.toObjId hTidObjNe hTcb] at hObjTidSt2
                by_cases hTidEnd : tid.toObjId = endpointId
                · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjTidPair
                  cases hObjTidPair
                · rw [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjTidPair
                  exact hReady tid tcb hObjTidPair hRunSt
              -- blockedOnSendNotRunnable
              · intro tid tcb eid hObjTid hBlocked
                intro hAbs; rw [removeRunnable_mem_iff] at hAbs
                by_cases hTidEq : tid = sender
                · exact hAbs.2 hTidEq
                · have hTidObjNe : tid.toObjId ≠ sender.toObjId := by
                    intro h; apply hTidEq
                    exact threadId_toObjId_inj h
                  have hObjTidSt2 : st2.objects tid.toObjId = some (.tcb tcb) := by
                    rwa [removeRunnable_preserves_objects st2 sender] at hObjTid
                  have hObjTidPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                    rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 sender _ tid.toObjId hTidObjNe hTcb] at hObjTidSt2
                  have hObjTidSt : st.objects tid.toObjId = some (.tcb tcb) := by
                    by_cases hTidEnd : tid.toObjId = endpointId
                    · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjTidPair; cases hObjTidPair
                    · rwa [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjTidPair
                  rw [hSchedTcb, hSchedEp] at hAbs
                  exact hBlockedSend tid tcb eid hObjTidSt hBlocked hAbs.1
              -- blockedOnReceiveNotRunnable
              · intro tid tcb eid hObjTid hBlocked
                intro hAbs; rw [removeRunnable_mem_iff] at hAbs
                by_cases hTidEq : tid = sender
                · exact hAbs.2 hTidEq
                · have hTidObjNe : tid.toObjId ≠ sender.toObjId := by
                    intro h; apply hTidEq
                    exact threadId_toObjId_inj h
                  have hObjTidSt2 : st2.objects tid.toObjId = some (.tcb tcb) := by
                    rwa [removeRunnable_preserves_objects st2 sender] at hObjTid
                  have hObjTidPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                    rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 sender _ tid.toObjId hTidObjNe hTcb] at hObjTidSt2
                  have hObjTidSt : st.objects tid.toObjId = some (.tcb tcb) := by
                    by_cases hTidEnd : tid.toObjId = endpointId
                    · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjTidPair; cases hObjTidPair
                    · rwa [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjTidPair
                  rw [hSchedTcb, hSchedEp] at hAbs
                  exact hBlockedRecv tid tcb eid hObjTidSt hBlocked hAbs.1)
      | receive =>
        cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
          simp [hObj, hState, hQueue, hWait] at hStep
        case nil.some receiver =>
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            have hSchedEq := storeObject_scheduler_eq st st' endpointId _ hStore
            refine ⟨?_, ?_, ?_⟩
            · intro tid tcb hObjTid hRun
              rw [hSchedEq] at hRun
              by_cases hTidEnd : tid.toObjId = endpointId
              · rw [hTidEnd, storeObject_objects_eq st st' endpointId _ hStore] at hObjTid
                cases hObjTid
              · rw [storeObject_objects_ne st st' endpointId tid.toObjId _ hTidEnd hStore] at hObjTid
                exact hReady tid tcb hObjTid hRun
            · intro tid tcb eid hObjTid hBlocked
              rw [hSchedEq]
              by_cases hTidEnd : tid.toObjId = endpointId
              · rw [hTidEnd, storeObject_objects_eq st st' endpointId _ hStore] at hObjTid
                cases hObjTid
              · rw [storeObject_objects_ne st st' endpointId tid.toObjId _ hTidEnd hStore] at hObjTid
                exact hBlockedSend tid tcb eid hObjTid hBlocked
            · intro tid tcb eid hObjTid hBlocked
              rw [hSchedEq]
              by_cases hTidEnd : tid.toObjId = endpointId
              · rw [hTidEnd, storeObject_objects_eq st st' endpointId _ hStore] at hObjTid
                cases hObjTid
              · rw [storeObject_objects_ne st st' endpointId tid.toObjId _ hTidEnd hStore] at hObjTid
                exact hBlockedRecv tid tcb eid hObjTid hBlocked

/-- Corollary: endpoint send preserves the runnableThreadIpcReady component. -/
theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hBlockedSend : blockedOnSendNotRunnable st)
    (hBlockedRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates
    st st' endpointId sender ⟨hInv, hBlockedSend, hBlockedRecv⟩ hStep).1

/-- Corollary: endpoint send preserves the blockedOnSendNotRunnable component. -/
theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates
    st st' endpointId sender hInv hStep).2.1

/-- Corollary: endpoint send preserves the blockedOnReceiveNotRunnable component. -/
theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates
    st st' endpointId sender hInv hStep).2.2

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedRecv⟩
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      cases hState : ep.state <;> cases hQueue : ep.queue <;>
        cases hWait : ep.waitingReceiver <;>
        simp [hObj, hState, hQueue, hWait] at hStep
      case idle.nil.none =>
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 receiver _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hSchedEp := storeObject_scheduler_eq st pair.2 endpointId _ hStore
            have hSchedTcb := storeTcbIpcState_scheduler_eq pair.2 st2 receiver _ hTcb
            refine ⟨?_, ?_, ?_⟩
            -- runnableThreadIpcReady
            · intro tid tcb hObjTid hRunTid
              rw [removeRunnable_mem_iff] at hRunTid
              have hRunSt : tid ∈ st.scheduler.runnable := by
                rw [hSchedTcb, hSchedEp] at hRunTid; exact hRunTid.1
              have hNeReceiver : tid ≠ receiver := hRunTid.2
              have hTidObjNe : tid.toObjId ≠ receiver.toObjId := by
                intro h; apply hNeReceiver
                exact threadId_toObjId_inj h
              have hObjTidSt2 : st2.objects tid.toObjId = some (.tcb tcb) := by
                rwa [removeRunnable_preserves_objects st2 receiver] at hObjTid
              have hObjTidPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 receiver _ tid.toObjId hTidObjNe hTcb] at hObjTidSt2
              by_cases hTidEnd : tid.toObjId = endpointId
              · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjTidPair; cases hObjTidPair
              · rw [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjTidPair
                exact hReady tid tcb hObjTidPair hRunSt
            -- blockedOnSendNotRunnable
            · intro tid tcb eid hObjTid hBlocked
              intro hAbs; rw [removeRunnable_mem_iff] at hAbs
              by_cases hTidEq : tid = receiver
              · exact hAbs.2 hTidEq
              · have hTidObjNe : tid.toObjId ≠ receiver.toObjId := by
                  intro h; apply hTidEq
                  exact threadId_toObjId_inj h
                have hObjSt : st.objects tid.toObjId = some (.tcb tcb) := by
                  have h1 : st2.objects tid.toObjId = some (.tcb tcb) := by
                    rwa [removeRunnable_preserves_objects st2 receiver] at hObjTid
                  have h2 := storeTcbIpcState_preserves_objects_ne pair.2 st2 receiver _ tid.toObjId hTidObjNe hTcb
                  rw [h2] at h1
                  by_cases hTidEnd : tid.toObjId = endpointId
                  · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at h1; cases h1
                  · rwa [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at h1
                rw [hSchedTcb, hSchedEp] at hAbs
                exact hBlockedSend tid tcb eid hObjSt hBlocked hAbs.1
            -- blockedOnReceiveNotRunnable
            · intro tid tcb eid hObjTid hBlocked
              intro hAbs; rw [removeRunnable_mem_iff] at hAbs
              by_cases hTidEq : tid = receiver
              · exact hAbs.2 hTidEq
              · have hTidObjNe : tid.toObjId ≠ receiver.toObjId := by
                  intro h; apply hTidEq
                  exact threadId_toObjId_inj h
                have hObjSt : st.objects tid.toObjId = some (.tcb tcb) := by
                  have h1 : st2.objects tid.toObjId = some (.tcb tcb) := by
                    rwa [removeRunnable_preserves_objects st2 receiver] at hObjTid
                  have h2 := storeTcbIpcState_preserves_objects_ne pair.2 st2 receiver _ tid.toObjId hTidObjNe hTcb
                  rw [h2] at h1
                  by_cases hTidEnd : tid.toObjId = endpointId
                  · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at h1; cases h1
                  · rwa [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at h1
                rw [hSchedTcb, hSchedEp] at hAbs
                exact hBlockedRecv tid tcb eid hObjSt hBlocked hAbs.1

/-- Corollary: endpoint await-receive preserves runnableThreadIpcReady. -/
theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    st st' endpointId receiver hInv hStep).1

/-- Corollary: endpoint await-receive preserves blockedOnSendNotRunnable. -/
theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    st st' endpointId receiver hInv hStep).2.1

/-- Corollary: endpoint await-receive preserves blockedOnReceiveNotRunnable. -/
theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    st st' endpointId receiver hInv hStep).2.2

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedRecv⟩
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      cases hState : ep.state <;> simp [hObj, hState] at hStep
      case send =>
        cases hQueue : ep.queue with
        | nil => cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
        | cons head tail =>
          cases hWait : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWait] at hStep; revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              intro hStep; revert hStep
              cases hTcb : storeTcbIpcState pair.2 head .ready with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨hSenderEq, hEq⟩; subst hEq; subst hSenderEq
                have hSchedEp := storeObject_scheduler_eq st pair.2 endpointId _ hStore
                have hSchedTcb := storeTcbIpcState_scheduler_eq pair.2 st2 head _ hTcb
                refine ⟨?_, ?_, ?_⟩
                -- runnableThreadIpcReady
                · intro tid tcb hObjTid hRunTid
                  rw [ensureRunnable_mem_iff] at hRunTid
                  rw [ensureRunnable_preserves_objects] at hObjTid
                  rcases hRunTid with hRunSt2 | hTidEqSender
                  · -- tid was already runnable in st2
                    rw [hSchedTcb, hSchedEp] at hRunSt2
                    by_cases hTidEq : tid = head
                    · -- tid = head: head's TCB was set to .ready by storeTcbIpcState
                      subst hTidEq
                      rcases storeTcbIpcState_objects_at pair.2 st2 tid .ready hTcb with
                        ⟨tcbOld, _, hPost⟩ | ⟨_, hStEq⟩
                      · rw [hPost] at hObjTid; cases hObjTid; rfl
                      · subst hStEq
                        by_cases hSendEnd : tid.toObjId = endpointId
                        · rw [hSendEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjTid; cases hObjTid
                        · rw [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hSendEnd hStore] at hObjTid
                          exact hReady tid tcb hObjTid hRunSt2
                    · -- tid ≠ head: backward to pre-state
                      have hTidObjNe : tid.toObjId ≠ head.toObjId := by
                        intro h; apply hTidEq
                        exact threadId_toObjId_inj h
                      have hObjPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                        rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 head .ready tid.toObjId hTidObjNe hTcb] at hObjTid
                      by_cases hTidEnd : tid.toObjId = endpointId
                      · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjPair; cases hObjPair
                      · rw [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjPair
                        exact hReady tid tcb hObjPair hRunSt2
                  · -- tid = head (added by ensureRunnable): head's TCB has .ready
                    subst hTidEqSender
                    rcases storeTcbIpcState_objects_at pair.2 st2 tid .ready hTcb with
                      ⟨tcbOld, _, hPost⟩ | ⟨hLookupNone, hStEq⟩
                    · rw [hPost] at hObjTid; cases hObjTid; rfl
                    · subst hStEq; exfalso; simp [lookupTcb, hObjTid] at hLookupNone
                -- blockedOnSendNotRunnable
                · intro tid tcb eid hObjTid hBlocked
                  rw [ensureRunnable_preserves_objects] at hObjTid
                  by_cases hTidEq : tid = head
                  · -- tid = head: head's TCB has ipcState = .ready, not blockedOnSend
                    subst hTidEq
                    rcases storeTcbIpcState_objects_at pair.2 st2 tid .ready hTcb with
                      ⟨_, _, hPost⟩ | ⟨hLookupNone, hStEq⟩
                    · rw [hPost] at hObjTid; cases hObjTid; cases hBlocked
                    · subst hStEq; exfalso; simp [lookupTcb, hObjTid] at hLookupNone
                  · -- tid ≠ head: backward to pre-state, use pre invariant
                    have hTidObjNe : tid.toObjId ≠ head.toObjId := by
                      intro h; apply hTidEq
                      exact threadId_toObjId_inj h
                    have hObjPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                      rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 head .ready tid.toObjId hTidObjNe hTcb] at hObjTid
                    have hObjSt : st.objects tid.toObjId = some (.tcb tcb) := by
                      by_cases hTidEnd : tid.toObjId = endpointId
                      · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjPair; cases hObjPair
                      · rwa [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjPair
                    have hNotRunSt : tid ∉ st.scheduler.runnable := hBlockedSend tid tcb eid hObjSt hBlocked
                    intro hAbs; rw [ensureRunnable_mem_iff] at hAbs
                    rcases hAbs with hRunSt2 | hTidSender
                    · rw [hSchedTcb, hSchedEp] at hRunSt2; exact hNotRunSt hRunSt2
                    · exact hTidEq hTidSender
                -- blockedOnReceiveNotRunnable
                · intro tid tcb eid hObjTid hBlocked
                  rw [ensureRunnable_preserves_objects] at hObjTid
                  by_cases hTidEq : tid = head
                  · subst hTidEq
                    rcases storeTcbIpcState_objects_at pair.2 st2 tid .ready hTcb with
                      ⟨_, _, hPost⟩ | ⟨hLookupNone, hStEq⟩
                    · rw [hPost] at hObjTid; cases hObjTid; cases hBlocked
                    · subst hStEq; exfalso; simp [lookupTcb, hObjTid] at hLookupNone
                  · have hTidObjNe : tid.toObjId ≠ head.toObjId := by
                      intro h; apply hTidEq
                      exact threadId_toObjId_inj h
                    have hObjPair : pair.2.objects tid.toObjId = some (.tcb tcb) := by
                      rwa [storeTcbIpcState_preserves_objects_ne pair.2 st2 head .ready tid.toObjId hTidObjNe hTcb] at hObjTid
                    have hObjSt : st.objects tid.toObjId = some (.tcb tcb) := by
                      by_cases hTidEnd : tid.toObjId = endpointId
                      · rw [hTidEnd, storeObject_objects_eq st pair.2 endpointId _ hStore] at hObjPair; cases hObjPair
                      · rwa [storeObject_objects_ne st pair.2 endpointId tid.toObjId _ hTidEnd hStore] at hObjPair
                    have hNotRunSt : tid ∉ st.scheduler.runnable := hBlockedRecv tid tcb eid hObjSt hBlocked
                    intro hAbs; rw [ensureRunnable_mem_iff] at hAbs
                    rcases hAbs with hRunSt2 | hTidSender
                    · rw [hSchedTcb, hSchedEp] at hRunSt2; exact hNotRunSt hRunSt2
                    · exact hTidEq hTidSender
          | some _ => simp [hQueue, hWait] at hStep

/-- Corollary: endpoint receive preserves runnableThreadIpcReady. -/
theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates
    st st' endpointId sender hInv hStep).1

/-- Corollary: endpoint receive preserves blockedOnSendNotRunnable. -/
theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates
    st st' endpointId sender hInv hStep).2.1

/-- Corollary: endpoint receive preserves blockedOnReceiveNotRunnable. -/
theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates
    st st' endpointId sender hInv hStep).2.2

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
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state with
          | idle =>
              simp only [hObj, hState] at hStep
              revert hStep
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep; revert hStep
                cases hTcb : storeTcbIpcState pair.2 sender _ with
                | error e => simp
                | ok st2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  let ep' : Endpoint := { state := .send, queue := [sender], waitingReceiver := none }
                  have hStored := storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStore
                  have hPreserved := storeTcbIpcState_preserves_endpoint pair.2 st2 sender _ endpointId ep' hStored hTcb
                  refine ⟨ep', ?_, ?_⟩
                  · rw [removeRunnable_preserves_objects st2 sender]; exact hPreserved
                  · simp [endpointQueueWellFormed, ep']
          | send =>
              simp only [hObj, hState] at hStep
              revert hStep
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep; revert hStep
                cases hTcb : storeTcbIpcState pair.2 sender _ with
                | error e => simp
                | ok st2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  let ep' : Endpoint := { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }
                  have hStored := storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStore
                  have hPreserved := storeTcbIpcState_preserves_endpoint pair.2 st2 sender _ endpointId ep' hStored hTcb
                  refine ⟨ep', ?_, ?_⟩
                  · rw [removeRunnable_preserves_objects st2 sender]; exact hPreserved
                  · simp [endpointQueueWellFormed, ep']
          | receive =>
              cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
                simp [hObj, hState, hQueue, hWait] at hStep
              case nil.some receiver =>
                revert hStep
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  refine ⟨{ state := .idle, queue := [], waitingReceiver := none }, ?_, ?_⟩
                  · exact storeObject_objects_eq st st' endpointId _ hStore
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
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          cases hState : ep.state <;> cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
            simp [hObj, hState, hQueue, hWait] at hStep
          case idle.nil.none =>
            revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              intro hStep; revert hStep
              cases hTcb : storeTcbIpcState pair.2 receiver _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                let ep' : Endpoint := { state := .receive, queue := [], waitingReceiver := some receiver }
                have hStored := storeObject_objects_eq st pair.2 endpointId (.endpoint ep') hStore
                have hPreserved := storeTcbIpcState_preserves_endpoint pair.2 st2 receiver _ endpointId ep' hStored hTcb
                refine ⟨ep', ?_, ?_⟩
                · rw [removeRunnable_preserves_objects st2 receiver]; exact hPreserved
                · simp [endpointQueueWellFormed, ep']

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
                    simp only [hQueue, hWait] at hStep
                    revert hStep
                    cases hStore : storeObject endpointId _ st with
                    | error e => simp
                    | ok pair =>
                      rcases pair with ⟨⟨⟩, st_store⟩
                      simp only []
                      intro hStep; revert hStep
                      cases hTcb : storeTcbIpcState st_store head .ready with
                      | error e => simp
                      | ok st2 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have hStored := storeObject_objects_eq st st_store endpointId _ hStore
                        have hPreserved := storeTcbIpcState_preserves_endpoint st_store st2 head .ready endpointId _ hStored hTcb
                        have hFinal := (congrFun (ensureRunnable_preserves_objects st2 head) endpointId).trans hPreserved
                        exact ⟨_, hFinal, by cases tail <;> simp [endpointQueueWellFormed]⟩
                | some receiver =>
                    simp [hQueue, hWait] at hStep

/-- H-09/WS-E3: Endpoint send preserves notification objects at other IDs. -/
theorem endpointSend_preserves_notification_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNe : nid ≠ endpointId)
    (hPre : st.objects nid = some (.notification ntfn)) :
    st'.objects nid = some (.notification ntfn) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state with
      | idle =>
        simp only [hObj, hState] at hStep
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []; intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 sender _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_objects st2 sender]
            exact storeTcbIpcState_preserves_notification pair.2 st2 sender _ nid ntfn
              (storeObject_objects_ne st pair.2 endpointId nid _ hNe hStore ▸ hPre) hTcb
      | send =>
        simp only [hObj, hState] at hStep
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []; intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 sender _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_objects st2 sender]
            exact storeTcbIpcState_preserves_notification pair.2 st2 sender _ nid ntfn
              (storeObject_objects_ne st pair.2 endpointId nid _ hNe hStore ▸ hPre) hTcb
      | receive =>
        cases hQueue : epOld.queue <;> cases hWait : epOld.waitingReceiver <;>
          simp [hObj, hState, hQueue, hWait] at hStep
        case nil.some receiver =>
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            exact storeObject_objects_ne st st' endpointId nid _ hNe hStore ▸ hPre

/-- H-09/WS-E3: Endpoint await-receive preserves notification objects at other IDs. -/
theorem endpointAwaitReceive_preserves_notification_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNe : nid ≠ endpointId)
    (hPre : st.objects nid = some (.notification ntfn)) :
    st'.objects nid = some (.notification ntfn) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> cases hQueue : epOld.queue <;>
        cases hWait : epOld.waitingReceiver <;>
        simp [hObj, hState, hQueue, hWait] at hStep
      case idle.nil.none =>
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []; intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 receiver _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_objects st2 receiver]
            exact storeTcbIpcState_preserves_notification pair.2 st2 receiver _ nid ntfn
              (storeObject_objects_ne st pair.2 endpointId nid _ hNe hStore ▸ hPre) hTcb

/-- H-09/WS-E3: Endpoint receive preserves notification objects at other IDs. -/
theorem endpointReceive_preserves_notification_at
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNe : nid ≠ endpointId)
    (hPre : st.objects nid = some (.notification ntfn)) :
    st'.objects nid = some (.notification ntfn) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> simp [hObj, hState] at hStep
      case send =>
        cases hQueue : epOld.queue with
        | nil => cases hWait : epOld.waitingReceiver <;> simp [hQueue, hWait] at hStep
        | cons head tail =>
          cases hWait : epOld.waitingReceiver with
          | none =>
            simp only [hQueue, hWait] at hStep
            revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []; intro hStep; revert hStep
              cases hTcb : storeTcbIpcState pair.2 head .ready with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                rw [ensureRunnable_preserves_objects st2 head]
                exact storeTcbIpcState_preserves_notification pair.2 st2 head .ready nid ntfn
                  (storeObject_objects_ne st pair.2 endpointId nid _ hNe hStore ▸ hPre) hTcb
          | some _ => simp [hQueue, hWait] at hStep

-- ============================================================================
-- H-09/WS-E3: Backward preservation lemmas for ipcInvariant proofs
-- ============================================================================

/-- Backward: if post-state of endpointSend has endpoint at oid ≠ endpointId,
    then pre-state had the same endpoint. -/
theorem endpointSend_endpoint_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ep : Endpoint) (hNe : oid ≠ endpointId)
    (hPost : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state with
      | idle | send =>
        all_goals (
          simp only [hObj, hState] at hStep; revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []; intro hStep; revert hStep
            cases hTcb : storeTcbIpcState pair.2 sender _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              rw [removeRunnable_preserves_objects st2 sender] at hPost
              exact storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore ▸
                storeTcbIpcState_endpoint_backward pair.2 st2 sender _ oid ep hPost hTcb)
      | receive =>
        cases hQueue : epOld.queue <;> cases hWait : epOld.waitingReceiver <;>
          simp [hObj, hState, hQueue, hWait] at hStep
        case nil.some receiver =>
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            exact (storeObject_objects_ne st st' endpointId oid _ hNe hStore).symm ▸ hPost

/-- Backward: if post-state of endpointSend has notification at oid ≠ endpointId,
    then pre-state had the same notification. -/
theorem endpointSend_notification_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ntfn : Notification) (hNe : oid ≠ endpointId)
    (hPost : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state with
      | idle | send =>
        all_goals (
          simp only [hObj, hState] at hStep; revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []; intro hStep; revert hStep
            cases hTcb : storeTcbIpcState pair.2 sender _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              rw [removeRunnable_preserves_objects st2 sender] at hPost
              exact storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore ▸
                storeTcbIpcState_notification_backward pair.2 st2 sender _ oid ntfn hPost hTcb)
      | receive =>
        cases hQueue : epOld.queue <;> cases hWait : epOld.waitingReceiver <;>
          simp [hObj, hState, hQueue, hWait] at hStep
        case nil.some receiver =>
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            exact (storeObject_objects_ne st st' endpointId oid _ hNe hStore).symm ▸ hPost

/-- Backward: if post-state of endpointAwaitReceive has endpoint at oid ≠ endpointId,
    then pre-state had the same endpoint. -/
theorem endpointAwaitReceive_endpoint_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ep : Endpoint) (hNe : oid ≠ endpointId)
    (hPost : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> cases hQueue : epOld.queue <;>
        cases hWait : epOld.waitingReceiver <;>
        simp [hObj, hState, hQueue, hWait] at hStep
      case idle.nil.none =>
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []; intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 receiver _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_objects st2 receiver] at hPost
            exact storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore ▸
              storeTcbIpcState_endpoint_backward pair.2 st2 receiver _ oid ep hPost hTcb

/-- Backward: if post-state of endpointAwaitReceive has notification at oid ≠ endpointId,
    then pre-state had the same notification. -/
theorem endpointAwaitReceive_notification_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ntfn : Notification) (hNe : oid ≠ endpointId)
    (hPost : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> cases hQueue : epOld.queue <;>
        cases hWait : epOld.waitingReceiver <;>
        simp [hObj, hState, hQueue, hWait] at hStep
      case idle.nil.none =>
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []; intro hStep; revert hStep
          cases hTcb : storeTcbIpcState pair.2 receiver _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_objects st2 receiver] at hPost
            exact storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore ▸
              storeTcbIpcState_notification_backward pair.2 st2 receiver _ oid ntfn hPost hTcb

/-- Backward: if post-state of endpointReceive has endpoint at oid ≠ endpointId,
    then pre-state had the same endpoint. -/
theorem endpointReceive_endpoint_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (ep : Endpoint) (hNe : oid ≠ endpointId)
    (hPost : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> simp [hObj, hState] at hStep
      case send =>
        cases hQueue : epOld.queue with
        | nil => cases hWait : epOld.waitingReceiver <;> simp [hQueue, hWait] at hStep
        | cons head tail =>
          cases hWait : epOld.waitingReceiver with
          | none =>
            simp only [hQueue, hWait] at hStep; revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []; intro hStep; revert hStep
              cases hTcb : storeTcbIpcState pair.2 head .ready with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                rw [ensureRunnable_preserves_objects st2 head] at hPost
                exact storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore ▸
                  storeTcbIpcState_endpoint_backward pair.2 st2 head .ready oid ep hPost hTcb
          | some _ => simp [hQueue, hWait] at hStep

/-- Backward: if post-state of endpointReceive has notification at oid ≠ endpointId,
    then pre-state had the same notification. -/
theorem endpointReceive_notification_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (ntfn : Notification) (hNe : oid ≠ endpointId)
    (hPost : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint epOld =>
      cases hState : epOld.state <;> simp [hObj, hState] at hStep
      case send =>
        cases hQueue : epOld.queue with
        | nil => cases hWait : epOld.waitingReceiver <;> simp [hQueue, hWait] at hStep
        | cons head tail =>
          cases hWait : epOld.waitingReceiver with
          | none =>
            simp only [hQueue, hWait] at hStep; revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []; intro hStep; revert hStep
              cases hTcb : storeTcbIpcState pair.2 head .ready with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                rw [ensureRunnable_preserves_objects st2 head] at hPost
                exact storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore ▸
                  storeTcbIpcState_notification_backward pair.2 st2 head .ready oid ntfn hPost hTcb
          | some _ => simp [hQueue, hWait] at hStep

theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    rcases endpointSend_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
    by_cases hEq : oid = endpointId
    · subst hEq
      have hCast : ep = epNew := by rw [hStored] at hObj; cases hObj; rfl
      have hObjValidNew := endpointObjectValid_of_queueWellFormed epNew hWfNew
      simpa [endpointInvariant, hCast] using And.intro hWfNew hObjValidNew
    · exact hEndpointInv oid ep
        (endpointSend_endpoint_backward st st' endpointId sender hStep oid ep hEq hObj)
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · rcases endpointSend_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, _⟩
      subst hEq; rw [hStored] at hObj; cases hObj
    · exact hNotificationInv oid ntfn
        (endpointSend_notification_backward st st' endpointId sender hStep oid ntfn hEq hObj)

theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    rcases endpointAwaitReceive_result_wellFormed st st' endpointId receiver hStep with ⟨epNew, hStored, hWfNew⟩
    by_cases hEq : oid = endpointId
    · subst hEq
      have hCast : ep = epNew := by rw [hStored] at hObj; cases hObj; rfl
      have hObjValidNew := endpointObjectValid_of_queueWellFormed epNew hWfNew
      simpa [endpointInvariant, hCast] using And.intro hWfNew hObjValidNew
    · exact hEndpointInv oid ep
        (endpointAwaitReceive_endpoint_backward st st' endpointId receiver hStep oid ep hEq hObj)
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · rcases endpointAwaitReceive_result_wellFormed st st' endpointId receiver hStep with ⟨epNew, hStored, _⟩
      subst hEq; rw [hStored] at hObj; cases hObj
    · exact hNotificationInv oid ntfn
        (endpointAwaitReceive_notification_backward st st' endpointId receiver hStep oid ntfn hEq hObj)

theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hObj
    rcases endpointReceive_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, hWfNew⟩
    by_cases hEq : oid = endpointId
    · subst hEq
      have hCast : ep = epNew := by rw [hStored] at hObj; cases hObj; rfl
      have hObjValidNew := endpointObjectValid_of_queueWellFormed epNew hWfNew
      simpa [endpointInvariant, hCast] using And.intro hWfNew hObjValidNew
    · exact hEndpointInv oid ep
        (endpointReceive_endpoint_backward st st' endpointId sender hStep oid ep hEq hObj)
  · intro oid ntfn hObj
    by_cases hEq : oid = endpointId
    · rcases endpointReceive_result_wellFormed st st' endpointId sender hStep with ⟨epNew, hStored, _⟩
      subst hEq; rw [hStored] at hObj; cases hObj
    · exact hNotificationInv oid ntfn
        (endpointReceive_notification_backward st st' endpointId sender hStep oid ntfn hEq hObj)

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
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
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
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
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
      | vspaceRoot root => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | endpoint ep =>
          refine ⟨ep, rfl⟩

/-- Shared preservation helper for endpoint operations that perform one endpoint-object store.

It captures the common proof skeleton used by send/await/receive scheduler-bundle theorems. -/
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

/-- `storeTcbIpcState` preserves the scheduler invariant bundle (scheduler unchanged,
    target TCB object remains a TCB). -/
private theorem storeTcbIpcState_preserves_schedulerInvariantBundle
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : schedulerInvariantBundle st)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  have hSched := storeTcbIpcState_scheduler_eq st st' tid ipc hStep
  refine ⟨by rwa [hSched], by rwa [hSched], ?_⟩
  unfold currentThreadValid at hCur ⊢; rw [hSched]
  cases hc : st.scheduler.current with
  | none => simp [hc]
  | some curTid =>
    simp only [hc] at hCur ⊢
    rcases hCur with ⟨tcb, hTcbObj⟩
    by_cases hEq : curTid.toObjId = tid.toObjId
    · rcases storeTcbIpcState_objects_at st st' tid ipc hStep with
        ⟨tcb', _, hPost⟩ | ⟨_, hStEq⟩
      · rw [← hEq] at hPost; exact ⟨_, hPost⟩
      · subst hStEq; exact ⟨tcb, hTcbObj⟩
    · exact ⟨tcb, by rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc _ hEq hStep]; exact hTcbObj⟩

/-- `removeRunnable` preserves the scheduler invariant bundle. -/
private theorem removeRunnable_preserves_schedulerInvariantBundle
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st) :
    schedulerInvariantBundle (removeRunnable st tid) := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent
    unfold queueCurrentConsistent at hQueue ⊢
    rw [removeRunnable_current]
    by_cases hEq : st.scheduler.current = some tid
    · simp [hEq]
    · simp [hEq]
      cases hc : st.scheduler.current with
      | none => trivial
      | some curTid =>
        simp only [hc] at hQueue ⊢
        rw [removeRunnable_mem_iff]
        exact ⟨hQueue, fun h => hEq (h ▸ hc)⟩
  · -- runQueueUnique
    unfold runQueueUnique at hRunq ⊢
    simp only [removeRunnable]
    exact hRunq.filter _
  · -- currentThreadValid
    unfold currentThreadValid at hCur ⊢
    simp only [removeRunnable]
    by_cases hEq : st.scheduler.current = some tid
    · simp [hEq]
    · simp [hEq]; exact hCur

/-- `ensureRunnable` preserves the scheduler invariant bundle. -/
private theorem ensureRunnable_preserves_schedulerInvariantBundle
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st) :
    schedulerInvariantBundle (ensureRunnable st tid) := by
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  unfold ensureRunnable
  by_cases hMem : tid ∈ st.scheduler.runnable
  · simp [hMem]; exact ⟨hQueue, hRunq, hCur⟩
  · simp [hMem]
    refine ⟨?_, ?_, ?_⟩
    · -- queueCurrentConsistent
      unfold queueCurrentConsistent at hQueue ⊢; simp only []
      cases hc : st.scheduler.current with
      | none => trivial
      | some curTid =>
        simp only [hc] at hQueue ⊢
        exact List.mem_append.mpr (Or.inl hQueue)
    · -- runQueueUnique
      unfold runQueueUnique at hRunq ⊢; simp only []
      rw [List.nodup_append]
      refine ⟨hRunq, .cons (fun _ h => absurd h List.not_mem_nil) .nil, ?_⟩
      intro a hal b hb
      rw [List.mem_singleton] at hb; subst hb; intro heq; subst heq; exact hMem hal
    · -- currentThreadValid
      unfold currentThreadValid at hCur ⊢; simp only []; exact hCur

/-- Endpoint send preserves the scheduler invariant bundle.

    H-09/WS-E3: Updated for compound transitions (storeObject → storeTcbIpcState →
    removeRunnable) on idle/send paths. The receive path remains single-step. -/
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
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hState : ep.state <;> simp only [hState] at hStep
      all_goals split at hStep
      -- idle: storeObject → storeTcbIpcState → removeRunnable
      · -- storeObject error
        exact absurd hStep (by simp)
      · -- storeObject ok
        rename_i st1 hStore
        split at hStep
        · exact absurd hStep (by simp)
        · rename_i st2 hTcb
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep; subst hStep
          exact removeRunnable_preserves_schedulerInvariantBundle _ sender
            (storeTcbIpcState_preserves_schedulerInvariantBundle _ _ sender _
              (endpoint_store_preserves_schedulerInvariantBundle st st1 endpointId hInv
                ⟨_, hStore⟩ ⟨ep, hObj⟩ (fun oid hNe => storeObject_objects_ne st st1 endpointId oid _ hNe hStore))
              hTcb)
      -- send: storeObject → storeTcbIpcState → removeRunnable
      · exact absurd hStep (by simp)
      · rename_i st1 hStore
        split at hStep
        · exact absurd hStep (by simp)
        · rename_i st2 hTcb
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep; subst hStep
          exact removeRunnable_preserves_schedulerInvariantBundle _ sender
            (storeTcbIpcState_preserves_schedulerInvariantBundle _ _ sender _
              (endpoint_store_preserves_schedulerInvariantBundle st st1 endpointId hInv
                ⟨_, hStore⟩ ⟨ep, hObj⟩ (fun oid hNe => storeObject_objects_ne st st1 endpointId oid _ hNe hStore))
              hTcb)
      -- receive: storeObject on ([], some _) or error on (_, _)
      · exact endpoint_store_preserves_schedulerInvariantBundle st st' endpointId hInv
          ⟨_, hStep⟩ ⟨ep, hObj⟩ (fun oid hNe => storeObject_objects_ne st st' endpointId oid _ hNe hStep)
      · exact absurd hStep (by simp)

/-- Endpoint await-receive preserves the scheduler invariant bundle. -/
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
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      -- Three-way match on (ep.state, ep.queue, ep.waitingReceiver):
      -- only (.idle, [], none) succeeds. Exhaust all combinations.
      cases hState : ep.state <;> cases hQ : ep.queue <;>
        cases hW : ep.waitingReceiver <;> simp [hState, hQ, hW] at hStep
      -- Sole survivor: idle, nil, none → storeObject → storeTcbIpcState → removeRunnable
      split at hStep
      · exact absurd hStep (by simp)
      · rename_i st1 hStore
        split at hStep
        · exact absurd hStep (by simp)
        · rename_i st2 hTcb
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep; subst hStep
          exact removeRunnable_preserves_schedulerInvariantBundle _ receiver
            (storeTcbIpcState_preserves_schedulerInvariantBundle _ _ receiver _
              (endpoint_store_preserves_schedulerInvariantBundle st st1 endpointId hInv
                ⟨_, hStore⟩ ⟨ep, hObj⟩ (fun oid hNe => storeObject_objects_ne st st1 endpointId oid _ hNe hStore))
              hTcb)

/-- Endpoint receive preserves the scheduler invariant bundle. -/
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
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      -- Three-way match on (ep.state, ep.queue, ep.waitingReceiver):
      -- only (.send, h::t, none) succeeds. Exhaust all combinations.
      cases hState : ep.state <;> cases hQ : ep.queue <;>
        cases hW : ep.waitingReceiver <;> simp [hState, hQ, hW] at hStep
      -- Sole survivor: send, cons h t, none → storeObject → storeTcbIpcState → ensureRunnable
      rename_i h t
      split at hStep
      · exact absurd hStep (by simp)
      · rename_i st1 hStore
        split at hStep
        · exact absurd hStep (by simp)
        · rename_i st2 hTcb
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, hEq⟩ := hStep; subst hEq
          exact ensureRunnable_preserves_schedulerInvariantBundle _ h
            (storeTcbIpcState_preserves_schedulerInvariantBundle _ _ h _
              (endpoint_store_preserves_schedulerInvariantBundle st st1 endpointId hInv
                ⟨_, hStore⟩ ⟨ep, hObj⟩ (fun oid hNe => storeObject_objects_ne st st1 endpointId oid _ hNe hStore))
              hTcb)


-- ============================================================================
-- F-12: Notification waiting-list uniqueness invariant (WS-D4, TPI-D06)
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
