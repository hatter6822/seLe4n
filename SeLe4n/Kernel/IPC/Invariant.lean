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

## H-09 (WS-E3) proof architecture

After H-09, endpoint operations perform a 3-step chain:
1. `storeObject` — update the endpoint object
2. `storeTcbIpcState` — set the thread's IPC state
3. `removeRunnable` / `ensureRunnable` — update the scheduler

The `*_chain` decomposition lemmas expose this structure so that all downstream
proofs can reason about the chain without re-unfolding the operations.
-/

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
-- Endpoint queue well-formedness (moved before chain lemmas for dependency order)
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

-- ============================================================================
-- H-09 (WS-E3): Chain decomposition lemmas
-- ============================================================================

/-- Chain decomposition for `endpointSend`.

After a successful `endpointSend`, the final state is the result of:
1. a `storeObject` at `endpointId` that writes a well-formed endpoint,
2. a `storeTcbIpcState` that modifies one thread's IPC state,
3. a `removeRunnable` or `ensureRunnable` that modifies the scheduler.

In the blocking path (idle→send or send→send), the sender's IPC state is set to
`blockedOnSend` and the sender is removed from the runnable queue.
In the handshake path (receive→idle), a waiting receiver's IPC state is set to
`ready` and the receiver is added to the runnable queue. -/
theorem endpointSend_chain
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ (ep' : Endpoint) (st1 st2 : SystemState),
      storeObject endpointId (.endpoint ep') st = .ok ((), st1) ∧
      endpointQueueWellFormed ep' ∧
      ((storeTcbIpcState st1 sender (.blockedOnSend endpointId) = .ok st2 ∧
        st' = removeRunnable st2 sender) ∨
       (∃ receiver, storeTcbIpcState st1 receiver .ready = .ok st2 ∧
        st' = ensureRunnable st2 receiver)) := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      cases hState : ep.state with
      | idle =>
        simp only [hObj, hState, storeObject] at hStep
        revert hStep
        cases hTcb : storeTcbIpcState _ sender (.blockedOnSend endpointId) with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro ⟨_, hEq⟩
          exact ⟨{ state := .send, queue := [sender], waitingReceiver := none },
            _, st2,
            by simp [storeObject],
            by simp [endpointQueueWellFormed],
            .inl ⟨hTcb, hEq.symm⟩⟩
      | send =>
        simp only [hObj, hState, storeObject] at hStep
        revert hStep
        cases hTcb : storeTcbIpcState _ sender (.blockedOnSend endpointId) with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro ⟨_, hEq⟩
          exact ⟨{ state := .send, queue := ep.queue ++ [sender], waitingReceiver := none },
            _, st2,
            by simp [storeObject],
            by simp [endpointQueueWellFormed],
            .inl ⟨hTcb, hEq.symm⟩⟩
      | receive =>
        simp only [hObj, hState] at hStep
        cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
          simp only [hQueue, hWait, storeObject] at hStep <;> try exact absurd hStep (by simp)
        case nil.some receiver =>
          revert hStep
          cases hTcb : storeTcbIpcState _ receiver .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩
            exact ⟨{ state := .idle, queue := [], waitingReceiver := none },
              _, st2,
              by simp [storeObject],
              by simp [endpointQueueWellFormed],
              .inr ⟨receiver, hTcb, hEq.symm⟩⟩

/-- Chain decomposition for `endpointAwaitReceive`.
Always takes the blocking path: receiver's IPC state → `blockedOnReceive`. -/
theorem endpointAwaitReceive_chain
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ (ep' : Endpoint) (st1 st2 : SystemState),
      storeObject endpointId (.endpoint ep') st = .ok ((), st1) ∧
      endpointQueueWellFormed ep' ∧
      storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) = .ok st2 ∧
      st' = removeRunnable st2 receiver := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      cases hState : ep.state <;> cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
        simp only [hObj, hState, hQueue, hWait, storeObject] at hStep <;> try exact absurd hStep (by simp)
      case idle.nil.none =>
        revert hStep
        cases hTcb : storeTcbIpcState _ receiver (.blockedOnReceive endpointId) with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]
          intro ⟨_, hEq⟩
          exact ⟨{ state := .receive, queue := [], waitingReceiver := some receiver },
            _, st2,
            by simp [storeObject],
            by simp [endpointQueueWellFormed],
            hTcb, hEq.symm⟩

/-- Chain decomposition for `endpointReceive`.
Always takes the unblocking path: dequeued sender's IPC state → `ready`. -/
theorem endpointReceive_chain
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ (ep' : Endpoint) (st1 st2 : SystemState),
      storeObject endpointId (.endpoint ep') st = .ok ((), st1) ∧
      endpointQueueWellFormed ep' ∧
      storeTcbIpcState st1 sender .ready = .ok st2 ∧
      st' = ensureRunnable st2 sender := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | vspaceRoot _ | notification _ => simp [hObj] at hStep
    | endpoint ep =>
      cases hState : ep.state with
      | idle => simp [hObj, hState] at hStep
      | receive => simp [hObj, hState] at hStep
      | send =>
        simp only [hObj, hState] at hStep
        cases hQueue : ep.queue with
        | nil =>
          cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
        | cons head tail =>
          cases hWait : ep.waitingReceiver with
          | none =>
            simp only [hQueue, hWait] at hStep
            -- Extract storeObject step (always succeeds)
            revert hStep
            cases hStore : storeObject endpointId
              (.endpoint { state := if tail.isEmpty = true then .idle else .send,
                           queue := tail }) st with
            | error e => intro hStep; simp [hStore] at hStep
            | ok val =>
              obtain ⟨_, st1⟩ := val
              simp only [hStore]
              cases hTcb : storeTcbIpcState st1 head .ready with
              | error e => intro hStep; simp [hTcb] at hStep
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq, hTcb]
                intro ⟨hSender, hEq⟩
                subst hSender
                have hWf : endpointQueueWellFormed
                    { state := if tail.isEmpty = true then .idle else .send,
                      queue := tail } := by
                  simp only [endpointQueueWellFormed]
                  cases tail with
                  | nil => simp
                  | cons _ _ => simp [List.isEmpty]
                exact ⟨_, st1, st2, hStore, hWf, hTcb, hEq.symm⟩
          | some _ => simp [hQueue, hWait] at hStep


-- ============================================================================
-- H-09 (WS-E3): Chain-level object preservation lemmas
-- ============================================================================

/-- Endpoint objects at IDs other than `endpointId` are preserved through the
full `endpointSend` chain (storeObject → storeTcbIpcState → removeRunnable/ensureRunnable). -/
theorem endpointSend_preserves_endpoint_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hEp : st.objects oid = some (.endpoint ep))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects oid = some (.endpoint ep) := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  have h1 : st1.objects oid = some (.endpoint ep) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hEp
  have h2 : st2.objects oid = some (.endpoint ep) := by
    rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
      exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ oid ep h1 hTcb
  rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
    first | rw [removeRunnable_preserves_objects]; exact h2
          | rw [ensureRunnable_preserves_objects]; exact h2

/-- Notification objects at any ID are preserved through `endpointSend`. -/
theorem endpointSend_preserves_notification_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ntfn : Notification)
    (hNtfn : st.objects oid = some (.notification ntfn))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects oid = some (.notification ntfn) := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  have hNe : oid ≠ endpointId := by
    intro heq; subst heq
    unfold endpointSend at hStep; simp [hNtfn] at hStep
  have h1 : st1.objects oid = some (.notification ntfn) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hNtfn
  have h2 : st2.objects oid = some (.notification ntfn) := by
    rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
      exact storeTcbIpcState_preserves_notification st1 st2 _ _ oid ntfn h1 hTcb
  rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
    first | rw [removeRunnable_preserves_objects]; exact h2
          | rw [ensureRunnable_preserves_objects]; exact h2

/-- CNode objects at any ID are preserved through `endpointSend`. -/
theorem endpointSend_preserves_cnode_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (cn : CNode)
    (hCn : st.objects oid = some (.cnode cn))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st'.objects oid = some (.cnode cn) := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  have hNe : oid ≠ endpointId := by
    intro heq; subst heq
    unfold endpointSend at hStep; simp [hCn] at hStep
  have h1 : st1.objects oid = some (.cnode cn) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hCn
  have h2 : st2.objects oid = some (.cnode cn) := by
    rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
      exact storeTcbIpcState_preserves_cnode st1 st2 _ _ oid cn h1 hTcb
  rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
    first | rw [removeRunnable_preserves_objects]; exact h2
          | rw [ensureRunnable_preserves_objects]; exact h2

/-- Endpoint objects at IDs other than `endpointId` are preserved through `endpointAwaitReceive`. -/
theorem endpointAwaitReceive_preserves_endpoint_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hEp : st.objects oid = some (.endpoint ep))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st'.objects oid = some (.endpoint ep) := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have h1 : st1.objects oid = some (.endpoint ep) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hEp
  rw [removeRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ oid ep h1 hTcb

/-- Notification objects are preserved through `endpointAwaitReceive`. -/
theorem endpointAwaitReceive_preserves_notification_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (ntfn : Notification)
    (hNtfn : st.objects oid = some (.notification ntfn))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st'.objects oid = some (.notification ntfn) := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have hNe : oid ≠ endpointId := by
    intro heq; subst heq
    unfold endpointAwaitReceive at hStep; simp [hNtfn] at hStep
  have h1 : st1.objects oid = some (.notification ntfn) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hNtfn
  rw [removeRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_notification st1 st2 _ _ oid ntfn h1 hTcb

/-- CNode objects are preserved through `endpointAwaitReceive`. -/
theorem endpointAwaitReceive_preserves_cnode_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (cn : CNode)
    (hCn : st.objects oid = some (.cnode cn))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st'.objects oid = some (.cnode cn) := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have hNe : oid ≠ endpointId := by
    intro heq; subst heq
    unfold endpointAwaitReceive at hStep; simp [hCn] at hStep
  rw [removeRunnable_preserves_objects]
  have h1 : st1.objects oid = some (.cnode cn) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hCn
  exact storeTcbIpcState_preserves_cnode st1 st2 _ _ oid cn h1 hTcb

/-- Endpoint objects at IDs other than `endpointId` are preserved through `endpointReceive`. -/
theorem endpointReceive_preserves_endpoint_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hEp : st.objects oid = some (.endpoint ep))
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st'.objects oid = some (.endpoint ep) := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have h1 : st1.objects oid = some (.endpoint ep) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hEp
  rw [ensureRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ oid ep h1 hTcb

/-- Notification objects are preserved through `endpointReceive`. -/
theorem endpointReceive_preserves_notification_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ntfn : Notification)
    (hNtfn : st.objects oid = some (.notification ntfn))
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st'.objects oid = some (.notification ntfn) := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have hNe : oid ≠ endpointId := by
    intro heq; subst heq
    unfold endpointReceive at hStep; simp [hNtfn] at hStep
  have h1 : st1.objects oid = some (.notification ntfn) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hNtfn
  rw [ensureRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_notification st1 st2 _ _ oid ntfn h1 hTcb

/-- CNode objects are preserved through `endpointReceive`. -/
theorem endpointReceive_preserves_cnode_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (cn : CNode)
    (hCn : st.objects oid = some (.cnode cn))
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st'.objects oid = some (.cnode cn) := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have hNe : oid ≠ endpointId := by
    intro heq; subst heq
    unfold endpointReceive at hStep; simp [hCn] at hStep
  have h1 : st1.objects oid = some (.cnode cn) := by
    rw [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore]; exact hCn
  rw [ensureRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_cnode st1 st2 _ _ oid cn h1 hTcb


-- ============================================================================
-- Invariant definitions
-- ============================================================================

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

-- ============================================================================
-- Well-formedness of operation results
-- ============================================================================

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
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, hWf, hChain⟩
  refine ⟨ep', ?_, hWf⟩
  have h1 : st1.objects endpointId = some (.endpoint ep') :=
    storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
  have h2 : st2.objects endpointId = some (.endpoint ep') := by
    rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
      exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ endpointId ep' h1 hTcb
  rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
    first | rw [removeRunnable_preserves_objects]; exact h2
          | rw [ensureRunnable_preserves_objects]; exact h2

theorem endpointAwaitReceive_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, hWf, hTcb, hSt'⟩
  subst hSt'
  refine ⟨ep', ?_, hWf⟩
  have h1 := storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
  rw [removeRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ endpointId ep' h1 hTcb

theorem endpointReceive_result_wellFormed
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, hWf, hTcb, hSt'⟩
  subst hSt'
  refine ⟨ep', ?_, hWf⟩
  have h1 := storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
  rw [ensureRunnable_preserves_objects]
  exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ endpointId ep' h1 hTcb


-- ============================================================================
-- H-09: Backward object-preservation through the chain
-- ============================================================================

/-- Backward: if a post-`endpointSend` state has an endpoint at `oid ≠ endpointId`,
the pre-state had the same endpoint. -/
theorem endpointSend_endpoint_backward_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hEpPost : st'.objects oid = some (.endpoint ep))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st.objects oid = some (.endpoint ep) := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  have h3 : st2.objects oid = some (.endpoint ep) := by
    rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
      first | rwa [removeRunnable_preserves_objects] at hEpPost
            | rwa [ensureRunnable_preserves_objects] at hEpPost
  have h2 : st1.objects oid = some (.endpoint ep) := by
    rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
      exact storeTcbIpcState_endpoint_backward st1 st2 _ _ oid ep h3 hTcb
  rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at h2

/-- Backward: if a post-`endpointSend` state has a notification at any `oid`,
the pre-state had the same notification. -/
theorem endpointSend_notification_backward_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ntfn : Notification)
    (hNtfnPost : st'.objects oid = some (.notification ntfn))
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    st.objects oid = some (.notification ntfn) := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  have hNe : oid ≠ endpointId := by
    intro heq; subst oid
    have h1 := storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
    have h2 : st2.objects endpointId = some (.endpoint ep') := by
      rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
        exact storeTcbIpcState_preserves_endpoint st1 st2 _ _ endpointId ep' h1 hTcb
    have h3 : st'.objects endpointId = some (.endpoint ep') := by
      rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
        first | rw [removeRunnable_preserves_objects]; exact h2
              | rw [ensureRunnable_preserves_objects]; exact h2
    rw [h3] at hNtfnPost; cases hNtfnPost
  have h3 : st2.objects oid = some (.notification ntfn) := by
    rcases hChain with ⟨_, hSt'⟩ | ⟨_, _, hSt'⟩ <;> subst hSt' <;>
      first | rwa [removeRunnable_preserves_objects] at hNtfnPost
            | rwa [ensureRunnable_preserves_objects] at hNtfnPost
  have h2 : st1.objects oid = some (.notification ntfn) := by
    rcases hChain with ⟨hTcb, _⟩ | ⟨_, hTcb, _⟩ <;>
      exact storeTcbIpcState_notification_backward st1 st2 _ _ oid ntfn h3 hTcb
  rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at h2

/-- Backward: if a post-`endpointAwaitReceive` state has an endpoint at `oid ≠ endpointId`,
the pre-state had the same endpoint. -/
theorem endpointAwaitReceive_endpoint_backward_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hEpPost : st'.objects oid = some (.endpoint ep))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st.objects oid = some (.endpoint ep) := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  rw [removeRunnable_preserves_objects] at hEpPost
  have h2 := storeTcbIpcState_endpoint_backward st1 st2 _ _ oid ep hEpPost hTcb
  rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at h2

/-- Backward: notification preservation through `endpointAwaitReceive`. -/
theorem endpointAwaitReceive_notification_backward_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (ntfn : Notification)
    (hNtfnPost : st'.objects oid = some (.notification ntfn))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    st.objects oid = some (.notification ntfn) := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have hNe : oid ≠ endpointId := by
    intro heq; subst oid
    have h1 := storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
    have h2 := storeTcbIpcState_preserves_endpoint st1 st2 _ _ endpointId ep' h1 hTcb
    rw [removeRunnable_preserves_objects] at hNtfnPost; rw [h2] at hNtfnPost; cases hNtfnPost
  rw [removeRunnable_preserves_objects] at hNtfnPost
  have h2 := storeTcbIpcState_notification_backward st1 st2 _ _ oid ntfn hNtfnPost hTcb
  rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at h2

/-- Backward: endpoint preservation through `endpointReceive`. -/
theorem endpointReceive_endpoint_backward_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hEpPost : st'.objects oid = some (.endpoint ep))
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st.objects oid = some (.endpoint ep) := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  rw [ensureRunnable_preserves_objects] at hEpPost
  have h2 := storeTcbIpcState_endpoint_backward st1 st2 _ _ oid ep hEpPost hTcb
  rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at h2

/-- Backward: notification preservation through `endpointReceive`. -/
theorem endpointReceive_notification_backward_at
    (st st' : SystemState) (endpointId oid : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (ntfn : Notification)
    (hNtfnPost : st'.objects oid = some (.notification ntfn))
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    st.objects oid = some (.notification ntfn) := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcb, hSt'⟩
  subst hSt'
  have hNe : oid ≠ endpointId := by
    intro heq; subst oid
    have h1 := storeObject_objects_eq st st1 endpointId (.endpoint ep') hStore
    have h2 := storeTcbIpcState_preserves_endpoint st1 st2 _ _ endpointId ep' h1 hTcb
    rw [ensureRunnable_preserves_objects] at hNtfnPost; rw [h2] at hNtfnPost; cases hNtfnPost
  rw [ensureRunnable_preserves_objects] at hNtfnPost
  have h2 := storeTcbIpcState_notification_backward st1 st2 _ _ oid ntfn hNtfnPost hTcb
  rwa [storeObject_objects_ne st st1 endpointId oid (.endpoint ep') hNe hStore] at h2

-- ============================================================================
-- IPC invariant preservation
-- ============================================================================

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
        (endpointSend_endpoint_backward_at st st' endpointId oid sender ep hEq hObj hStep)
  · intro oid ntfn hObj
    exact hNotificationInv oid ntfn
      (endpointSend_notification_backward_at st st' endpointId oid sender ntfn hObj hStep)

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
        (endpointAwaitReceive_endpoint_backward_at st st' endpointId oid receiver ep hEq hObj hStep)
  · intro oid ntfn hObj
    exact hNotificationInv oid ntfn
      (endpointAwaitReceive_notification_backward_at st st' endpointId oid receiver ntfn hObj hStep)

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
        (endpointReceive_endpoint_backward_at st st' endpointId oid sender ep hEq hObj hStep)
  · intro oid ntfn hObj
    exact hNotificationInv oid ntfn
      (endpointReceive_notification_backward_at st st' endpointId oid sender ntfn hObj hStep)

-- ============================================================================
-- Pre-state endpoint existence
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


-- ============================================================================
-- H-09 (WS-E3): IPC-scheduler contract preservation (non-vacuous proofs)
-- ============================================================================

/-- Helper: TCB objects at `tid.toObjId` where `tid ≠ modifiedTid` are preserved
through the endpoint 3-step chain, provided `tid.toObjId ≠ endpointId`.

This is the key frame lemma for IPC-scheduler contract proofs. -/
private theorem chain_tcb_at_other_thread
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId)
    (tid modifiedTid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (tcb : TCB) (ep' : Endpoint)
    (hNeTid : tid ≠ modifiedTid)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 modifiedTid ipc = .ok st2)
    (hTcbPost : st2.objects tid.toObjId = some (.tcb tcb)) :
    st.objects tid.toObjId = some (.tcb tcb) := by
  have hNeObjId : tid.toObjId ≠ modifiedTid.toObjId :=
    fun h => hNeTid (SeLe4n.ThreadId.toObjId_injective tid modifiedTid h)
  have h2 : st1.objects tid.toObjId = some (.tcb tcb) := by
    rwa [storeTcbIpcState_preserves_objects_ne st1 st2 modifiedTid ipc tid.toObjId hNeObjId hTcb] at hTcbPost
  by_cases hNeEp : tid.toObjId = endpointId
  · -- endpointId has an endpoint in st1, not a TCB
    have hEpAtId := storeObject_objects_eq st st1 endpointId _ hStore
    rw [hNeEp] at h2; rw [hEpAtId] at h2; cases h2
  · rwa [storeObject_objects_ne st st1 endpointId tid.toObjId _ hNeEp hStore] at h2

theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  intro tid tcb hObj hRun
  rcases hChain with ⟨hTcbStep, hSt'⟩ | ⟨receiver, hTcbStep, hSt'⟩
  · -- Blocking case: sender removed from runnable
    subst hSt'
    have hNeSender : tid ≠ sender := removeRunnable_mem_implies_ne st2 sender tid hRun
    rw [removeRunnable_preserves_objects] at hObj
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
    have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid sender _ tcb ep' hNeSender hStore hTcbStep hObj
    have hRunOrig : tid ∈ st.scheduler.runnable := by
      have := removeRunnable_mem_implies_mem st2 sender tid hRun
      rwa [hSchedEq2, hSchedEq1] at this
    exact hInv tid tcb hObjOrig hRunOrig
  · -- Handshake case: receiver added to runnable
    subst hSt'
    rw [ensureRunnable_preserves_objects] at hObj
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
    by_cases hEqRecv : tid = receiver
    · -- tid IS the unblocked receiver: its ipcState was set to .ready
      subst hEqRecv
      unfold storeTcbIpcState at hTcbStep
      cases hLookup : lookupTcb st1 tid with
      | none =>
        -- lookupTcb = none contradicts hObj (which says tid.toObjId has a TCB)
        simp [hLookup] at hTcbStep; subst hTcbStep
        exfalso; simp [lookupTcb, hObj] at hLookup
      | some origTcb =>
        -- storeTcbIpcState wrote a new TCB with ipcState = .ready
        simp only [hLookup] at hTcbStep
        revert hTcbStep
        cases hInnerStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready }) st1 with
        | error e => simp
        | ok pair =>
          simp only [Except.ok.injEq]
          intro hSt2Eq; subst hSt2Eq
          have hTcbAt := storeObject_objects_eq st1 pair.2 tid.toObjId _ hInnerStore
          rw [hTcbAt] at hObj
          cases hObj
          rfl
    · -- tid ≠ receiver: TCB and runnable membership from pre-state
      have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid receiver _ tcb ep' hEqRecv hStore hTcbStep hObj
      have hRunOrig : tid ∈ st.scheduler.runnable := by
        rcases ensureRunnable_mem_implies st2 receiver tid hRun with h | h
        · rwa [hSchedEq2, hSchedEq1] at h
        · exact absurd h hEqRecv
      exact hInv tid tcb hObjOrig hRunOrig

theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  intro tid tcb epId hObj hBlocked
  rcases hChain with ⟨hTcbStep, hSt'⟩ | ⟨receiver, hTcbStep, hSt'⟩
  · -- Blocking case
    subst hSt'
    rw [removeRunnable_preserves_objects] at hObj
    by_cases hEqSender : tid = sender
    · -- sender was removed from runnable → not in filtered list
      subst hEqSender
      simp [removeRunnable, List.mem_filter]
    · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid sender _ tcb ep' hEqSender hStore hTcbStep hObj
      have hNotRun := hInv tid tcb epId hObjOrig hBlocked
      have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
      have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
      intro hRunMem
      have hMem := removeRunnable_mem_implies_mem st2 sender tid hRunMem
      rw [hSchedEq2, hSchedEq1] at hMem
      exact hNotRun hMem
  · -- Handshake case
    subst hSt'
    rw [ensureRunnable_preserves_objects] at hObj
    by_cases hEqRecv : tid = receiver
    · -- receiver's ipcState was set to .ready, not blockedOnSend
      subst hEqRecv
      unfold storeTcbIpcState at hTcbStep
      cases hLookup : lookupTcb st1 tid with
      | none =>
        simp [hLookup] at hTcbStep; subst hTcbStep
        exfalso; simp [lookupTcb, hObj] at hLookup
      | some origTcb =>
        simp only [hLookup] at hTcbStep
        revert hTcbStep
        cases hInnerStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready }) st1 with
        | error e => simp
        | ok pair =>
          simp only [Except.ok.injEq]
          intro hSt2Eq; subst hSt2Eq
          rw [storeObject_objects_eq st1 pair.2 tid.toObjId _ hInnerStore] at hObj
          cases hObj
          simp at hBlocked
    · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid receiver _ tcb ep' hEqRecv hStore hTcbStep hObj
      have hNotRun := hInv tid tcb epId hObjOrig hBlocked
      have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
      have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
      intro hRunMem
      rcases ensureRunnable_mem_implies st2 receiver tid hRunMem with hMem | hEq
      · rw [hSchedEq2, hSchedEq1] at hMem; exact hNotRun hMem
      · exact absurd hEq hEqRecv


theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  intro tid tcb epId hObj hBlocked
  rcases hChain with ⟨hTcbStep, hSt'⟩ | ⟨receiver, hTcbStep, hSt'⟩
  · -- Blocking case: storeTcbIpcState sets blockedOnSend, not blockedOnReceive
    subst hSt'
    rw [removeRunnable_preserves_objects] at hObj
    by_cases hEqSender : tid = sender
    · subst hEqSender; simp [removeRunnable, List.mem_filter]
    · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid sender _ tcb ep' hEqSender hStore hTcbStep hObj
      have hNotRun := hInv tid tcb epId hObjOrig hBlocked
      have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
      have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
      intro hRunMem
      have hMem := removeRunnable_mem_implies_mem st2 sender tid hRunMem
      rw [hSchedEq2, hSchedEq1] at hMem
      exact hNotRun hMem
  · -- Handshake case: storeTcbIpcState sets .ready, not blockedOnReceive
    subst hSt'
    rw [ensureRunnable_preserves_objects] at hObj
    by_cases hEqRecv : tid = receiver
    · subst hEqRecv
      unfold storeTcbIpcState at hTcbStep
      cases hLookup : lookupTcb st1 tid with
      | none =>
        simp [hLookup] at hTcbStep; subst hTcbStep
        exfalso; simp [lookupTcb, hObj] at hLookup
      | some origTcb =>
        simp only [hLookup] at hTcbStep
        revert hTcbStep
        cases hInnerStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready }) st1 with
        | error e => simp
        | ok pair =>
          simp only [Except.ok.injEq]
          intro hSt2Eq; subst hSt2Eq
          rw [storeObject_objects_eq st1 pair.2 tid.toObjId _ hInnerStore] at hObj
          cases hObj; simp at hBlocked
    · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid receiver _ tcb ep' hEqRecv hStore hTcbStep hObj
      have hNotRun := hInv tid tcb epId hObjOrig hBlocked
      have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
      have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
      intro hRunMem
      rcases ensureRunnable_mem_implies st2 receiver tid hRunMem with hMem | hEq
      · rw [hSchedEq2, hSchedEq1] at hMem; exact hNotRun hMem
      · exact absurd hEq hEqRecv

theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  exact ⟨endpointSend_preserves_runnableThreadIpcReady st st' endpointId sender hReady hStep,
    endpointSend_preserves_blockedOnSendNotRunnable st st' endpointId sender hBlockedSend hStep,
    endpointSend_preserves_blockedOnReceiveNotRunnable st st' endpointId sender hBlockedReceive hStep⟩

-- Await-receive: always blocking (receiver removed from runnable)
-- Simpler than endpointSend because there is no handshake case.

theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  intro tid tcb hObj hRun
  rw [removeRunnable_preserves_objects] at hObj
  have hNeRecv : tid ≠ receiver := removeRunnable_mem_implies_ne st2 receiver tid hRun
  have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid receiver _ tcb ep' hNeRecv hStore hTcbStep hObj
  have hRunOrig : tid ∈ st.scheduler.runnable := by
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
    have hMem := removeRunnable_mem_implies_mem st2 receiver tid hRun
    rw [hSchedEq2, hSchedEq1] at hMem; exact hMem
  exact hInv tid tcb hObjOrig hRunOrig

theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  intro tid tcb epId hObj hBlocked
  rw [removeRunnable_preserves_objects] at hObj
  by_cases hEqRecv : tid = receiver
  · subst hEqRecv; simp [removeRunnable, List.mem_filter]
  · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid receiver _ tcb ep' hEqRecv hStore hTcbStep hObj
    have hNotRun := hInv tid tcb epId hObjOrig hBlocked
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
    intro hRunMem
    have hMem := removeRunnable_mem_implies_mem st2 receiver tid hRunMem
    rw [hSchedEq2, hSchedEq1] at hMem
    exact hNotRun hMem

theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  intro tid tcb epId hObj hBlocked
  rw [removeRunnable_preserves_objects] at hObj
  by_cases hEqRecv : tid = receiver
  · subst hEqRecv; simp [removeRunnable, List.mem_filter]
  · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid receiver _ tcb ep' hEqRecv hStore hTcbStep hObj
    have hNotRun := hInv tid tcb epId hObjOrig hBlocked
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
    intro hRunMem
    have hMem := removeRunnable_mem_implies_mem st2 receiver tid hRunMem
    rw [hSchedEq2, hSchedEq1] at hMem
    exact hNotRun hMem

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  exact ⟨endpointAwaitReceive_preserves_runnableThreadIpcReady st st' endpointId receiver hReady hStep,
    endpointAwaitReceive_preserves_blockedOnSendNotRunnable st st' endpointId receiver hBlockedSend hStep,
    endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable st st' endpointId receiver hBlockedReceive hStep⟩


-- Receive: always unblocking (sender added to runnable with .ready)

theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : runnableThreadIpcReady st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  intro tid tcb hObj hRun
  rw [ensureRunnable_preserves_objects] at hObj
  have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
  have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
  by_cases hEqSender : tid = sender
  · -- sender's ipcState was set to .ready
    subst hEqSender
    unfold storeTcbIpcState at hTcbStep
    cases hLookup : lookupTcb st1 tid with
    | none =>
      simp [hLookup] at hTcbStep; subst hTcbStep
      exfalso; simp [lookupTcb, hObj] at hLookup
    | some origTcb =>
      simp only [hLookup] at hTcbStep
      revert hTcbStep
      cases hInnerStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready }) st1 with
      | error e => simp
      | ok pair =>
        simp only [Except.ok.injEq]
        intro hSt2Eq; subst hSt2Eq
        rw [storeObject_objects_eq st1 pair.2 tid.toObjId _ hInnerStore] at hObj
        cases hObj; rfl
  · -- tid ≠ sender: preserved from pre-state
    have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid sender _ tcb ep' hEqSender hStore hTcbStep hObj
    have hRunOrig : tid ∈ st.scheduler.runnable := by
      rcases ensureRunnable_mem_implies st2 sender tid hRun with hMem | hEq
      · rw [hSchedEq2, hSchedEq1] at hMem; exact hMem
      · exact absurd hEq hEqSender
    exact hInv tid tcb hObjOrig hRunOrig

theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnSendNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  intro tid tcb epId hObj hBlocked
  rw [ensureRunnable_preserves_objects] at hObj
  by_cases hEqSender : tid = sender
  · subst hEqSender
    unfold storeTcbIpcState at hTcbStep
    cases hLookup : lookupTcb st1 tid with
    | none =>
      simp [hLookup] at hTcbStep; subst hTcbStep
      exfalso; simp [lookupTcb, hObj] at hLookup
    | some origTcb =>
      simp only [hLookup] at hTcbStep
      revert hTcbStep
      cases hInnerStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready }) st1 with
      | error e => simp
      | ok pair =>
        simp only [Except.ok.injEq]
        intro hSt2Eq; subst hSt2Eq
        rw [storeObject_objects_eq st1 pair.2 tid.toObjId _ hInnerStore] at hObj
        cases hObj; simp at hBlocked
  · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid sender _ tcb ep' hEqSender hStore hTcbStep hObj
    have hNotRun := hInv tid tcb epId hObjOrig hBlocked
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
    intro hRunMem
    rcases ensureRunnable_mem_implies st2 sender tid hRunMem with hMem | hEq
    · rw [hSchedEq2, hSchedEq1] at hMem; exact hNotRun hMem
    · exact absurd hEq hEqSender

theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : blockedOnReceiveNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  intro tid tcb epId hObj hBlocked
  rw [ensureRunnable_preserves_objects] at hObj
  by_cases hEqSender : tid = sender
  · subst hEqSender
    unfold storeTcbIpcState at hTcbStep
    cases hLookup : lookupTcb st1 tid with
    | none =>
      simp [hLookup] at hTcbStep; subst hTcbStep
      exfalso; simp [lookupTcb, hObj] at hLookup
    | some origTcb =>
      simp only [hLookup] at hTcbStep
      revert hTcbStep
      cases hInnerStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready }) st1 with
      | error e => simp
      | ok pair =>
        simp only [Except.ok.injEq]
        intro hSt2Eq; subst hSt2Eq
        rw [storeObject_objects_eq st1 pair.2 tid.toObjId _ hInnerStore] at hObj
        cases hObj; simp at hBlocked
  · have hObjOrig := chain_tcb_at_other_thread st st1 st2 endpointId tid sender _ tcb ep' hEqSender hStore hTcbStep hObj
    have hNotRun := hInv tid tcb epId hObjOrig hBlocked
    have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
    intro hRunMem
    rcases ensureRunnable_mem_implies st2 sender tid hRunMem with hMem | hEq
    · rw [hSchedEq2, hSchedEq1] at hMem; exact hNotRun hMem
    · exact absurd hEq hEqSender

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hInv with ⟨hReady, hBlockedSend, hBlockedReceive⟩
  exact ⟨endpointReceive_preserves_runnableThreadIpcReady st st' endpointId sender hReady hStep,
    endpointReceive_preserves_blockedOnSendNotRunnable st st' endpointId sender hBlockedSend hStep,
    endpointReceive_preserves_blockedOnReceiveNotRunnable st st' endpointId sender hBlockedReceive hStep⟩


-- ============================================================================
-- H-09: Scheduler invariant bundle preservation
-- ============================================================================

/-- Endpoint send preserves the scheduler invariant bundle.

H-09 (WS-E3): The old proof relied on `st'.scheduler = st.scheduler`. With the
3-step chain, the scheduler IS modified by `removeRunnable`/`ensureRunnable`.
The proof now handles each component individually:
- `queueCurrentConsistent`: removeRunnable clears current when removing it;
  ensureRunnable adds the receiver (who becomes runnable) without changing current.
- `runQueueUnique`: filter preserves Nodup; ensureRunnable only adds if absent.
- `currentThreadValid`: TCB at current thread is preserved through the chain. -/
theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases endpointSend_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hChain⟩
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
  rcases hChain with ⟨hTcbStep, hSt'⟩ | ⟨receiver, hTcbStep, hSt'⟩
  · -- Blocking case: removeRunnable
    subst hSt'
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
    have hSchedEq : st2.scheduler = st.scheduler := by rw [hSchedEq2, hSchedEq1]
    refine ⟨?_, ?_, ?_⟩
    · -- queueCurrentConsistent
      unfold queueCurrentConsistent
      simp only [removeRunnable]
      rw [hSchedEq]
      cases hCurVal : st.scheduler.current with
      | none => simp [hCurVal]
      | some tid =>
        by_cases hEq : tid = sender
        · simp [hEq]
        · simp [hEq]
          simpa [queueCurrentConsistent, hCurVal] using hQueue
    · -- runQueueUnique
      simp only [removeRunnable, runQueueUnique]
      rw [hSchedEq]
      exact List.Nodup.sublist List.filter_sublist hRunq
    · -- currentThreadValid
      unfold currentThreadValid
      simp only [removeRunnable]
      rw [hSchedEq]
      cases hCurVal : st.scheduler.current with
      | none => simp [hCurVal]
      | some tid =>
        by_cases hEq : tid = sender
        · simp [hEq]
        · simp [hEq]
          simp [currentThreadValid, hCurVal] at hCur
          rcases hCur with ⟨tcb, hTcbObj⟩
          have hNeEp : tid.toObjId ≠ endpointId := by
            intro h
            have ⟨ep, hEpObj⟩ := endpointSend_ok_implies_endpoint_object st _ endpointId sender hStep
            rw [h] at hTcbObj; rw [hEpObj] at hTcbObj; cases hTcbObj
          have hTcb1 : st1.objects tid.toObjId = some (.tcb tcb) := by
            rw [storeObject_objects_ne st st1 endpointId tid.toObjId _ hNeEp hStore]; exact hTcbObj
          have hNeObjId : tid.toObjId ≠ sender.toObjId :=
            fun h => hEq (SeLe4n.ThreadId.toObjId_injective tid sender h)
          rw [storeTcbIpcState_preserves_objects_ne st1 st2 sender _ tid.toObjId hNeObjId hTcbStep]
          exact ⟨tcb, hTcb1⟩
  · -- Handshake case: ensureRunnable
    subst hSt'
    have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
    have hSchedEq : st2.scheduler = st.scheduler := by rw [hSchedEq2, hSchedEq1]
    refine ⟨?_, ?_, ?_⟩
    · -- queueCurrentConsistent
      unfold queueCurrentConsistent
      rw [ensureRunnable_preserves_current, hSchedEq]
      cases hCurVal : st.scheduler.current with
      | none => trivial
      | some tid =>
        have hTidInRunnable : tid ∈ st.scheduler.runnable := by
          simpa [queueCurrentConsistent, hCurVal] using hQueue
        simp only [ensureRunnable]
        split
        · rw [hSchedEq]; exact hTidInRunnable
        · exact List.mem_append_left _ (by rw [hSchedEq]; exact hTidInRunnable)
    · -- runQueueUnique
      simp only [runQueueUnique, ensureRunnable]
      split
      · rw [hSchedEq]; exact hRunq
      · next hNotMem =>
        have hRunnableEq : st2.scheduler.runnable = st.scheduler.runnable :=
          congrArg SchedulerState.runnable hSchedEq
        rw [hRunnableEq] at hNotMem ⊢
        rw [List.nodup_append]
        exact ⟨hRunq,
          .cons (fun _ h => absurd h List.not_mem_nil) .nil,
          fun x hxl y hya => by
            rw [List.mem_singleton] at hya; subst hya
            exact fun heq => hNotMem (heq ▸ hxl)⟩
    · -- currentThreadValid
      unfold currentThreadValid
      rw [ensureRunnable_preserves_current, hSchedEq]
      cases hCurVal : st.scheduler.current with
      | none => trivial
      | some tid =>
        rw [ensureRunnable_preserves_objects]
        simp [currentThreadValid, hCurVal] at hCur
        rcases hCur with ⟨tcb, hTcbObj⟩
        have hNeEp : tid.toObjId ≠ endpointId := by
          intro h
          have ⟨ep, hEpObj⟩ := endpointSend_ok_implies_endpoint_object st _ endpointId sender hStep
          rw [h] at hTcbObj; rw [hEpObj] at hTcbObj; cases hTcbObj
        have hTcb1 : st1.objects tid.toObjId = some (.tcb tcb) := by
          rw [storeObject_objects_ne st st1 endpointId tid.toObjId _ hNeEp hStore]; exact hTcbObj
        by_cases hTidRecv : tid.toObjId = receiver.toObjId
        · -- tid shares ObjId with receiver; storeTcbIpcState wrote a TCB there (still a TCB)
          unfold storeTcbIpcState at hTcbStep
          cases hLookup : lookupTcb st1 receiver with
          | none =>
            simp [hLookup] at hTcbStep; subst hTcbStep; exact ⟨tcb, hTcb1⟩
          | some origTcb =>
            simp only [hLookup] at hTcbStep
            revert hTcbStep
            cases hInnerStore : storeObject receiver.toObjId _ st1 with
            | error e => simp
            | ok pair =>
              simp only [Except.ok.injEq]; intro hSt2Eq; subst hSt2Eq
              rw [hTidRecv]
              exact ⟨{ origTcb with ipcState := .ready },
                storeObject_objects_eq st1 pair.2 receiver.toObjId _ hInnerStore⟩
        · exact ⟨tcb, by
            rw [storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hTidRecv hTcbStep]
            exact hTcb1⟩


/-- Endpoint await-receive preserves the scheduler invariant bundle. -/
theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases endpointAwaitReceive_chain st st' endpointId receiver hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
  have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 receiver _ hTcbStep
  have hSchedEq : st2.scheduler = st.scheduler := by rw [hSchedEq2, hSchedEq1]
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent
    unfold queueCurrentConsistent
    simp only [removeRunnable]
    rw [hSchedEq]
    cases hCurVal : st.scheduler.current with
    | none => simp [hCurVal]
    | some tid =>
      by_cases hEq : tid = receiver
      · simp [hEq]
      · simp [hEq]
        simpa [queueCurrentConsistent, hCurVal] using hQueue
  · -- runQueueUnique
    simp only [removeRunnable, runQueueUnique]
    rw [hSchedEq]
    exact List.Nodup.sublist List.filter_sublist hRunq
  · -- currentThreadValid
    unfold currentThreadValid
    simp only [removeRunnable]
    rw [hSchedEq]
    cases hCurVal : st.scheduler.current with
    | none => simp [hCurVal]
    | some tid =>
      by_cases hEq : tid = receiver
      · simp [hEq]
      · simp [hEq]
        simp [currentThreadValid, hCurVal] at hCur
        rcases hCur with ⟨tcb, hTcbObj⟩
        have hNeEp : tid.toObjId ≠ endpointId := by
          intro h
          have ⟨ep, hEpObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st _ endpointId receiver hStep
          rw [h] at hTcbObj; rw [hEpObj] at hTcbObj; cases hTcbObj
        have hTcb1 : st1.objects tid.toObjId = some (.tcb tcb) := by
          rw [storeObject_objects_ne st st1 endpointId tid.toObjId _ hNeEp hStore]; exact hTcbObj
        have hNeTidRecv : tid ≠ receiver := by intro h; exact absurd h hEq
        have hNeObjId : tid.toObjId ≠ receiver.toObjId :=
          fun h => hNeTidRecv (SeLe4n.ThreadId.toObjId_injective tid receiver h)
        exact ⟨tcb, by
          rw [storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hTcbStep]
          exact hTcb1⟩

/-- Endpoint receive preserves the scheduler invariant bundle. -/
theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    schedulerInvariantBundle st' := by
  rcases endpointReceive_chain st st' endpointId sender hStep with ⟨ep', st1, st2, hStore, _, hTcbStep, hSt'⟩
  subst hSt'
  rcases hInv with ⟨hQueue, hRunq, hCur⟩
  have hSchedEq1 := storeObject_scheduler_eq st st1 endpointId _ hStore
  have hSchedEq2 := storeTcbIpcState_preserves_scheduler st1 st2 sender _ hTcbStep
  have hSchedEq : st2.scheduler = st.scheduler := by rw [hSchedEq2, hSchedEq1]
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent
    unfold queueCurrentConsistent
    rw [ensureRunnable_preserves_current, hSchedEq]
    cases hCurVal : st.scheduler.current with
    | none => trivial
    | some tid =>
      have hTidInRunnable : tid ∈ st.scheduler.runnable := by
        simpa [queueCurrentConsistent, hCurVal] using hQueue
      simp only [ensureRunnable]
      split
      · rw [hSchedEq]; exact hTidInRunnable
      · exact List.mem_append_left _ (by rw [hSchedEq]; exact hTidInRunnable)
  · -- runQueueUnique
    simp only [runQueueUnique, ensureRunnable]
    split
    · rw [hSchedEq]; exact hRunq
    · next hNotMem =>
      have hRunnableEq : st2.scheduler.runnable = st.scheduler.runnable :=
        congrArg SchedulerState.runnable hSchedEq
      rw [hRunnableEq] at hNotMem ⊢
      rw [List.nodup_append]
      exact ⟨hRunq,
        .cons (fun _ h => absurd h List.not_mem_nil) .nil,
        fun x hxl y hya => by
          rw [List.mem_singleton] at hya; subst hya
          exact fun heq => hNotMem (heq ▸ hxl)⟩
  · -- currentThreadValid
    unfold currentThreadValid
    rw [ensureRunnable_preserves_current, hSchedEq]
    cases hCurVal : st.scheduler.current with
    | none => trivial
    | some tid =>
      rw [ensureRunnable_preserves_objects]
      simp [currentThreadValid, hCurVal] at hCur
      rcases hCur with ⟨tcb, hTcbObj⟩
      have hNeEp : tid.toObjId ≠ endpointId := by
        intro h
        have ⟨ep, hEpObj⟩ := endpointReceive_ok_implies_endpoint_object st _ endpointId sender hStep
        rw [h] at hTcbObj; rw [hEpObj] at hTcbObj; cases hTcbObj
      have hTcb1 : st1.objects tid.toObjId = some (.tcb tcb) := by
        rw [storeObject_objects_ne st st1 endpointId tid.toObjId _ hNeEp hStore]; exact hTcbObj
      by_cases hTidSender : tid.toObjId = sender.toObjId
      · unfold storeTcbIpcState at hTcbStep
        cases hLookup : lookupTcb st1 sender with
        | none =>
          simp [hLookup] at hTcbStep; subst hTcbStep; exact ⟨tcb, hTcb1⟩
        | some origTcb =>
          simp only [hLookup] at hTcbStep
          revert hTcbStep
          cases hInnerStore : storeObject sender.toObjId _ st1 with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]; intro hSt2Eq; subst hSt2Eq
            rw [hTidSender]
            exact ⟨{ origTcb with ipcState := .ready },
              storeObject_objects_eq st1 pair.2 sender.toObjId _ hInnerStore⟩
      · exact ⟨tcb, by
          rw [storeTcbIpcState_preserves_objects_ne st1 st2 sender _ tid.toObjId hTidSender hTcbStep]
          exact hTcb1⟩


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
