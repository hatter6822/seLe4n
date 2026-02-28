import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

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
-- Endpoint well-formedness definitions
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

def ipcInvariant (st : SystemState) : Prop :=
  (∀ oid ep, st.objects oid = some (.endpoint ep) → endpointInvariant ep) ∧
  (∀ oid ntfn, st.objects oid = some (.notification ntfn) → notificationInvariant ntfn)

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

theorem endpointObjectValid_of_queueWellFormed
    (ep : Endpoint)
    (hWf : endpointQueueWellFormed ep) :
    endpointObjectValid ep := by
  cases hState : ep.state <;> cases hWait : ep.waitingReceiver <;>
    simp [endpointQueueWellFormed, endpointObjectValid, hState, hWait] at hWf ⊢

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
-- WS-E3/H-09: Tracks through storeObject → storeTcbIpcState → removeRunnable/ensureRunnable.
-- ============================================================================

theorem endpointSend_result_wellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
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
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
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
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;>
      simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      revert hStep
      cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
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
          exact ⟨_, storeTcbIpcState_preserves_endpoint pair.2 st2 receiver _ endpointId _
            (storeObject_objects_eq st pair.2 endpointId _ hStore) hTcb,
            by simp [endpointQueueWellFormed]⟩

theorem endpointAwaitReceive_result_wellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  -- endpointAwaitReceive only succeeds on idle/[]/none
  simp [endpointAwaitReceive, hObj] at hStep
  cases hState : ep.state <;> simp [hState] at hStep
  case idle =>
    cases hQueue : ep.queue <;> simp [hQueue] at hStep
    case nil =>
      cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
      case none =>
        revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
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
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ∃ ep', st'.objects endpointId = some (.endpoint ep') ∧ endpointQueueWellFormed ep' := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle => simp [endpointReceive, hObj, hState] at hStep
  | receive => simp [endpointReceive, hObj, hState] at hStep
  | send =>
    cases hQueue : ep.queue with
    | nil =>
      cases hWait : ep.waitingReceiver <;>
        simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : ep.waitingReceiver with
      | some _ => simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep
        simp only [hObj, hState, hQueue, hWait] at hStep
        revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := if tl.isEmpty then .idle else .send, queue := tl, waitingReceiver := none }) st with
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
            refine ⟨_, storeTcbIpcState_preserves_endpoint pair.2 st2 hd _ endpointId _
              (storeObject_objects_eq st pair.2 endpointId _ hStore) hTcb, ?_⟩
            simp only [endpointQueueWellFormed]
            cases tl <;> simp [List.isEmpty]

-- ============================================================================
-- CNode backward-preservation: if post-state has a CNode, pre-state had it.
-- WS-E3/H-09: Multi-step tracking: storeObject(ep) → storeTcbIpcState → removeRunnable/ensureRunnable.
-- ============================================================================

private theorem endpointSend_preserves_cnode
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (cn : CNode) (hCn : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId (.endpoint { state := .send, queue := [sender], waitingReceiver := none }) st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender (.blockedOnSend endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hCn2 : st2.objects oid = some (.cnode cn) := by rwa [removeRunnable_preserves_objects] at hCn
        have hCn1 : pair.2.objects oid = some (.cnode cn) :=
          storeTcbIpcState_cnode_backward pair.2 st2 sender _ oid cn hTcb hCn2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at hCn1; cases hCn1
        · rw [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at hCn1; exact hCn1
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId (.endpoint { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }) st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender (.blockedOnSend endpointId) with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hCn2 : st2.objects oid = some (.cnode cn) := by rwa [removeRunnable_preserves_objects] at hCn
        have hCn1 : pair.2.objects oid = some (.cnode cn) :=
          storeTcbIpcState_cnode_backward pair.2 st2 sender _ oid cn hTcb hCn2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at hCn1; cases hCn1
        · rw [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at hCn1; exact hCn1
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      revert hStep
      cases hStore : storeObject endpointId (.endpoint { state := .idle, queue := [], waitingReceiver := none }) st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver .ready with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          have hCn2 : st2.objects oid = some (.cnode cn) := by
            rwa [ensureRunnable_preserves_objects] at hCn
          have hCn1 : pair.2.objects oid = some (.cnode cn) :=
            storeTcbIpcState_cnode_backward pair.2 st2 receiver _ oid cn hTcb hCn2
          by_cases hEq : oid = endpointId
          · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at hCn1; cases hCn1
          · rw [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at hCn1; exact hCn1

private theorem endpointAwaitReceive_preserves_cnode
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (cn : CNode) (hCn : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hState : ep.state <;> simp [hState] at hStep
  case idle =>
    cases hQueue : ep.queue <;> simp [hQueue] at hStep
    case nil =>
      cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
      case none =>
        revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := .receive, queue := [], waitingReceiver := some receiver }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 receiver (.blockedOnReceive endpointId) with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            have hCn2 : st2.objects oid = some (.cnode cn) := by rwa [removeRunnable_preserves_objects] at hCn
            have hCn1 : pair.2.objects oid = some (.cnode cn) :=
              storeTcbIpcState_cnode_backward pair.2 st2 receiver _ oid cn hTcb hCn2
            by_cases hEq : oid = endpointId
            · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at hCn1; cases hCn1
            · rw [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at hCn1; exact hCn1

private theorem endpointReceive_preserves_cnode
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointReceive endpointId st = .ok (sender, st'))
    (oid : SeLe4n.ObjId) (cn : CNode) (hCn : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle => simp [endpointReceive, hObj, hState] at hStep
  | receive => simp [endpointReceive, hObj, hState] at hStep
  | send =>
    cases hQueue : ep.queue with
    | nil =>
      cases hWait : ep.waitingReceiver <;> simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : ep.waitingReceiver with
      | some _ => simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep
        simp only [hObj, hState, hQueue, hWait] at hStep
        revert hStep
        cases hStore : storeObject endpointId (.endpoint { state := if tl.isEmpty then .idle else .send, queue := tl, waitingReceiver := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 hd .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨hSenderEq, hStEq⟩
            subst hStEq; subst hSenderEq
            have hCn2 : st2.objects oid = some (.cnode cn) := by
              rwa [ensureRunnable_preserves_objects] at hCn
            have hCn1 : pair.2.objects oid = some (.cnode cn) :=
              storeTcbIpcState_cnode_backward pair.2 st2 hd _ oid cn hTcb hCn2
            by_cases hEq : oid = endpointId
            · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at hCn1; cases hCn1
            · rw [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at hCn1; exact hCn1

-- ============================================================================
-- Endpoint backward-preservation: if post-state has an endpoint at oid ≠ target,
-- the pre-state had the same endpoint there.
-- ============================================================================

private theorem endpointSend_preserves_other_endpoint
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ep : Endpoint) (hEp : st'.objects oid = some (.endpoint ep))
    (hNe : oid ≠ endpointId) :
    st.objects oid = some (.endpoint ep) := by
  obtain ⟨epOrig, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : epOrig.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hEp2 : st2.objects oid = some (.endpoint ep) := by rwa [removeRunnable_preserves_objects] at hEp
        have hEp1 := storeTcbIpcState_endpoint_backward pair.2 st2 sender _ oid ep hTcb hEp2
        rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at hEp1
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hEp2 : st2.objects oid = some (.endpoint ep) := by rwa [removeRunnable_preserves_objects] at hEp
        have hEp1 := storeTcbIpcState_endpoint_backward pair.2 st2 sender _ oid ep hTcb hEp2
        rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at hEp1
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : epOrig.queue <;> cases hWait : epOrig.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      revert hStep
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver _ with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          have hEp2 : st2.objects oid = some (.endpoint ep) := by rwa [ensureRunnable_preserves_objects] at hEp
          have hEp1 := storeTcbIpcState_endpoint_backward pair.2 st2 receiver _ oid ep hTcb hEp2
          rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at hEp1

-- ============================================================================
-- Notification backward-preservation through endpoint operations
-- ============================================================================

private theorem endpointSend_preserves_notification
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hStep : endpointSend endpointId sender st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.notification ntfn) := by rwa [removeRunnable_preserves_objects] at hNtfn
        have h1 := storeTcbIpcState_notification_backward pair.2 st2 sender _ oid ntfn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have h2 : st2.objects oid = some (.notification ntfn) := by rwa [removeRunnable_preserves_objects] at hNtfn
        have h1 := storeTcbIpcState_notification_backward pair.2 st2 sender _ oid ntfn hTcb h2
        by_cases hEq : oid = endpointId
        · subst hEq; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
        · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEq hStore] at h1
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      revert hStep
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver _ with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          have h2 : st2.objects oid = some (.notification ntfn) := by rwa [ensureRunnable_preserves_objects] at hNtfn
          have h1 := storeTcbIpcState_notification_backward pair.2 st2 receiver _ oid ntfn hTcb h2
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
  · intro oid ep' hObj
    by_cases hEq : oid = endpointId
    · obtain ⟨ep'', hObj', hWf⟩ := endpointSend_result_wellFormed st st' endpointId sender hStep
      rw [hEq] at hObj; rw [hObj] at hObj'; cases hObj'
      exact ⟨hWf, endpointObjectValid_of_queueWellFormed _ hWf⟩
    · exact hEp oid ep' (endpointSend_preserves_other_endpoint st st' endpointId sender hStep oid ep' hObj hEq)
  · intro oid ntfn hObj
    exact hNtfn oid ntfn (endpointSend_preserves_notification st st' endpointId sender hStep oid ntfn hObj)

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
      rw [hEq] at hObjPost; rw [hObjPost] at hObj'; cases hObj'
      exact ⟨hWf, endpointObjectValid_of_queueWellFormed _ hWf⟩
    · -- Other endpoints preserved backward
      have hBackward : st.objects oid = some (.endpoint ep') := by
        simp [endpointAwaitReceive, hObj] at hStep
        cases hState : ep.state <;> simp [hState] at hStep
        case idle =>
          cases hQueue : ep.queue <;> simp [hQueue] at hStep
          case nil =>
            cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
            case none =>
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
    cases hState : ep.state <;> simp [hState] at hStep
    case idle =>
      cases hQueue : ep.queue <;> simp [hQueue] at hStep
      case nil =>
        cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
        case none =>
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
  obtain ⟨epOrig, hObjEq⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : epOrig.state with
  | idle => simp [endpointReceive, hObjEq, hState] at hStep
  | receive => simp [endpointReceive, hObjEq, hState] at hStep
  | send =>
    cases hQueue : epOrig.queue with
    | nil =>
      cases hWait : epOrig.waitingReceiver <;>
        simp [endpointReceive, hObjEq, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : epOrig.waitingReceiver with
      | some _ => simp [endpointReceive, hObjEq, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep; simp only [hObjEq, hState, hQueue, hWait] at hStep
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
  obtain ⟨epOrig, hObjEq⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : epOrig.state with
  | idle => simp [endpointReceive, hObjEq, hState] at hStep
  | receive => simp [endpointReceive, hObjEq, hState] at hStep
  | send =>
    cases hQueue : epOrig.queue with
    | nil =>
      cases hWait : epOrig.waitingReceiver <;>
        simp [endpointReceive, hObjEq, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : epOrig.waitingReceiver with
      | some _ => simp [endpointReceive, hObjEq, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep; simp only [hObjEq, hState, hQueue, hWait] at hStep
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
    · obtain ⟨ep'', hObj', hWf⟩ := endpointReceive_result_wellFormed st st' endpointId sender hStep
      rw [hEq] at hObjPost; rw [hObjPost] at hObj'; cases hObj'
      exact ⟨hWf, endpointObjectValid_of_queueWellFormed _ hWf⟩
    · exact hEp oid ep' (endpointReceive_preserves_other_endpoint st st' endpointId sender hStep oid ep' hObjPost hEq)
  · intro oid ntfn hObjPost
    exact hNtfn oid ntfn (endpointReceive_preserves_notification st st' endpointId sender hStep oid ntfn hObjPost)

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
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
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
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
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
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
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
          refine ⟨?_, ?_, ?_⟩
          · -- queueCurrentConsistent: current unchanged by ensureRunnable, old members preserved
            unfold queueCurrentConsistent
            rw [ensureRunnable_scheduler_current, hSchedEq]
            cases hCurr : st.scheduler.current with
            | none => trivial
            | some x =>
              have hMem : x ∈ st.scheduler.runnable := by
                have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
              exact ensureRunnable_mem_old st2 receiver x (hSchedEq ▸ hMem)
          · exact ensureRunnable_nodup st2 receiver (hSchedEq ▸ hRQU)
          · -- currentThreadValid: prove via case split on current thread
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
              · -- Current thread IS the receiver: storeTcbIpcState stores a (possibly updated) TCB
                have h1 : pair.2.objects receiver.toObjId = some (.tcb tcb) := by
                  have := tcb_preserved_through_endpoint_store st pair.2 endpointId _ x tcb hTcbObj ⟨ep, hObj⟩ hStore
                  rwa [hNeTid] at this
                have h2 := storeTcbIpcState_tcb_exists_at_target pair.2 st2 receiver _ hTcb ⟨tcb, h1⟩
                rwa [← hNeTid] at h2
              · have hNe2 : x.toObjId ≠ receiver.toObjId := hNeTid
                have h_s1 := storeObject_objects_ne st pair.2 endpointId x.toObjId _ hNe1 hStore
                have h_s2 := storeTcbIpcState_preserves_objects_ne pair.2 st2 receiver _ x.toObjId hNe2 hTcb
                exact ⟨tcb, by rw [h_s2, h_s1]; exact hTcbObj⟩

theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hState : ep.state <;> simp [hState] at hStep
  case idle =>
    cases hQueue : ep.queue <;> simp [hQueue] at hStep
    case nil =>
      cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
      case none =>
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
  cases hState : ep.state with
  | idle => simp [endpointReceive, hObj, hState] at hStep
  | receive => simp [endpointReceive, hObj, hState] at hStep
  | send =>
    cases hQueue : ep.queue with
    | nil =>
      cases hWait : ep.waitingReceiver <;> simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : ep.waitingReceiver with
      | some _ => simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep; simp only [hObj, hState, hQueue, hWait] at hStep
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
-- IPC Scheduler Contract Predicate Preservation (M3.5)
-- WS-E3/H-09: Substantive proofs — these are NON-VACUOUS because the endpoint
-- operations now perform actual IPC state transitions.
-- ============================================================================

/-- Helper: transport a TCB backward through storeObject at endpointId + storeTcbIpcState
    for a thread whose ObjId differs from both the target thread and the endpoint. -/
private theorem tcb_transport_backward
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (obj : KernelObject) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hStore : storeObject endpointId obj st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2)
    (hNeObjId : tid.toObjId ≠ target.toObjId)
    (hNeEp : tid.toObjId ≠ endpointId)
    (hTcbSt2 : st2.objects tid.toObjId = some (.tcb tcb)) :
    st.objects tid.toObjId = some (.tcb tcb) := by
  have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcb).symm.trans hTcbSt2
  exact (storeObject_objects_ne st st1 endpointId tid.toObjId obj hNeEp hStore).symm.trans hTcbSt1

/-- WS-E3/H-09: Blocking path (storeObject + storeTcbIpcState + removeRunnable) preserves
    all three ipcSchedulerContract predicates. Non-target threads are transported backward
    to the pre-state; the target thread is not runnable (removeRunnable). -/
private theorem blocking_path_preserves_contracts
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (epNew : Endpoint)
    (hStore : storeObject endpointId (.endpoint epNew) st = .ok ((), st1))
    (hTcbStep : storeTcbIpcState st1 target ipc = .ok st2)
    (hSchedEq : st2.scheduler = st.scheduler)
    (hReady : runnableThreadIpcReady st)
    (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) :
    ipcSchedulerContractPredicates (removeRunnable st2 target) := by
  have hRunnableEq := congrArg SchedulerState.runnable hSchedEq
  -- Helper: derive hNeEp from the post-storeObject state (endpoint ≠ tcb at same slot)
  have deriveNeEp : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st1.objects tid.toObjId = some (.tcb tcb) → tid.toObjId ≠ endpointId := by
    intro tid tcb hTcbSt1 h; rw [h] at hTcbSt1
    have := storeObject_objects_eq st st1 endpointId (.endpoint epNew) hStore
    rw [this] at hTcbSt1; exact absurd hTcbSt1 (by simp)
  refine ⟨?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid tcb hTcbPost hRunPost
    have ⟨hRunSt2, hNe⟩ := (removeRunnable_mem st2 target tid).mp hRunPost
    have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
    have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
    have hNeEp := deriveNeEp tid tcb hTcbSt1
    have hTcbPre := (storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
    exact hReady tid tcb hTcbPre (show tid ∈ st.scheduler.runnable by rw [← hRunnableEq]; exact hRunSt2)
  · -- blockedOnSendNotRunnable
    intro tid tcb eid hTcbPost hIpcPost
    by_cases hNe : tid = target
    · subst hNe; exact removeRunnable_not_mem_self st2 _
    · have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      have hRunSt := ((removeRunnable_mem st2 target tid).mp hRunPost).1
      exact hBlockSend tid tcb eid hTcbPre hIpcPost (show tid ∈ st.scheduler.runnable by rw [← hRunnableEq]; exact hRunSt)
  · -- blockedOnReceiveNotRunnable
    intro tid tcb eid hTcbPost hIpcPost
    by_cases hNe : tid = target
    · subst hNe; exact removeRunnable_not_mem_self st2 _
    · have hNeObjId : tid.toObjId ≠ target.toObjId := fun h => hNe (threadId_toObjId_injective h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target ipc tid.toObjId hNeObjId hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      have hRunSt := ((removeRunnable_mem st2 target tid).mp hRunPost).1
      exact hBlockRecv tid tcb eid hTcbPre hIpcPost (show tid ∈ st.scheduler.runnable by rw [← hRunnableEq]; exact hRunSt)

/-- WS-E3/H-09: Handshake path (storeObject + storeTcbIpcState(.ready) + ensureRunnable) preserves
    all three ipcSchedulerContract predicates. The target thread gets ipcState = .ready (matching
    runnable status); non-target threads are transported backward. -/
private theorem handshake_path_preserves_contracts
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (epNew : Endpoint)
    (hStore : storeObject endpointId (.endpoint epNew) st = .ok ((), st1))
    (hTcbStep : storeTcbIpcState st1 target .ready = .ok st2)
    (hSchedEq : st2.scheduler = st.scheduler)
    (hReady : runnableThreadIpcReady st)
    (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st) :
    ipcSchedulerContractPredicates (ensureRunnable st2 target) := by
  have hRunnableEq := congrArg SchedulerState.runnable hSchedEq
  have deriveNeEp : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st1.objects tid.toObjId = some (.tcb tcb) → tid.toObjId ≠ endpointId := by
    intro tid tcb hTcbSt1 h; rw [h] at hTcbSt1
    have := storeObject_objects_eq st st1 endpointId (.endpoint epNew) hStore
    rw [this] at hTcbSt1; exact absurd hTcbSt1 (by simp)
  refine ⟨?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid tcb hTcbPost hRunPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · exact storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost)
    · have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hReady tid tcb hTcbPre (show tid ∈ st.scheduler.runnable by rw [← hRunnableEq]; exact hRun)
      · exact absurd hEq hNeTid
  · -- blockedOnSendNotRunnable
    intro tid tcb eid hTcbPost hIpcPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · have := storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost)
      simp_all
    · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hBlockSend tid tcb eid hTcbPre hIpcPost (show tid ∈ st.scheduler.runnable by rw [← hRunnableEq]; exact hRun)
      · exact absurd hEq hNeTid
  · -- blockedOnReceiveNotRunnable
    intro tid tcb eid hTcbPost hIpcPost
    rw [ensureRunnable_preserves_objects] at hTcbPost
    by_cases hNe : tid.toObjId = target.toObjId
    · have := storeTcbIpcState_ipcState_eq st1 st2 target .ready hTcbStep tcb (hNe ▸ hTcbPost)
      simp_all
    · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
      have hTcbSt1 := (storeTcbIpcState_preserves_objects_ne st1 st2 target .ready tid.toObjId hNe hTcbStep).symm.trans hTcbPost
      have hNeEp := deriveNeEp tid tcb hTcbSt1
      have hTcbPre := (storeObject_objects_ne st st1 endpointId tid.toObjId (.endpoint epNew) hNeEp hStore).symm.trans hTcbSt1
      intro hRunPost
      rcases ensureRunnable_mem_reverse st2 target tid hRunPost with hRun | hEq
      · exact hBlockRecv tid tcb eid hTcbPre hIpcPost (show tid ∈ st.scheduler.runnable by rw [← hRunnableEq]; exact hRun)
      · exact absurd hEq hNeTid

-- ============================================================================
-- IPC Scheduler Contract Predicate Preservation (M3.5)
-- WS-E3/H-09: Substantive proofs — these are NON-VACUOUS because the endpoint
-- operations now perform actual IPC state transitions.
-- ============================================================================

theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st2 endpointId _ sender _ hStore hTcb
        exact blocking_path_preserves_contracts st pair.2 st2 endpointId sender _ _ hStore hTcb hSchedEq hReady hBlockSend hBlockRecv
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hSchedEq := scheduler_unchanged_through_store_tcb st pair.2 st2 endpointId _ sender _ hStore hTcb
        exact blocking_path_preserves_contracts st pair.2 st2 endpointId sender _ _ hStore hTcb hSchedEq hReady hBlockSend hBlockRecv
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
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
          exact handshake_path_preserves_contracts st pair.2 st2 endpointId receiver _ hStore hTcb hSchedEq hReady hBlockSend hBlockRecv

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hState : ep.state <;> simp [hState] at hStep
  case idle =>
    cases hQueue : ep.queue <;> simp [hQueue] at hStep
    case nil =>
      cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
      case none =>
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
            exact blocking_path_preserves_contracts st pair.2 st2 endpointId receiver _ _ hStore hTcb hSchedEq hReady hBlockSend hBlockRecv

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle => simp [endpointReceive, hObj, hState] at hStep
  | receive => simp [endpointReceive, hObj, hState] at hStep
  | send =>
    cases hQueue : ep.queue with
    | nil =>
      cases hWait : ep.waitingReceiver <;> simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : ep.waitingReceiver with
      | some _ => simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep; simp only [hObj, hState, hQueue, hWait] at hStep
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
            exact handshake_path_preserves_contracts st pair.2 st2 endpointId hd _ hStore hTcb hSchedEq hReady hBlockSend hBlockRecv

-- ============================================================================
-- M3.5 step-6: per-predicate decomposition of bundled preservation theorems
-- ============================================================================

theorem endpointSend_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).1

theorem endpointSend_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).2.1

theorem endpointSend_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).2.2

theorem endpointAwaitReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    runnableThreadIpcReady st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).1

theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnSendNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).2.1

theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).2.2

theorem endpointReceive_preserves_runnableThreadIpcReady
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    runnableThreadIpcReady st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).1

theorem endpointReceive_preserves_blockedOnSendNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnSendNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).2.1

theorem endpointReceive_preserves_blockedOnReceiveNotRunnable
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (hReady : runnableThreadIpcReady st) (hBlockSend : blockedOnSendNotRunnable st)
    (hBlockRecv : blockedOnReceiveNotRunnable st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    blockedOnReceiveNotRunnable st' :=
  (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender
    ⟨hReady, hBlockSend, hBlockRecv⟩ hStep).2.2

-- ============================================================================
-- Notification uniqueness (F-12 / WS-D4)
-- ============================================================================

def uniqueWaiters (st : SystemState) : Prop :=
  ∀ oid ntfn, st.objects oid = some (.notification ntfn) → ntfn.waitingThreads.Nodup

private theorem list_nodup_append_singleton
    {α : Type} [DecidableEq α]
    (xs : List α) (x : α)
    (hNodup : xs.Nodup) (hNotMem : x ∉ xs) :
    (xs ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hNodup, ?_, ?_⟩
  · exact .cons (fun _ h => absurd h List.not_mem_nil) .nil
  · intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    exact fun heq => hNotMem (heq ▸ ha)

theorem notificationWait_preserves_uniqueWaiters
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hInv : uniqueWaiters st)
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
        (by rw [← hBadge]; exact hStep) with ⟨ntfnOld, ntfnNew, hObjOld, _, hNotMem, hObjNew, hAppend⟩
      rw [hObj] at hObjNew; cases hObjNew
      rw [hAppend]
      exact list_nodup_append_singleton ntfnOld.waitingThreads waiter (hInv notificationId ntfnOld hObjOld) hNotMem
  · -- At other IDs, the notification is preserved backward to pre-state
    unfold notificationWait at hStep
    cases hLookup : st.objects notificationId with
    | none => simp [hLookup] at hStep
    | some obj =>
      cases obj with
      | tcb _ | cnode _ | endpoint _ | vspaceRoot _ => simp [hLookup] at hStep
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
              have hPre : st.objects oid = some (.notification ntfn) := by
                have h2 := storeTcbIpcState_notification_backward pair.2 st2 waiter _ oid ntfn hTcb hObj
                by_cases hEq2 : oid = notificationId
                · exact absurd hEq2 hEq
                · rwa [storeObject_objects_ne st pair.2 notificationId oid _ hEq hStore] at h2
              exact hInv oid ntfn hPre
        | none =>
          simp only [hPend] at hStep
          by_cases hMem : waiter ∈ ntfnOrig.waitingThreads
          · simp [hMem] at hStep
          · simp only [hMem, ite_false] at hStep
            revert hStep
            cases hStore : storeObject notificationId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hTcb : storeTcbIpcState pair.2 waiter _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hStEq⟩
                have hPre : st.objects oid = some (.notification ntfn) := by
                  have hRemObj : (removeRunnable st2 waiter).objects = st2.objects := rfl
                  rw [← hStEq, hRemObj] at hObj
                  have h2 := storeTcbIpcState_notification_backward pair.2 st2 waiter _ oid ntfn hTcb hObj
                  by_cases hEq2 : oid = notificationId
                  · exact absurd hEq2 hEq
                  · rwa [storeObject_objects_ne st pair.2 notificationId oid _ hEq hStore] at h2
                exact hInv oid ntfn hPre

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

/-- notificationWait result notification is well-formed (wait path):
    waiting state, non-empty waiter list (appended), no badge. -/
theorem notificationWait_result_wellFormed_wait
    (waiters : List SeLe4n.ThreadId)
    (waiter : SeLe4n.ThreadId) :
    notificationQueueWellFormed
      { state := .waiting, waitingThreads := waiters ++ [waiter], pendingBadge := none } := by
  unfold notificationQueueWellFormed
  constructor
  · intro h; simp [List.append_eq_nil_iff] at h
  · rfl

-- ============================================================================
-- WS-E4/M-12: Preservation theorems for endpointReply
-- ============================================================================

/-- WS-F1/WS-E4/M-12: endpointReply preserves schedulerInvariantBundle.
Reply stores a TCB (with message) and calls ensureRunnable, similar to
endpointReceive unblocking. Updated for WS-F1 message transfer. -/
theorem endpointReply_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReply target msg st = .ok ((), st')) :
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
      | blockedOnReply _ =>
          simp only [hIpc] at hStep
          cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hTcb] at hStep
          | ok st1 =>
              simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hStEq⟩ := hStep; subst hStEq
              rcases hInv with ⟨hQueue, hRunUnique, hCurrent⟩
              have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hTcb
              refine ⟨?_, ?_, ?_⟩
              · -- queueCurrentConsistent
                unfold queueCurrentConsistent
                rw [ensureRunnable_scheduler_current, hSchedEq]
                cases hCurr : st.scheduler.current with
                | none => trivial
                | some x =>
                  have hMem : x ∈ st.scheduler.runnable := by
                    have := hQueue; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact ensureRunnable_mem_old st1 target x (hSchedEq ▸ hMem)
              · -- runQueueUnique
                exact ensureRunnable_nodup st1 target (hSchedEq ▸ hRunUnique)
              · -- currentThreadValid
                show currentThreadValid (ensureRunnable st1 target)
                unfold currentThreadValid
                simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  simp only []
                  have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCurrent; exact hCurrent
                  by_cases hNeTid : x.toObjId = target.toObjId
                  · have hTargetTcb : ∃ tcb', st.objects target.toObjId = some (.tcb tcb') :=
                      hNeTid ▸ hCTV'
                    have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target .ready (some msg) hTcb hTargetTcb
                    rwa [← hNeTid] at h
                  · rcases hCTV' with ⟨tcb', hTcbObj⟩
                    exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) x.toObjId hNeTid hTcb) ▸ hTcbObj⟩

/-- WS-F1/WS-E4/M-12: endpointReply preserves ipcInvariant.
Reply modifies only a TCB (no endpoint/notification changes).
Updated for WS-F1 message transfer via storeTcbIpcStateAndMessage. -/
theorem endpointReply_preserves_ipcInvariant
    (st st' : SystemState)
    (target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointReply target msg st = .ok ((), st')) :
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
      | blockedOnReply _ =>
          simp only [hIpc] at hStep
          cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hTcb] at hStep
          | ok st1 =>
              simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hStEq⟩ := hStep; subst hStEq
              rcases hInv with ⟨hEpInv, hNtfnInv⟩
              constructor
              · intro oid ep hObj
                have hObjSt1 : st1.objects oid = some (.endpoint ep) := by
                  rwa [ensureRunnable_preserves_objects st1 target] at hObj
                exact hEpInv oid ep (storeTcbIpcStateAndMessage_endpoint_backward st st1 target .ready (some msg) oid ep hTcb hObjSt1)
              · intro oid ntfn hObj
                have hObjSt1 : st1.objects oid = some (.notification ntfn) := by
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
      cases hObj : st.objects endpointId with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
        | endpoint ep =>
          simp only [hObj] at hStep
          have hInvEp := hEpInv endpointId ep hObj
          revert hStep
          cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
          | none => simp [hHead]
          | some headTid =>
            simp only [hHead]
            cases hLookup : lookupTcb st headTid with
            | none => simp [hLookup]
            | some headTcb =>
              simp only [hLookup]
              cases hStore : storeObject endpointId _ st with
              | error e => simp [hStore]
              | ok pair => simp only [hStore]; cases hNext : headTcb.queueNext with
                | none =>
                  simp only [hNext]
                  cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
                  | error e => simp [hFinal]
                  | ok st3 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    rw [hNe] at hObjPost
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none endpointId ep' hFinal hObjPost
                    rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at h1
                    simp at h1; subst h1; cases isReceiveQ <;> exact hInvEp
                | some nextTid =>
                  simp only [hNext]
                  cases hLookupNext : lookupTcb pair.2 nextTid with
                  | none => simp [hLookupNext]
                  | some nextTcb =>
                    simp only [hLookupNext]
                    cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                    | error e => simp [hLink]
                    | ok st2 =>
                      simp only []
                      cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                      | error e => simp [hFinal]
                      | ok st3 =>
                        simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
      cases hObj : st.objects endpointId with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
                  | error e => simp [hStore]
                  | ok pair =>
                    simp only [hStore]
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
                    | error e => simp [hStore]
                    | ok pair =>
                      simp only [hStore]
                      cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                      | error e => simp [hLink1]
                      | ok st2 =>
                        simp only [hLink1]
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
        st'.objects tid.toObjId = some (.tcb tcb') →
        ∃ tcb, st.objects tid.toObjId = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
    (hContract : ipcSchedulerContractPredicates st) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  refine ⟨?_, ?_, ?_⟩
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
                exact ensureRunnable_mem_old st2 pair.1 x (hSchedEq ▸ hMem)
            · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
            · show currentThreadValid (ensureRunnable st2 pair.1)
              unfold currentThreadValid
              simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                by_cases hNeTid : x.toObjId = pair.1.toObjId
                · have hTargetTcb : ∃ t, pair.2.objects pair.1.toObjId = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
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
                  rw [removeRunnable_mem]
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
                  show ∃ tcb, st2.objects x.toObjId = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
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
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  unfold endpointSendDual at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
            ⟨hReady, hBlockSend, hBlockRecv⟩
          -- Now storeTcbIpcStateAndMessage(.ready, receiver) + ensureRunnable
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            refine ⟨?_, ?_, ?_⟩
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
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage(.blockedOnSend) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false sender st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId false sender st st1 tid tcb' hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 sender (.blockedOnSend endpointId) (some msg) hMsg
            refine ⟨?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 sender tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 sender tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 sender tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-F1/TPI-D08: endpointReceiveDual preserves ipcInvariant. -/
theorem endpointReceiveDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcInvariant st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbPendingMessage
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId false st pair.2 pair.1 hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 .ready none hInv1 hMsg
            -- ensureRunnable preserves ipcInvariant
            have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) := by
              rcases hInv2 with ⟨hEp, hNtfn⟩
              exact ⟨fun oid ep' h => hEp oid ep' (by rwa [ensureRunnable_preserves_objects] at h),
                     fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
            -- storeTcbPendingMessage preserves or errors (error path = ensureRunnable)
            revert hStep
            cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
            | ok st4 =>
              simp only [hPend, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact storeTcbPendingMessage_preserves_ipcInvariant _ _ receiver _ hInv3 hPend
            | error _ =>
              simp only [hPend, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact hInv3
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbPendingMessage
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId false st pair.2 pair.1 hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready none hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
            -- Build scheduler invariant for ensureRunnable st2 pair.1
            have hInvER : schedulerInvariantBundle (ensureRunnable st2 pair.1) := by
              refine ⟨?_, ?_, ?_⟩
              · unfold queueCurrentConsistent
                rw [ensureRunnable_scheduler_current, hSchedEq]
                cases hCurr : st.scheduler.current with
                | none => trivial
                | some x =>
                  have hMem : x ∈ st.scheduler.runnable := by
                    have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact ensureRunnable_mem_old st2 pair.1 x (hSchedEq ▸ hMem)
              · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
              · show currentThreadValid (ensureRunnable st2 pair.1)
                unfold currentThreadValid
                simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  simp only []
                  have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                  by_cases hNeTid : x.toObjId = pair.1.toObjId
                  · have hTargetTcb : ∃ t, pair.2.objects pair.1.toObjId = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                    have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 .ready none hMsg hTargetTcb
                    rwa [← hNeTid] at h
                  · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready none x.toObjId hNeTid hMsg) ▸ hTcb1⟩
            -- storeTcbPendingMessage preserves scheduler invariant (scheduler unchanged, TCBs preserved)
            revert hStep
            cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
            | ok st4 =>
              simp only [hPend, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              rcases hInvER with ⟨hQCC', hRQU', hCTV'⟩
              have hSchedPend := storeTcbPendingMessage_scheduler_eq _ _ receiver _ hPend
              refine ⟨?_, ?_, ?_⟩
              · rw [queueCurrentConsistent]; rw [queueCurrentConsistent] at hQCC'
                rwa [hSchedPend]
              · show st4.scheduler.runnable.Nodup
                rw [show st4.scheduler.runnable = (ensureRunnable st2 pair.1).scheduler.runnable from congrArg SchedulerState.runnable hSchedPend]; exact hRQU'
              · unfold currentThreadValid
                rw [hSchedPend]
                cases hCurr : (ensureRunnable st2 pair.1).scheduler.current with
                | none => simp
                | some x =>
                  simp only []
                  have ⟨tcbX, hTcbX⟩ : ∃ tcb', (ensureRunnable st2 pair.1).objects x.toObjId = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV'; exact hCTV'
                  exact storeTcbPendingMessage_tcb_forward _ _ receiver _ x.toObjId tcbX hPend hTcbX
            | error _ =>
              simp only [hPend, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact hInvER
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
                  rw [removeRunnable_mem]
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
                  show ∃ tcb, st2.objects x.toObjId = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
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
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbPendingMessage
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId false st pair.2 pair.1 hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2 pair.1 tid tcb' hPop h)
            ⟨hReady, hBlockSend, hBlockRecv⟩
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready none hMsg
            -- Build contracts for ensureRunnable st2 pair.1 (same handshake pattern as sendDual)
            have hContractER : ipcSchedulerContractPredicates (ensureRunnable st2 pair.1) := by
              refine ⟨?_, ?_, ?_⟩
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
            -- storeTcbPendingMessage preserves contracts (scheduler and ipcStates unchanged)
            revert hStep
            cases hPend : storeTcbPendingMessage (ensureRunnable st2 pair.1) receiver _ with
            | ok st4 =>
              simp only [hPend, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              have hSchedPend := storeTcbPendingMessage_scheduler_eq _ st4 receiver _ hPend
              exact contracts_of_same_scheduler_ipcState _ st4 hSchedPend
                (fun tid tcb'' hTcb'' => storeTcbPendingMessage_tcb_ipcState_backward _ st4 receiver _ tid tcb'' hPend hTcb'')
                hContractER
            | error _ =>
              simp only [hPend, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact hContractER
      | none =>
        -- Blocking: Enqueue → storeTcbIpcState(.blockedOnReceive) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId true receiver st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId true receiver st st1 tid tcb' hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv⟩
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv'⟩
            have hSchedIpc := storeTcbIpcState_scheduler_eq st1 st2 receiver _ hIpc
            refine ⟨?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 receiver tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 receiver tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = receiver
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hIpc).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 receiver tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])

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
      cases hObj : st.objects endpointId with
      | none => simp [hObj] at hStep
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
        | endpoint epOrig =>
          have hInvEp := hEpInv endpointId epOrig hObj
          simp only [hObj] at hStep; revert hStep
          cases hLookup : lookupTcb st tid with
          | none => simp [hLookup]
          | some tcbTid =>
            simp only [hLookup]
            cases hPPrev : tcbTid.queuePPrev with
            | none => simp [hPPrev]
            | some pprev =>
              simp only [hPPrev]
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
                    simp only [hStore1]; cases hNext : tcbTid.queueNext with
                    | none =>
                      simp only [hNext]
                      cases hStore2 : storeObject endpointId _ pair1.2 with
                      | error e => simp
                      | ok pair2 =>
                      simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        rw [hNe] at hObjPost
                        have h := storeTcbQueueLinks_endpoint_backward _ _ tid none none none endpointId ep' hFinal hObjPost
                        rw [storeObject_objects_eq _ _ endpointId _ hStore2] at h
                        simp at h; subst h; cases isSendQ <;> exact hInvEp
                    | some nextTid =>
                      simp only [hNext]
                      cases hLookupN : lookupTcb pair1.2 nextTid with
                      | none => simp
                      | some nextTcb =>
                      simp only [hLookupN]; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      simp only [hLink]; cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
    have hCTV' : ∃ tcb', st.objects ctid.toObjId = some (.tcb tcb') := by
      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
    rcases hCTV' with ⟨tcbC, hTcbC⟩
    exact endpointQueueRemoveDual_tcb_forward st st' endpointId isSendQ tid ctid.toObjId tcbC hStep hTcbC

-- ============================================================================
-- WS-F1: endpointCall / endpointReplyRecv invariant preservation (F-11 remediation)
--
-- TPI-D09: Compound operation preservation proof infrastructure
--
-- Architecture: endpointCall = endpointQueuePopHead + storeTcbIpcStateAndMessage
-- + ensureRunnable + storeTcbIpcState + removeRunnable. endpointReplyRecv =
-- storeTcbIpcStateAndMessage + ensureRunnable + endpointAwaitReceive.
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId) with
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
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnSend endpointId) (some msg) with
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId) hIpc
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
                    rw [removeRunnable_mem]
                    constructor
                    · rw [congrArg SchedulerState.runnable hSchedIpc]
                      apply ensureRunnable_mem_old
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
                    show ∃ tcb, st4.objects x.toObjId = some (.tcb tcb)
                    have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
                      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                    have hNeCaller : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                    have hTcb2 : ∃ tcb2, st2.objects x.toObjId = some (.tcb tcb2) := by
                      by_cases hNeTid : x.toObjId = pair.1.toObjId
                      · have hTargetTcb : ∃ t, pair.2.objects pair.1.toObjId = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
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
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnSend endpointId) (some msg) hMsg
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
                  rw [removeRunnable_mem]
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
                  show ∃ tcb, st2.objects x.toObjId = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId false caller st st1 x.toObjId tcbX hEnq hTcbX
                  have hNeTid : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller (.blockedOnSend endpointId) (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩

/-- WS-F1/TPI-D09: endpointCall preserves ipcSchedulerContractPredicates. -/
theorem endpointCall_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
  unfold endpointCall at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
            ⟨hReady, hBlockSend, hBlockRecv⟩
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId) hIpc
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv'⟩
              refine ⟨?_, ?_, ?_⟩
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
                    have ⟨hRunSt4, _⟩ := (removeRunnable_mem st4 caller tid).mp hRun'
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
                    have ⟨hRunSt4, _⟩ := (removeRunnable_mem st4 caller tid).mp hRun'
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
                    have ⟨hRunSt4, _⟩ := (removeRunnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
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
            ⟨hReady, hBlockSend, hBlockRecv⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnSend endpointId) (some msg) hMsg
            refine ⟨?_, ?_, ?_⟩
            · intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 caller tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 caller tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_mem st2 caller tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-F1/TPI-D09: endpointReplyRecv preserves ipcInvariant.
Chains endpointReply_preserves_ipcInvariant with
endpointAwaitReceive_preserves_ipcInvariant. -/
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
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ =>
      simp only [hIpc] at hStep
      cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
      | error e => simp [hMsg] at hStep
      | ok st1 =>
        simp only [hMsg] at hStep
        have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st1 replyTarget .ready (some msg) hInv hMsg
        -- ensureRunnable preserves objects, so ipcInvariant is preserved
        have hInv2 : ipcInvariant (ensureRunnable st1 replyTarget) := by
          rcases hInv1 with ⟨hEp, hNtfn⟩
          exact ⟨fun oid ep h => hEp oid ep (by rwa [ensureRunnable_preserves_objects] at h),
                 fun oid ntfn h => hNtfn oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)⟩
        -- endpointAwaitReceive preserves ipcInvariant
        cases hAwait : endpointAwaitReceive endpointId receiver (ensureRunnable st1 replyTarget) with
        | error e => simp [hAwait] at hStep
        | ok result =>
          simp only [hAwait, Except.ok.injEq] at hStep
          obtain ⟨_, hEq⟩ := Prod.mk.inj hStep; subst hEq
          exact endpointAwaitReceive_preserves_ipcInvariant _ _ endpointId receiver hInv2 hAwait

/-- WS-F1/TPI-D09: endpointReplyRecv preserves schedulerInvariantBundle.
Chains endpointReply_preserves_schedulerInvariantBundle with
endpointAwaitReceive_preserves_schedulerInvariantBundle. -/
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
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ =>
      simp only [hIpc] at hStep
      cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
      | error e => simp [hMsg] at hStep
      | ok st1 =>
        simp only [hMsg] at hStep
        -- storeTcbIpcStateAndMessage + ensureRunnable preserves schedulerInvariantBundle
        -- (same argument as endpointReply_preserves_schedulerInvariantBundle)
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
              exact ensureRunnable_mem_old st1 replyTarget x (hSchedEq ▸ hMem)
          · exact ensureRunnable_nodup st1 replyTarget (hSchedEq ▸ hRQU)
          · show currentThreadValid (ensureRunnable st1 replyTarget)
            unfold currentThreadValid
            simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
            cases hCurr : st.scheduler.current with
            | none => simp
            | some x =>
              simp only []
              have hCTV' : ∃ tcb', st.objects x.toObjId = some (.tcb tcb') := by
                simp [currentThreadValid, hCurr] at hCTV; exact hCTV
              by_cases hNeTid : x.toObjId = replyTarget.toObjId
              · have hTargetTcb : ∃ t, st.objects replyTarget.toObjId = some (.tcb t) := hNeTid ▸ hCTV'
                have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 replyTarget .ready (some msg) hMsg hTargetTcb
                rwa [← hNeTid] at h
              · rcases hCTV' with ⟨tcb', hTcbObj⟩
                exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) x.toObjId hNeTid hMsg) ▸ hTcbObj⟩
        -- endpointAwaitReceive preserves schedulerInvariantBundle
        cases hAwait : endpointAwaitReceive endpointId receiver (ensureRunnable st1 replyTarget) with
        | error e => simp [hAwait] at hStep
        | ok result =>
          simp only [hAwait, Except.ok.injEq] at hStep
          obtain ⟨_, hEq⟩ := Prod.mk.inj hStep; subst hEq
          exact endpointAwaitReceive_preserves_schedulerInvariantBundle _ _ endpointId receiver hInvMid hAwait

/-- WS-F1/TPI-D09: endpointReply preserves ipcSchedulerContractPredicates.
endpointReply only stores a TCB and calls ensureRunnable; the contract
predicate preservation follows the handshake_path_preserves_contracts pattern
since the target is set to .ready and added to runnable. -/
theorem endpointReply_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReply target msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv⟩
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
    | blockedOnReply _ =>
      simp only [hIpc] at hStep
      cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
      | error e => simp [hMsg] at hStep
      | ok st1 =>
        simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq
        have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hMsg
        refine ⟨?_, ?_, ?_⟩
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

end SeLe4n.Kernel
