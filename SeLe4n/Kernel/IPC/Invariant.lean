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

/-- WS-E4/M-12: endpointReply preserves schedulerInvariantBundle.
Reply stores a TCB and calls ensureRunnable, similar to endpointReceive unblocking. -/
theorem endpointReply_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (target : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : endpointReply target st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnReply _ =>
          simp [hIpc] at hStep
          cases hTcb : storeTcbIpcState st target .ready with
          | error e => simp [hTcb] at hStep
          | ok st1 =>
              simp [hTcb] at hStep; cases hStep
              rcases hInv with ⟨hQueue, hRunUnique, hCurrent⟩
              have hSchedEq := storeTcbIpcState_scheduler_eq st st1 target .ready hTcb
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
                    have h := storeTcbIpcState_tcb_exists_at_target st st1 target .ready hTcb hTargetTcb
                    rwa [← hNeTid] at h
                  · rcases hCTV' with ⟨tcb', hTcbObj⟩
                    exact ⟨tcb', (storeTcbIpcState_preserves_objects_ne st st1 target .ready x.toObjId hNeTid hTcb) ▸ hTcbObj⟩

/-- WS-E4/M-12: endpointReply preserves ipcInvariant.
Reply modifies only a TCB (no endpoint/notification changes). -/
theorem endpointReply_preserves_ipcInvariant
    (st st' : SystemState)
    (target : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hStep : endpointReply target st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnReply _ =>
          simp [hIpc] at hStep
          cases hTcb : storeTcbIpcState st target .ready with
          | error e => simp [hTcb] at hStep
          | ok st1 =>
              simp [hTcb] at hStep; cases hStep
              rcases hInv with ⟨hEpInv, hNtfnInv⟩
              constructor
              · intro oid ep hObj
                have hObjSt1 : st1.objects oid = some (.endpoint ep) := by
                  rwa [ensureRunnable_preserves_objects st1 target] at hObj
                exact hEpInv oid ep (storeTcbIpcState_endpoint_backward st st1 target .ready oid ep hTcb hObjSt1)
              · intro oid ntfn hObj
                have hObjSt1 : st1.objects oid = some (.notification ntfn) := by
                  rwa [ensureRunnable_preserves_objects st1 target] at hObj
                exact hNtfnInv oid ntfn (storeTcbIpcState_notification_backward st st1 target .ready oid ntfn hTcb hObjSt1)

end SeLe4n.Kernel
