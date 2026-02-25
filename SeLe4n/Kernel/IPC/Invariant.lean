import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.IPC.Operations

/-!
# IPC Invariant Preservation Proofs

WS-E4/M-01+M-02+M-12: Rewritten for dual send/receive queue endpoint model,
message payloads, and reply capabilities. All proofs substantive; no placeholders.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-E4/M-01: Endpoint well-formedness definitions (dual-queue model)
-- ============================================================================

/-- WS-E4/M-01: At most one of send/receive queues is non-empty. -/
def endpointQueueWellFormed (ep : Endpoint) : Prop :=
  ep.sendQueue = [] ∨ ep.receiveQueue = []

def notificationQueueWellFormed (ntfn : Notification) : Prop :=
  match ntfn.state with
  | .idle => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge = none
  | .waiting => ntfn.waitingThreads ≠ [] ∧ ntfn.pendingBadge = none
  | .active => ntfn.waitingThreads = [] ∧ ntfn.pendingBadge.isSome

def notificationInvariant (ntfn : Notification) : Prop :=
  notificationQueueWellFormed ntfn

def endpointInvariant (ep : Endpoint) : Prop :=
  endpointQueueWellFormed ep

def ipcInvariant (st : SystemState) : Prop :=
  (∀ oid ep, st.objects oid = some (.endpoint ep) → endpointInvariant ep) ∧
  (∀ oid ntfn, st.objects oid = some (.notification ntfn) → notificationInvariant ntfn)

-- ============================================================================
-- Scheduler-IPC coherence contract predicates (M3.5 + WS-E4/M-12)
-- ============================================================================

def runnableThreadIpcReady (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb,
    st.objects tid.toObjId = some (.tcb tcb) →
    tid ∈ st.scheduler.runnable → tcb.ipcState = .ready

def blockedOnSendNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb epId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnSend epId →
    tid ∉ st.scheduler.runnable

def blockedOnReceiveNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb epId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnReceive epId →
    tid ∉ st.scheduler.runnable

def blockedOnReplyNotRunnable (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb epId,
    st.objects tid.toObjId = some (.tcb tcb) →
    tcb.ipcState = .blockedOnReply epId →
    tid ∉ st.scheduler.runnable

def ipcSchedulerContractPredicates (st : SystemState) : Prop :=
  runnableThreadIpcReady st ∧
  blockedOnSendNotRunnable st ∧
  blockedOnReceiveNotRunnable st ∧
  blockedOnReplyNotRunnable st

-- ============================================================================
-- Private helpers: endpoint/notification preservation through operation chain
-- ============================================================================

/-- Endpoint at the target ID equals the stored endpoint after the chain. -/
private theorem ep_at_target_chain
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStore : storeObject epId (.endpoint ep') st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid ipc = .ok s2) :
    s2.objects epId = some (.endpoint ep') :=
  storeTcbIpcState_preserves_endpoint s1 s2 tid ipc epId ep'
    (storeObject_objects_eq st s1 epId _ hStore) hTcb

-- ============================================================================
-- IPC-invariant preservation for endpoint operations
-- ============================================================================

theorem endpointSend_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : MessagePayload)
    (hInv : ipcInvariant st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEps, hNtfns⟩
  unfold endpointSend at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    have hWf := hEps endpointId ep hObj
    match hRecv : ep.receiveQueue with
    | receiver :: restRecv =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue, restRecv⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          constructor
          · intro oid ep' hObj'
            rw [ensureRunnable_preserves_objects] at hObj'
            by_cases hEq : oid = endpointId
            · subst hEq
              rw [ep_at_target_chain st s1 s2 oid _ receiver .ready hStore hTcb] at hObj'
              cases hObj'; unfold endpointInvariant endpointQueueWellFormed
              rcases hWf with h | h
              · exact Or.inl h
              · simp [h] at hRecv
            · exact hEps oid ep' (by
                have := storeTcbIpcState_endpoint_backward s1 s2 receiver .ready oid ep' hTcb hObj'
                rwa [storeObject_objects_ne st s1 endpointId oid _ hEq hStore] at this)
          · intro oid ntfn hObj'
            rw [ensureRunnable_preserves_objects] at hObj'
            have h1 := storeTcbIpcState_notification_backward s1 s2 receiver .ready oid ntfn hTcb hObj'
            have hNe : oid ≠ endpointId := by
              intro h; subst h; rw [storeObject_objects_eq st s1 oid _ hStore] at h1; cases h1
            rw [storeObject_objects_ne st s1 endpointId oid _ hNe hStore] at h1
            exact hNtfns oid ntfn h1
    | [] =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue ++ [(sender, msg)], []⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender (.blockedOnSend endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          constructor
          · intro oid ep' hObj'
            rw [removeRunnable_preserves_objects] at hObj'
            by_cases hEq : oid = endpointId
            · subst hEq
              rw [ep_at_target_chain st s1 s2 oid _ sender _ hStore hTcb] at hObj'
              cases hObj'; exact Or.inr rfl
            · exact hEps oid ep' (by
                have := storeTcbIpcState_endpoint_backward s1 s2 sender _ oid ep' hTcb hObj'
                rwa [storeObject_objects_ne st s1 endpointId oid _ hEq hStore] at this)
          · intro oid ntfn hObj'
            rw [removeRunnable_preserves_objects] at hObj'
            have h1 := storeTcbIpcState_notification_backward s1 s2 sender _ oid ntfn hTcb hObj'
            have hNe : oid ≠ endpointId := by
              intro h; subst h; rw [storeObject_objects_eq st s1 oid _ hStore] at h1; cases h1
            rw [storeObject_objects_ne st s1 endpointId oid _ hNe hStore] at h1
            exact hNtfns oid ntfn h1

theorem endpointAwaitReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × MessagePayload))
    (hInv : ipcInvariant st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEps, hNtfns⟩
  unfold endpointAwaitReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    have hWf := hEps endpointId ep hObj
    match hSend : ep.sendQueue with
    | (sender, sMsg) :: restSend =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨restSend, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          constructor
          · intro oid ep' hObj'
            rw [ensureRunnable_preserves_objects] at hObj'
            by_cases hEq : oid = endpointId
            · subst hEq
              rw [ep_at_target_chain st s1 s2 oid _ sender .ready hStore hTcb] at hObj'
              cases hObj'; unfold endpointInvariant endpointQueueWellFormed
              rcases hWf with h | h
              · simp [h] at hSend
              · exact Or.inr h
            · exact hEps oid ep' (by
                have := storeTcbIpcState_endpoint_backward s1 s2 sender .ready oid ep' hTcb hObj'
                rwa [storeObject_objects_ne st s1 endpointId oid _ hEq hStore] at this)
          · intro oid ntfn hObj'
            rw [ensureRunnable_preserves_objects] at hObj'
            have h1 := storeTcbIpcState_notification_backward s1 s2 sender .ready oid ntfn hTcb hObj'
            have hNe : oid ≠ endpointId := by
              intro h; subst h; rw [storeObject_objects_eq st s1 oid _ hStore] at h1; cases h1
            rw [storeObject_objects_ne st s1 endpointId oid _ hNe hStore] at h1
            exact hNtfns oid ntfn h1
    | [] =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨[], ep.receiveQueue ++ [receiver]⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver (.blockedOnReceive endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          constructor
          · intro oid ep' hObj'
            rw [removeRunnable_preserves_objects] at hObj'
            by_cases hEq : oid = endpointId
            · subst hEq
              rw [ep_at_target_chain st s1 s2 oid _ receiver _ hStore hTcb] at hObj'
              cases hObj'; exact Or.inl rfl
            · exact hEps oid ep' (by
                have := storeTcbIpcState_endpoint_backward s1 s2 receiver _ oid ep' hTcb hObj'
                rwa [storeObject_objects_ne st s1 endpointId oid _ hEq hStore] at this)
          · intro oid ntfn hObj'
            rw [removeRunnable_preserves_objects] at hObj'
            have h1 := storeTcbIpcState_notification_backward s1 s2 receiver _ oid ntfn hTcb hObj'
            have hNe : oid ≠ endpointId := by
              intro h; subst h; rw [storeObject_objects_eq st s1 oid _ hStore] at h1; cases h1
            rw [storeObject_objects_ne st s1 endpointId oid _ hNe hStore] at h1
            exact hNtfns oid ntfn h1

theorem endpointReceive_preserves_ipcInvariant
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × MessagePayload)
    (hInv : ipcInvariant st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEps, hNtfns⟩
  unfold endpointReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    have hWf := hEps endpointId ep hObj
    match hSend : ep.sendQueue with
    | [] => simp [hSend] at hStep
    | (sender, sMsg) :: rest =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨rest, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          constructor
          · intro oid ep' hObj'
            rw [ensureRunnable_preserves_objects] at hObj'
            by_cases hEq : oid = endpointId
            · subst hEq
              rw [ep_at_target_chain st s1 s2 oid _ sender .ready hStore hTcb] at hObj'
              cases hObj'; unfold endpointInvariant endpointQueueWellFormed
              rcases hWf with h | h
              · simp [h] at hSend
              · exact Or.inr h
            · exact hEps oid ep' (by
                have := storeTcbIpcState_endpoint_backward s1 s2 sender .ready oid ep' hTcb hObj'
                rwa [storeObject_objects_ne st s1 endpointId oid _ hEq hStore] at this)
          · intro oid ntfn hObj'
            rw [ensureRunnable_preserves_objects] at hObj'
            have h1 := storeTcbIpcState_notification_backward s1 s2 sender .ready oid ntfn hTcb hObj'
            have hNe : oid ≠ endpointId := by
              intro h; subst h; rw [storeObject_objects_eq st s1 oid _ hStore] at h1; cases h1
            rw [storeObject_objects_ne st s1 endpointId oid _ hNe hStore] at h1
            exact hNtfns oid ntfn h1

-- ============================================================================
-- Unique waiters for notifications
-- ============================================================================

def uniqueWaiters (st : SystemState) : Prop :=
  ∀ oid ntfn,
    st.objects oid = some (.notification ntfn) →
    ntfn.waitingThreads.Nodup

-- ============================================================================
-- Notification well-formedness results
-- ============================================================================

theorem notificationSignal_result_wellFormed_wake
    (rest : List SeLe4n.ThreadId) :
    notificationQueueWellFormed
      { state := if rest.isEmpty then .idle else .waiting, waitingThreads := rest, pendingBadge := none } := by
  cases rest with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ => exact ⟨fun h => by simp at h, rfl⟩

theorem notificationSignal_result_wellFormed_merge
    (mergedBadge : SeLe4n.Badge) :
    notificationQueueWellFormed
      { state := .active, waitingThreads := [], pendingBadge := some mergedBadge } := by
  exact ⟨rfl, rfl⟩

theorem notificationWait_result_wellFormed_badge :
    notificationQueueWellFormed
      { state := .idle, waitingThreads := ([] : List SeLe4n.ThreadId), pendingBadge := none } := by
  exact ⟨rfl, rfl⟩

theorem notificationWait_result_wellFormed_wait
    (ntfn : Notification) (waiter : SeLe4n.ThreadId) :
    notificationQueueWellFormed
      { state := .waiting, waitingThreads := ntfn.waitingThreads ++ [waiter], pendingBadge := none } := by
  exact ⟨fun h => by cases ntfn.waitingThreads <;> simp at h, rfl⟩

-- ============================================================================
-- Endpoint operations preserve CNode objects (frame conditions)
-- ============================================================================

/-- Helper: CNode preserved through storeObject(endpoint) + storeTcbIpcState chain. -/
private theorem cnode_preserved_chain
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (cnodeId : SeLe4n.ObjId) (cn : CNode)
    (hNe : cnodeId ≠ epId)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStore : storeObject epId (.endpoint ep') st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid ipc = .ok s2) :
    s2.objects cnodeId = some (.cnode cn) :=
  storeTcbIpcState_preserves_cnode s1 s2 tid ipc cnodeId cn
    (by rw [storeObject_objects_ne st s1 epId cnodeId _ hNe hStore]; exact hCn) hTcb

theorem endpointSend_preserves_cnode
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : MessagePayload)
    (cnodeId : SeLe4n.ObjId) (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    st'.objects cnodeId = some (.cnode cn) := by
  unfold endpointSend at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hRecv : ep.receiveQueue with
    | receiver :: restRecv =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue, restRecv⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq; rw [ensureRunnable_preserves_objects]
          exact cnode_preserved_chain st s1 s2 endpointId _ receiver .ready cnodeId cn
            (by intro h; subst h; rw [hCn] at hObj; cases hObj) hCn hStore hTcb
    | [] =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue ++ [(sender, msg)], []⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender (.blockedOnSend endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq; rw [removeRunnable_preserves_objects]
          exact cnode_preserved_chain st s1 s2 endpointId _ sender _ cnodeId cn
            (by intro h; subst h; rw [hCn] at hObj; cases hObj) hCn hStore hTcb

theorem endpointAwaitReceive_preserves_cnode
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × MessagePayload))
    (cnodeId : SeLe4n.ObjId) (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    st'.objects cnodeId = some (.cnode cn) := by
  unfold endpointAwaitReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hSend : ep.sendQueue with
    | (sender, sMsg) :: restSend =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨restSend, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq; rw [ensureRunnable_preserves_objects]
          exact cnode_preserved_chain st s1 s2 endpointId _ sender .ready cnodeId cn
            (by intro h; subst h; rw [hCn] at hObj; cases hObj) hCn hStore hTcb
    | [] =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨[], ep.receiveQueue ++ [receiver]⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver (.blockedOnReceive endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq; rw [removeRunnable_preserves_objects]
          exact cnode_preserved_chain st s1 s2 endpointId _ receiver _ cnodeId cn
            (by intro h; subst h; rw [hCn] at hObj; cases hObj) hCn hStore hTcb

theorem endpointReceive_preserves_cnode
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × MessagePayload)
    (cnodeId : SeLe4n.ObjId) (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    st'.objects cnodeId = some (.cnode cn) := by
  unfold endpointReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hSend : ep.sendQueue with
    | [] => simp [hSend] at hStep
    | (sender, sMsg) :: rest =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨rest, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq; rw [ensureRunnable_preserves_objects]
          exact cnode_preserved_chain st s1 s2 endpointId _ sender .ready cnodeId cn
            (by intro h; subst h; rw [hCn] at hObj; cases hObj) hCn hStore hTcb

-- ============================================================================
-- Scheduler invariant bundle preservation
-- ============================================================================

/-- If a TCB exists at tid.toObjId before storeTcbIpcState, one still exists after. -/
private theorem storeTcbIpcState_tcb_still_exists
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (tcb : TCB) (hTcb : st.objects tid.toObjId = some (.tcb tcb)) :
    ∃ tcb', st'.objects tid.toObjId = some (.tcb tcb') := by
  unfold storeTcbIpcState at hStep
  have hLookup : lookupTcb st tid = some tcb := by unfold lookupTcb; simp [hTcb]
  simp only [hLookup] at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hStore] at hStep
  | ok pair =>
    simp only [hStore] at hStep
    have := Except.ok.inj hStep; subst this
    exact ⟨{ tcb with ipcState := ipc }, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

/-- Helper: currentThreadValid preserved through storeObject(endpoint) + storeTcbIpcState chain. -/
private theorem currentThreadValid_through_chain
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (epOrig epNew : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hValid : currentThreadValid st)
    (hEp : st.objects epId = some (.endpoint epOrig))
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid ipc = .ok s2) :
    currentThreadValid s2 := by
  unfold currentThreadValid at hValid ⊢
  rw [storeTcbIpcState_scheduler_eq s1 s2 tid ipc hTcb,
      storeObject_scheduler_eq st s1 epId _ hStore]
  cases hc : st.scheduler.current with
  | none => trivial
  | some ctid =>
    simp only [hc] at hValid ⊢
    rcases hValid with ⟨tcb, hTcbObj⟩
    have hNeEp : ctid.toObjId ≠ epId := by
      intro h; rw [h] at hTcbObj; rw [hEp] at hTcbObj; cases hTcbObj
    have h1 : s1.objects ctid.toObjId = some (.tcb tcb) := by
      rw [storeObject_objects_ne st s1 epId ctid.toObjId _ hNeEp hStore]; exact hTcbObj
    by_cases hEq : ctid.toObjId = tid.toObjId
    · rw [hEq]; exact storeTcbIpcState_tcb_still_exists s1 s2 tid ipc hTcb tcb (hEq ▸ h1)
    · exact ⟨tcb, by rw [storeTcbIpcState_preserves_objects_ne s1 s2 tid ipc ctid.toObjId hEq hTcb]; exact h1⟩

/-- Scheduler invariant bundle preserved through storeObject + storeTcbIpcState + ensureRunnable. -/
private theorem schedulerBundle_through_ensure
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (epOrig epNew : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hBundle : schedulerInvariantBundle st)
    (hEp : st.objects epId = some (.endpoint epOrig))
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid ipc = .ok s2) :
    schedulerInvariantBundle (ensureRunnable s2 tid) := by
  rcases hBundle with ⟨hCurr, hUniq, hValid⟩
  have hSchedStore := storeObject_scheduler_eq st s1 epId _ hStore
  have hSchedTcb := storeTcbIpcState_scheduler_eq s1 s2 tid ipc hTcb
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent
    unfold queueCurrentConsistent at hCurr ⊢
    rw [ensureRunnable_scheduler_current, hSchedTcb, hSchedStore]
    cases hc : st.scheduler.current with
    | none => trivial
    | some ctid =>
      simp only [hc] at hCurr
      exact ensureRunnable_mem_old s2 tid ctid (by rw [hSchedTcb, hSchedStore]; exact hCurr)
  · exact ensureRunnable_nodup s2 tid (by rw [hSchedTcb, hSchedStore]; exact hUniq)
  · -- currentThreadValid
    have h_chain := currentThreadValid_through_chain st s1 s2 epId epOrig epNew tid ipc hValid hEp hStore hTcb
    unfold currentThreadValid at h_chain ⊢
    rw [storeTcbIpcState_scheduler_eq s1 s2 tid ipc hTcb,
        storeObject_scheduler_eq st s1 epId _ hStore] at h_chain
    rw [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects,
        hSchedTcb, hSchedStore]
    exact h_chain

/-- Scheduler invariant bundle preserved through storeObject + storeTcbIpcState + removeRunnable. -/
private theorem schedulerBundle_through_remove
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (epOrig epNew : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hBundle : schedulerInvariantBundle st)
    (hEp : st.objects epId = some (.endpoint epOrig))
    (hStore : storeObject epId (.endpoint epNew) st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid ipc = .ok s2) :
    schedulerInvariantBundle (removeRunnable s2 tid) := by
  rcases hBundle with ⟨hCurr, hUniq, hValid⟩
  have hSchedStore := storeObject_scheduler_eq st s1 epId _ hStore
  have hSchedTcb := storeTcbIpcState_scheduler_eq s1 s2 tid ipc hTcb
  refine ⟨?_, ?_, ?_⟩
  · -- queueCurrentConsistent
    unfold queueCurrentConsistent at hCurr ⊢
    rw [removeRunnable_scheduler_current, hSchedTcb, hSchedStore]
    cases hc : st.scheduler.current with
    | none => trivial
    | some ctid =>
      simp only [hc] at hCurr ⊢
      by_cases heq : ctid = tid
      · subst heq; simp
      · simp [show some ctid ≠ some tid from fun h => heq (Option.some.inj h)]
        rw [removeRunnable_mem]
        exact ⟨by rw [hSchedTcb, hSchedStore]; exact hCurr, heq⟩
  · exact removeRunnable_nodup s2 tid (by rw [hSchedTcb, hSchedStore]; exact hUniq)
  · -- currentThreadValid
    have h_chain := currentThreadValid_through_chain st s1 s2 epId epOrig epNew tid ipc hValid hEp hStore hTcb
    unfold currentThreadValid at h_chain ⊢
    rw [storeTcbIpcState_scheduler_eq s1 s2 tid ipc hTcb,
        storeObject_scheduler_eq st s1 epId _ hStore] at h_chain
    rw [removeRunnable_scheduler_current, removeRunnable_preserves_objects,
        hSchedTcb, hSchedStore]
    cases hc : st.scheduler.current with
    | none => trivial
    | some ctid =>
      simp only [hc] at h_chain ⊢
      by_cases heq : ctid = tid
      · subst heq; simp
      · simp [show some ctid ≠ some tid from fun h => heq (Option.some.inj h)]
        exact h_chain

theorem endpointSend_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : MessagePayload)
    (hBundle : schedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointSend at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hRecv : ep.receiveQueue with
    | receiver :: restRecv =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue, restRecv⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact schedulerBundle_through_ensure st s1 s2 endpointId ep _ receiver .ready
            hBundle hObj hStore hTcb
    | [] =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue ++ [(sender, msg)], []⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender (.blockedOnSend endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact schedulerBundle_through_remove st s1 s2 endpointId ep _ sender _
            hBundle hObj hStore hTcb

theorem endpointAwaitReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × MessagePayload))
    (hBundle : schedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    schedulerInvariantBundle st' := by
  unfold endpointAwaitReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hSend : ep.sendQueue with
    | (sender, sMsg) :: restSend =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨restSend, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact schedulerBundle_through_ensure st s1 s2 endpointId ep _ sender .ready
            hBundle hObj hStore hTcb
    | [] =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨[], ep.receiveQueue ++ [receiver]⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver (.blockedOnReceive endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact schedulerBundle_through_remove st s1 s2 endpointId ep _ receiver _
            hBundle hObj hStore hTcb

theorem endpointReceive_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × MessagePayload)
    (hBundle : schedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hSend : ep.sendQueue with
    | [] => simp [hSend] at hStep
    | (sender, sMsg) :: rest =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨rest, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact schedulerBundle_through_ensure st s1 s2 endpointId ep _ sender .ready
            hBundle hObj hStore hTcb

-- ============================================================================
-- WS-E4/M-12: IPC-scheduler contract predicate preservation helpers
-- ============================================================================

/-- Contract predicates preserved through storeObject(endpoint) + storeTcbIpcState(.ready)
    + ensureRunnable. Used by the handshake branch of endpoint operations. -/
private theorem contractPredicates_through_ensure
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId)
    (hInv : ipcSchedulerContractPredicates st)
    (hStore : storeObject epId (.endpoint ep') st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid .ready = .ok s2) :
    ipcSchedulerContractPredicates (ensureRunnable s2 tid) := by
  rcases hInv with ⟨hReady, hSend, hRecv, hReply⟩
  have hSchedStore := storeObject_scheduler_eq st s1 epId _ hStore
  have hSchedTcb := storeTcbIpcState_scheduler_eq s1 s2 tid .ready hTcb
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid' tcb' hObj' hMem'
    rw [ensureRunnable_preserves_objects] at hObj'
    rcases ensureRunnable_mem_reverse s2 tid tid' hMem' with hOld | hEqTid
    · -- tid' was already runnable in s2
      rw [hSchedTcb, hSchedStore] at hOld
      by_cases hEq : tid'.toObjId = tid.toObjId
      · -- tid' maps to same ObjId as tid, so it got the .ready ipcState
        exact storeTcbIpcState_ipcState_eq s1 s2 tid .ready hTcb tcb' (hEq ▸ hObj')
      · -- tid' is a different thread; its TCB is unchanged
        have hObjS1 : s1.objects tid'.toObjId = some (.tcb tcb') :=
          by rwa [storeTcbIpcState_preserves_objects_ne s1 s2 tid .ready tid'.toObjId hEq hTcb] at hObj'
        have hNe : tid'.toObjId ≠ epId := by
          intro h; rw [h, storeObject_objects_eq st s1 epId _ hStore] at hObjS1; cases hObjS1
        rw [storeObject_objects_ne st s1 epId tid'.toObjId _ hNe hStore] at hObjS1
        exact hReady tid' tcb' hObjS1 hOld
    · -- tid' = tid, so ipcState was set to .ready
      subst hEqTid
      exact storeTcbIpcState_ipcState_eq s1 s2 tid' .ready hTcb tcb' hObj'
  · -- blockedOnSendNotRunnable
    intro tid' tcb' epId' hObj' hIpc' hMem'
    rw [ensureRunnable_preserves_objects] at hObj'
    rcases ensureRunnable_mem_reverse s2 tid tid' hMem' with hOld | hEqTid
    · rw [hSchedTcb, hSchedStore] at hOld
      by_cases hEq : tid'.toObjId = tid.toObjId
      · -- Same ObjId as tid → ipcState is .ready, contradicts blockedOnSend
        have := storeTcbIpcState_ipcState_eq s1 s2 tid .ready hTcb tcb' (hEq ▸ hObj')
        rw [this] at hIpc'; cases hIpc'
      · have hObjS1 : s1.objects tid'.toObjId = some (.tcb tcb') :=
          by rwa [storeTcbIpcState_preserves_objects_ne s1 s2 tid .ready tid'.toObjId hEq hTcb] at hObj'
        have hNe : tid'.toObjId ≠ epId := by
          intro h; rw [h, storeObject_objects_eq st s1 epId _ hStore] at hObjS1; cases hObjS1
        rw [storeObject_objects_ne st s1 epId tid'.toObjId _ hNe hStore] at hObjS1
        exact absurd hOld (hSend tid' tcb' epId' hObjS1 hIpc')
    · -- tid' = tid → ipcState is .ready, contradicts blockedOnSend
      subst hEqTid
      have := storeTcbIpcState_ipcState_eq s1 s2 tid' .ready hTcb tcb' hObj'
      rw [this] at hIpc'; cases hIpc'
  · -- blockedOnReceiveNotRunnable
    intro tid' tcb' epId' hObj' hIpc' hMem'
    rw [ensureRunnable_preserves_objects] at hObj'
    rcases ensureRunnable_mem_reverse s2 tid tid' hMem' with hOld | hEqTid
    · rw [hSchedTcb, hSchedStore] at hOld
      by_cases hEq : tid'.toObjId = tid.toObjId
      · have := storeTcbIpcState_ipcState_eq s1 s2 tid .ready hTcb tcb' (hEq ▸ hObj')
        rw [this] at hIpc'; cases hIpc'
      · have hObjS1 : s1.objects tid'.toObjId = some (.tcb tcb') :=
          by rwa [storeTcbIpcState_preserves_objects_ne s1 s2 tid .ready tid'.toObjId hEq hTcb] at hObj'
        have hNe : tid'.toObjId ≠ epId := by
          intro h; rw [h, storeObject_objects_eq st s1 epId _ hStore] at hObjS1; cases hObjS1
        rw [storeObject_objects_ne st s1 epId tid'.toObjId _ hNe hStore] at hObjS1
        exact absurd hOld (hRecv tid' tcb' epId' hObjS1 hIpc')
    · subst hEqTid
      have := storeTcbIpcState_ipcState_eq s1 s2 tid' .ready hTcb tcb' hObj'
      rw [this] at hIpc'; cases hIpc'
  · -- blockedOnReplyNotRunnable
    intro tid' tcb' epId' hObj' hIpc' hMem'
    rw [ensureRunnable_preserves_objects] at hObj'
    rcases ensureRunnable_mem_reverse s2 tid tid' hMem' with hOld | hEqTid
    · rw [hSchedTcb, hSchedStore] at hOld
      by_cases hEq : tid'.toObjId = tid.toObjId
      · have := storeTcbIpcState_ipcState_eq s1 s2 tid .ready hTcb tcb' (hEq ▸ hObj')
        rw [this] at hIpc'; cases hIpc'
      · have hObjS1 : s1.objects tid'.toObjId = some (.tcb tcb') :=
          by rwa [storeTcbIpcState_preserves_objects_ne s1 s2 tid .ready tid'.toObjId hEq hTcb] at hObj'
        have hNe : tid'.toObjId ≠ epId := by
          intro h; rw [h, storeObject_objects_eq st s1 epId _ hStore] at hObjS1; cases hObjS1
        rw [storeObject_objects_ne st s1 epId tid'.toObjId _ hNe hStore] at hObjS1
        exact absurd hOld (hReply tid' tcb' epId' hObjS1 hIpc')
    · subst hEqTid
      have := storeTcbIpcState_ipcState_eq s1 s2 tid' .ready hTcb tcb' hObj'
      rw [this] at hIpc'; cases hIpc'

/-- Contract predicates preserved through storeObject(endpoint) + storeTcbIpcState(any)
    + removeRunnable. Used by the blocking branch of endpoint operations. -/
private theorem contractPredicates_through_remove
    (st s1 s2 : SystemState) (epId : SeLe4n.ObjId) (ep' : Endpoint)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : ipcSchedulerContractPredicates st)
    (hStore : storeObject epId (.endpoint ep') st = .ok ((), s1))
    (hTcb : storeTcbIpcState s1 tid ipc = .ok s2) :
    ipcSchedulerContractPredicates (removeRunnable s2 tid) := by
  rcases hInv with ⟨hReady, hSend, hRecv, hReply⟩
  have hSchedStore := storeObject_scheduler_eq st s1 epId _ hStore
  have hSchedTcb := storeTcbIpcState_scheduler_eq s1 s2 tid ipc hTcb
  -- Shared helper: for tid' ≠ tid, recover original TCB from st
  have restore : ∀ (tid' : SeLe4n.ThreadId) (tcb' : TCB),
      s2.objects tid'.toObjId = some (.tcb tcb') →
      tid' ≠ tid →
      st.objects tid'.toObjId = some (.tcb tcb') := by
    intro tid' tcb' hObj' hNe
    have hNeObj : tid'.toObjId ≠ tid.toObjId :=
      fun h => absurd (threadId_toObjId_injective h) hNe
    have hObjS1 : s1.objects tid'.toObjId = some (.tcb tcb') := by
      rwa [storeTcbIpcState_preserves_objects_ne s1 s2 tid ipc tid'.toObjId hNeObj hTcb] at hObj'
    have hNe2 : tid'.toObjId ≠ epId := by
      intro h; rw [h, storeObject_objects_eq st s1 epId _ hStore] at hObjS1; cases hObjS1
    rwa [storeObject_objects_ne st s1 epId tid'.toObjId _ hNe2 hStore] at hObjS1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid' tcb' hObj' hMem'
    rw [removeRunnable_preserves_objects] at hObj'
    rw [removeRunnable_mem] at hMem'
    rcases hMem' with ⟨hIn, hNe⟩
    rw [hSchedTcb, hSchedStore] at hIn
    exact hReady tid' tcb' (restore tid' tcb' hObj' hNe) hIn
  · -- blockedOnSendNotRunnable
    intro tid' tcb' epId' hObj' hIpc'
    rw [removeRunnable_preserves_objects] at hObj'
    by_cases hEq : tid' = tid
    · subst hEq; exact removeRunnable_not_mem_self s2 tid'
    · intro hMem'; rw [removeRunnable_mem] at hMem'
      rcases hMem' with ⟨hIn, _⟩
      rw [hSchedTcb, hSchedStore] at hIn
      exact absurd hIn (hSend tid' tcb' epId' (restore tid' tcb' hObj' hEq) hIpc')
  · -- blockedOnReceiveNotRunnable
    intro tid' tcb' epId' hObj' hIpc'
    rw [removeRunnable_preserves_objects] at hObj'
    by_cases hEq : tid' = tid
    · subst hEq; exact removeRunnable_not_mem_self s2 tid'
    · intro hMem'; rw [removeRunnable_mem] at hMem'
      rcases hMem' with ⟨hIn, _⟩
      rw [hSchedTcb, hSchedStore] at hIn
      exact absurd hIn (hRecv tid' tcb' epId' (restore tid' tcb' hObj' hEq) hIpc')
  · -- blockedOnReplyNotRunnable
    intro tid' tcb' epId' hObj' hIpc'
    rw [removeRunnable_preserves_objects] at hObj'
    by_cases hEq : tid' = tid
    · subst hEq; exact removeRunnable_not_mem_self s2 tid'
    · intro hMem'; rw [removeRunnable_mem] at hMem'
      rcases hMem' with ⟨hIn, _⟩
      rw [hSchedTcb, hSchedStore] at hIn
      exact absurd hIn (hReply tid' tcb' epId' (restore tid' tcb' hObj' hEq) hIpc')

-- ============================================================================
-- WS-E4/M-12: IPC-scheduler contract predicate preservation for IPC operations
-- ============================================================================

theorem endpointSend_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : MessagePayload)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointSend endpointId sender msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  unfold endpointSend at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hRecv : ep.receiveQueue with
    | receiver :: restRecv =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue, restRecv⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact contractPredicates_through_ensure st s1 s2 endpointId _ receiver
            hInv hStore hTcb
    | [] =>
      simp only [hRecv] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨ep.sendQueue ++ [(sender, msg)], []⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender (.blockedOnSend endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact contractPredicates_through_remove st s1 s2 endpointId _ sender _
            hInv hStore hTcb

theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : Option (SeLe4n.ThreadId × MessagePayload))
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok (result, st')) :
    ipcSchedulerContractPredicates st' := by
  unfold endpointAwaitReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hSend : ep.sendQueue with
    | (sender, sMsg) :: restSend =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨restSend, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact contractPredicates_through_ensure st s1 s2 endpointId _ sender
            hInv hStore hTcb
    | [] =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨[], ep.receiveQueue ++ [receiver]⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 receiver (.blockedOnReceive endpointId) with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = removeRunnable s2 receiver := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact contractPredicates_through_remove st s1 s2 endpointId _ receiver _
            hInv hStore hTcb

theorem endpointReceive_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (result : SeLe4n.ThreadId × MessagePayload)
    (hInv : ipcSchedulerContractPredicates st)
    (hStep : endpointReceive endpointId st = .ok (result, st')) :
    ipcSchedulerContractPredicates st' := by
  unfold endpointReceive at hStep
  match hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some (.tcb _) | some (.notification _) | some (.cnode _) | some (.vspaceRoot _) =>
    simp [hObj] at hStep
  | some (.endpoint ep) =>
    simp only [hObj] at hStep
    match hSend : ep.sendQueue with
    | [] => simp [hSend] at hStep
    | (sender, sMsg) :: rest =>
      simp only [hSend] at hStep
      match hStore : storeObject endpointId (.endpoint ⟨rest, ep.receiveQueue⟩) st with
      | .error e => simp [hStore] at hStep
      | .ok ((), s1) =>
        simp only [hStore] at hStep
        match hTcb : storeTcbIpcState s1 sender .ready with
        | .error e => simp [hTcb] at hStep
        | .ok s2 =>
          simp only [hTcb] at hStep
          have hEq : st' = ensureRunnable s2 sender := by
            have := Except.ok.inj hStep; cases this; rfl
          subst hEq
          exact contractPredicates_through_ensure st s1 s2 endpointId _ sender
            hInv hStore hTcb

end SeLe4n.Kernel
