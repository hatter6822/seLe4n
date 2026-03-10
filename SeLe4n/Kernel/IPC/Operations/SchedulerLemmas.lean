import SeLe4n.Kernel.IPC.Operations.Endpoint

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-E3/H-09: Scheduler lemmas for removeRunnable and ensureRunnable
-- ============================================================================

theorem removeRunnable_scheduler_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).scheduler.current =
      if st.scheduler.current = some tid then none else st.scheduler.current := by
  rfl

theorem removeRunnable_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId) :
    x ∈ (removeRunnable st tid).scheduler.runQueue ↔
    x ∈ st.scheduler.runQueue ∧ x ≠ tid := by
  simp only [removeRunnable]
  exact RunQueue.mem_remove st.scheduler.runQueue tid x

/-- WS-G4: Flat-list version of `removeRunnable_mem` for proof compatibility.
    Works with `.runnable` (= `runQueue.toList`) instead of `.runQueue` (HashSet). -/
theorem removeRunnable_runnable_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId) :
    x ∈ (removeRunnable st tid).scheduler.runnable ↔
    x ∈ st.scheduler.runnable ∧ x ≠ tid := by
  simp only [SchedulerState.runnable, removeRunnable, RunQueue.toList]
  unfold RunQueue.remove
  constructor
  · intro hx
    have ⟨hFlat, hNe⟩ := List.mem_filter.mp hx
    exact ⟨hFlat, by simpa using hNe⟩
  · intro ⟨hFlat, hNe⟩
    exact List.mem_filter.mpr ⟨hFlat, by simpa using hNe⟩

theorem removeRunnable_nodup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNodup : st.scheduler.runnable.Nodup) :
    (removeRunnable st tid).scheduler.runnable.Nodup := by
  simp only [SchedulerState.runnable, removeRunnable, RunQueue.toList]
  unfold RunQueue.remove
  exact hNodup.sublist List.filter_sublist

theorem ensureRunnable_scheduler_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).scheduler.current = st.scheduler.current := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> rfl

theorem ensureRunnable_mem_self
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    tid ∈ (ensureRunnable st tid).scheduler.runQueue := by
  obtain ⟨tcb, hTcb⟩ := hTcb
  unfold ensureRunnable
  split
  · assumption
  · simp only [hTcb]
    rw [RunQueue.mem_insert]
    exact Or.inr rfl

theorem ensureRunnable_mem_old
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runQueue) :
    x ∈ (ensureRunnable st tid).scheduler.runQueue := by
  unfold ensureRunnable
  split
  · exact hMem
  · split
    · rw [RunQueue.mem_insert]; exact Or.inl hMem
    · exact hMem

/-- WS-G4: Flat-list version of `ensureRunnable_mem_old` for proof compatibility.
    Works with `.runnable` (= `runQueue.toList`) instead of `.runQueue` (HashSet). -/
theorem ensureRunnable_runnable_mem_old
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runnable) :
    x ∈ (ensureRunnable st tid).scheduler.runnable := by
  unfold ensureRunnable
  split
  · exact hMem
  · rename_i hNotMem
    split
    · rename_i tcb hTcb
      show x ∈ (st.scheduler.runQueue.insert tid tcb.priority).toList
      rw [RunQueue.toList_insert_not_mem _ _ _ hNotMem]
      exact List.mem_append_left _ hMem
    · exact hMem

theorem ensureRunnable_nodup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNodup : st.scheduler.runnable.Nodup) :
    (ensureRunnable st tid).scheduler.runnable.Nodup := by
  unfold ensureRunnable
  split
  · exact hNodup
  · rename_i hNotMem
    split
    · rename_i tcb hTcb
      show (st.scheduler.runQueue.insert tid tcb.priority).toList.Nodup
      rw [RunQueue.toList_insert_not_mem _ _ _ hNotMem]
      have hNotFlat : tid ∉ st.scheduler.runnable :=
        RunQueue.not_mem_toList_of_not_mem _ _ hNotMem
      refine List.nodup_append.2 ⟨hNodup, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      have : y = tid := by simpa using hy
      subst this; intro hEq; subst hEq
      exact hNotFlat hx
    · exact hNodup

/-- Alias referencing the canonical `ThreadId.toObjId_injective` in Prelude. -/
theorem threadId_toObjId_injective {a b : SeLe4n.ThreadId}
    (h : a.toObjId = b.toObjId) : a = b :=
  SeLe4n.ThreadId.toObjId_injective a b h

/-- WS-E3/H-09: If `storeTcbIpcState st tid ipc` succeeds and the post-state has a TCB
    at `tid.toObjId`, then that TCB has `ipcState = ipc`. Covers both the case where
    lookupTcb found an existing TCB (which was updated) and the no-op case (which leads
    to contradiction since lookupTcb failing means no TCB at tid). -/
theorem storeTcbIpcState_ipcState_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (tcb : TCB) (hTcb : st'.objects[tid.toObjId]? = some (.tcb tcb)) :
    tcb.ipcState = ipc := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    simp [hLookup] at hStep
  | some tcb' =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb' with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hAt := storeObject_objects_eq st pair.2 tid.toObjId _ hStore
      rw [hAt] at hTcb; cases hTcb; rfl

/-- WS-E3/H-09: Reverse membership for ensureRunnable. If a thread is in the runnable
    queue after ensureRunnable, it was either already there or it is the added thread. -/
theorem ensureRunnable_mem_reverse
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ (ensureRunnable st tid).scheduler.runnable) :
    x ∈ st.scheduler.runnable ∨ x = tid := by
  unfold ensureRunnable at hMem
  split at hMem
  · exact .inl hMem
  · rename_i hNotMem
    split at hMem
    · -- TCB case: runnable = (rq.insert tid prio).toList
      simp only [SchedulerState.runnable, RunQueue.toList] at hMem ⊢
      unfold RunQueue.insert at hMem
      split at hMem
      · exact .inl hMem
      · simp only [List.mem_append, List.mem_singleton] at hMem
        exact hMem.elim .inl .inr
    · exact .inl hMem

/-- WS-E3/H-09: A thread is never in its own removeRunnable result. -/
theorem removeRunnable_not_mem_self
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∉ (removeRunnable st tid).scheduler.runnable := by
  simp only [SchedulerState.runnable, removeRunnable]
  exact RunQueue.not_mem_remove_toList st.scheduler.runQueue tid

/-- WS-H12b: If a thread is not in the runnable queue, it remains absent after
    `ensureRunnable` on a *different* thread. Contrapositive of `ensureRunnable_mem_reverse`. -/
theorem ensureRunnable_not_mem_of_not_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hNotMem : x ∉ st.scheduler.runnable) (hNe : x ≠ tid) :
    x ∉ (ensureRunnable st tid).scheduler.runnable := by
  intro hContra
  rcases ensureRunnable_mem_reverse st tid x hContra with hOld | hEq
  · exact hNotMem hOld
  · exact hNe hEq

/-- WS-H12b: If a thread is not in the runnable queue, it remains absent after
    `removeRunnable` (which only removes threads). -/
theorem removeRunnable_not_mem_of_not_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hNotMem : x ∉ st.scheduler.runnable) :
    x ∉ (removeRunnable st tid).scheduler.runnable := by
  intro hContra
  exact hNotMem ((removeRunnable_runnable_mem st tid x).mp hContra).1

/-- WS-E3/H-09: If a TCB exists at `tid.toObjId` in the pre-state, then a TCB still
    exists there after `storeTcbIpcState` (though the ipcState may have changed). -/
theorem storeTcbIpcState_tcb_exists_at_target
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (_hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact ⟨{ tcb with ipcState := ipc }, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

-- ============================================================================
-- WS-F1: Supporting lemmas for storeTcbIpcStateAndMessage / storeTcbPendingMessage
-- ============================================================================

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbIpcStateAndMessage_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hStore

/-- WS-F1: `storeTcbIpcStateAndMessage` does not modify the scheduler. -/
theorem storeTcbIpcStateAndMessage_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves endpoint objects. -/
theorem storeTcbIpcStateAndMessage_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (epId : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg epId hEq hStep]; exact hEp

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves notification objects. -/
theorem storeTcbIpcStateAndMessage_preserves_notification
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (notifId : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[notifId]? = some (.notification ntfn) := by
  by_cases hEq : notifId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hNtfn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg notifId hEq hStep]; exact hNtfn

/-- WS-F1: Backward endpoint preservation for `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hEp; cases hEp
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg oid hEq hStep] at hEp; exact hEp

/-- WS-F1: Backward notification preservation for `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hNtfn; cases hNtfn
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg oid hEq hStep] at hNtfn; exact hNtfn

/-- WS-F1: IPC state read-back for `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_ipcState_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (tcb : TCB) (hTcb : st'.objects[tid.toObjId]? = some (.tcb tcb)) :
    tcb.ipcState = ipc := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb' =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb' with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hAt := storeObject_objects_eq st pair.2 tid.toObjId _ hStore
      rw [hAt] at hTcb; cases hTcb; rfl

/-- WS-F1: TCB existence at target after `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_tcb_exists_at_target
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (_hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact ⟨_, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

/-- WS-F1: `storeTcbPendingMessage` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbPendingMessage_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage) (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeTcbPendingMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hStore

/-- WS-F1: `storeTcbPendingMessage` does not modify the scheduler. -/
theorem storeTcbPendingMessage_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbPendingMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-F1: `storeTcbPendingMessage` preserves endpoint objects. -/
theorem storeTcbPendingMessage_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage) (epId : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg epId hEq hStep]; exact hEp

/-- WS-F1: Backward endpoint preservation for `storeTcbPendingMessage`. -/
theorem storeTcbPendingMessage_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hEp; cases hEp
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg oid hEq hStep] at hEp; exact hEp

/-- WS-F1: Backward notification preservation for `storeTcbPendingMessage`. -/
theorem storeTcbPendingMessage_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hNtfn; cases hNtfn
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg oid hEq hStep] at hNtfn; exact hNtfn

/-- WS-F1: storeTcbPendingMessage forward-preserves TCB existence. -/
theorem storeTcbPendingMessage_tcb_forward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hTcb : st.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some origTcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { origTcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
        exact ⟨_, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩
  · exact ⟨tcb, by rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg oid hEq hStep]; exact hTcb⟩

/-- WS-F1: storeTcbPendingMessage backward-preserves TCB ipcStates. -/
theorem storeTcbPendingMessage_tcb_ipcState_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  by_cases hEq : anyTid.toObjId = tid.toObjId
  · unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some origTcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { origTcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
        rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hTcb'
        simp at hTcb'; subst hTcb'
        exact ⟨origTcb, hEq ▸ lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg anyTid.toObjId hEq hStep] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩


end SeLe4n.Kernel
