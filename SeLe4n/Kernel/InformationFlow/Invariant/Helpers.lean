import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Enforcement
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Service.Invariant
import SeLe4n.Kernel.Architecture.VSpace

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-F3: storeObject objectIndex filter preservation
-- ============================================================================

/-- WS-F3: storeObject at a non-observable ID preserves the projected object index.
If the target is non-observable, its addition to the raw index is filtered out. -/
private theorem storeObject_preserves_projectObjectIndex
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectObjectIndex ctx observer st' = projectObjectIndex ctx observer st := by
  unfold storeObject at hStore; cases hStore
  simp only [projectObjectIndex]
  split
  · rfl
  · rw [List.filter_cons]; simp [hOidHigh]

/-- WS-F3: cspaceInsertSlot at a non-observable CNode preserves the projected object index.
Follows from storeObject + storeCapabilityRef frame lemmas. -/
theorem cspaceInsertSlot_preserves_projectObjectIndex
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hOidHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    projectObjectIndex ctx observer st' = projectObjectIndex ctx observer st := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hMid := storeObject_preserves_projectObjectIndex ctx observer st stMid
                    addr.cnode _ hOidHigh hStore
                  have hRef := storeCapabilityRef_preserves_objectIndex stMid st' addr (some cap.target) hStep
                  rw [show projectObjectIndex ctx observer st' = stMid.objectIndex.filter (objectObservable ctx observer) from by
                    simp [projectObjectIndex, hRef]]
                  exact hMid

-- ============================================================================
-- Shared non-interference proof infrastructure
-- ============================================================================

/-- A generic storeObject at a non-observable id preserves low-equivalence.
This is the shared proof skeleton used by multiple non-interference theorems. -/
theorem storeObject_at_unobservable_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (targetId : SeLe4n.ObjId)
    (obj₁ obj₂ : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hStore₁ : storeObject targetId obj₁ s₁ = .ok ((), s₁'))
    (hStore₂ : storeObject targetId obj₂ s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ :=
    congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ :=
    congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ :=
    congrArg ObservableState.current hLow
  have hSvcLow : projectServiceStatus ctx observer s₁ = projectServiceStatus ctx observer s₂ :=
    congrArg ObservableState.services hLow
  have hDomLow : projectActiveDomain ctx observer s₁ = projectActiveDomain ctx observer s₂ :=
    congrArg ObservableState.activeDomain hLow
  have hIrqLow : projectIrqHandlers ctx observer s₁ = projectIrqHandlers ctx observer s₂ :=
    congrArg ObservableState.irqHandlers hLow
  have hIdxLow : projectObjectIndex ctx observer s₁ = projectObjectIndex ctx observer s₂ :=
    congrArg ObservableState.objectIndex hLow
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = targetId
      · subst hEq; simp [hTargetHigh] at hObs
      · have hObj₁ : s₁'.objects[oid]? = s₁.objects[oid]? :=
          storeObject_objects_ne s₁ s₁' targetId oid obj₁ hEq hStore₁
        have hObj₂ : s₂'.objects[oid]? = s₂.objects[oid]? :=
          storeObject_objects_ne s₂ s₂' targetId oid obj₂ hEq hStore₂
        have hObjBase : (s₁.objects[oid]?).map (projectKernelObject ctx observer) =
            (s₂.objects[oid]?).map (projectKernelObject ctx observer) := by
          have hBase := congrFun hObjLow oid
          simp only [projectObjects, hObs, ite_true] at hBase
          exact hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    unfold storeObject at hStore₁ hStore₂
    cases hStore₁; cases hStore₂
    simpa [projectServiceStatus] using hSvcLow
  have hDom' : projectActiveDomain ctx observer s₁' = projectActiveDomain ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectActiveDomain, hSched₁, hSched₂] using hDomLow
  have hIrq' : projectIrqHandlers ctx observer s₁' = projectIrqHandlers ctx observer s₂' := by
    have hIH₁ := storeObject_irqHandlers_eq s₁ s₁' targetId obj₁ hStore₁
    have hIH₂ := storeObject_irqHandlers_eq s₂ s₂' targetId obj₂ hStore₂
    funext irq; simp only [projectIrqHandlers, hIH₁, hIH₂]
    exact congrFun hIrqLow irq
  have hIdx' : projectObjectIndex ctx observer s₁' = projectObjectIndex ctx observer s₂' := by
    rw [storeObject_preserves_projectObjectIndex ctx observer s₁ s₁' targetId obj₁ hTargetHigh hStore₁,
        storeObject_preserves_projectObjectIndex ctx observer s₂ s₂' targetId obj₂ hTargetHigh hStore₂]
    exact hIdxLow
  have hDTR : projectDomainTimeRemaining ctx observer s₁' = projectDomainTimeRemaining ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectDomainTimeRemaining, hSched₁, hSched₂]
    exact congrArg ObservableState.domainTimeRemaining hLow
  have hDS : projectDomainSchedule ctx observer s₁' = projectDomainSchedule ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectDomainSchedule, hSched₁, hSched₂]
    exact congrArg ObservableState.domainSchedule hLow
  have hDSI : projectDomainScheduleIndex ctx observer s₁' = projectDomainScheduleIndex ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectDomainScheduleIndex, hSched₁, hSched₂]
    exact congrArg ObservableState.domainScheduleIndex hLow
  have hMR : projectMachineRegs ctx observer s₁' = projectMachineRegs ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    have hM₁ := storeObject_machine_eq s₁ s₁' targetId obj₁ hStore₁
    have hM₂ := storeObject_machine_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectMachineRegs, hSched₁, hSched₂, hM₁, hM₂]
    exact congrArg ObservableState.machineRegs hLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc', hDom', hIrq', hIdx', hDTR, hDS, hDSI, hMR]

-- ============================================================================
-- WS-E5: clearCapabilityRefsState preserves projection (used by composed proofs)
-- ============================================================================

/-- clearCapabilityRefsState preserves the observer projection for any refs list. -/
theorem clearCapabilityRefsState_preserves_projectState
    (ctx : LabelingContext) (observer : IfObserver)
    (refs : List SlotRef) (st : SystemState) :
    projectState ctx observer (clearCapabilityRefsState refs st) =
      projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext oid; simp [projectObjects, clearCapabilityRefsState_preserves_objects]
  · simp [projectRunnable, clearCapabilityRefsState_preserves_scheduler]
  · simp [projectCurrent, clearCapabilityRefsState_preserves_scheduler]
  · funext sid; simp [projectServiceStatus, clearCapabilityRefsState_lookupService]
  · simp [projectActiveDomain, clearCapabilityRefsState_preserves_scheduler]
  · funext irq; simp [projectIrqHandlers, clearCapabilityRefsState_preserves_irqHandlers]
  · simp [projectObjectIndex, clearCapabilityRefsState_preserves_objectIndex]
  · simp [projectDomainTimeRemaining, clearCapabilityRefsState_preserves_scheduler]
  · simp [projectDomainSchedule, clearCapabilityRefsState_preserves_scheduler]
  · simp [projectDomainScheduleIndex, clearCapabilityRefsState_preserves_scheduler]
  · simp [projectMachineRegs, clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_machine]

-- ============================================================================
-- WS-E3/H-09: Multi-step operation helpers for non-interference
-- ============================================================================

/-- List filter commutation: filtering by (· ≠ a) then by p equals just filtering by p
when p a = false. Used for removeRunnable projection preservation. -/
private theorem list_filter_ne_then_filter_eq
    {α : Type} [DecidableEq α] (xs : List α) (a : α) (p : α → Bool)
    (hPa : p a = false) :
    (xs.filter (· ≠ a)).filter p = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter]
    by_cases hxeq : x = a
    · -- x = a: the (· ≠ a) filter drops x; p a = false drops it from RHS too
      subst hxeq
      simp only [ne_eq, not_true, decide_false, hPa]
      exact ih
    · -- x ≠ a: the (· ≠ a) filter keeps x
      have hNeTrue : decide (x ≠ a) = true := decide_eq_true_eq.mpr hxeq
      rw [hNeTrue]; simp only [List.filter]
      cases hpx : p x
      · exact ih
      · simp only [List.cons.injEq, true_and]; exact ih

/-- List filter absorption: filtering by p on (xs ++ [a]) equals filtering by p on xs
when p a = false. Used for ensureRunnable projection preservation. -/
private theorem list_filter_append_singleton_unobs
    {α : Type} [DecidableEq α] (xs : List α) (a : α) (p : α → Bool)
    (hPa : p a = false) :
    (xs ++ [a]).filter p = xs.filter p := by
  rw [List.filter_append]
  simp [List.filter, hPa]

/-- Removing a non-observable thread preserves low-equivalence projection. -/
theorem removeRunnable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (removeRunnable st tid) = projectState ctx observer st := by
  have hRun : projectRunnable ctx observer (removeRunnable st tid) = projectRunnable ctx observer st := by
    simp only [projectRunnable, removeRunnable]
    exact list_filter_ne_then_filter_eq st.scheduler.runnable tid (threadObservable ctx observer) hTidHigh
  have hCur : projectCurrent ctx observer (removeRunnable st tid) = projectCurrent ctx observer st := by
    simp only [projectCurrent, removeRunnable]
    cases hC : st.scheduler.current with
    | none => simp
    | some x =>
      by_cases hEq : some x = some tid
      · rw [if_pos hEq]; cases (Option.some.inj hEq); simp [hTidHigh]
      · rw [if_neg hEq]
  have hObj : projectObjects ctx observer (removeRunnable st tid) = projectObjects ctx observer st := rfl
  have hSvc : projectServiceStatus ctx observer (removeRunnable st tid) =
      projectServiceStatus ctx observer st := funext fun _ => rfl
  have hDom : projectActiveDomain ctx observer (removeRunnable st tid) =
      projectActiveDomain ctx observer st := rfl
  have hIrq : projectIrqHandlers ctx observer (removeRunnable st tid) =
      projectIrqHandlers ctx observer st := rfl
  have hIdx : projectObjectIndex ctx observer (removeRunnable st tid) =
      projectObjectIndex ctx observer st := rfl
  have hDTR : projectDomainTimeRemaining ctx observer (removeRunnable st tid) =
      projectDomainTimeRemaining ctx observer st := rfl
  have hDS : projectDomainSchedule ctx observer (removeRunnable st tid) =
      projectDomainSchedule ctx observer st := rfl
  have hDSI : projectDomainScheduleIndex ctx observer (removeRunnable st tid) =
      projectDomainScheduleIndex ctx observer st := rfl
  have hMR : projectMachineRegs ctx observer (removeRunnable st tid) =
      projectMachineRegs ctx observer st := by
    simp only [projectMachineRegs, removeRunnable]
    cases hC : st.scheduler.current with
    | none => simp
    | some x =>
      by_cases hEq : some x = some tid
      · rw [if_pos hEq]; cases (Option.some.inj hEq); simp [hTidHigh]
      · rw [if_neg hEq]
  simp only [projectState, hObj, hRun, hCur, hSvc, hDom, hIrq, hIdx, hDTR, hDS, hDSI, hMR]

/-- Adding a non-observable thread to runnable preserves low-equivalence projection. -/
theorem ensureRunnable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (ensureRunnable st tid) = projectState ctx observer st := by
  unfold ensureRunnable
  split
  · rfl
  · rename_i hNotMem
    cases hObjTcb : st.objects[tid.toObjId]? with
    | none => rfl
    | some obj =>
      cases obj with
      | endpoint ep => rfl
      | notification ntfn => rfl
      | cnode cn => rfl
      | vspaceRoot root => rfl
      | untyped _ => rfl
      | tcb tcb =>
          show projectState ctx observer
              { st with scheduler := { st.scheduler with
                  runQueue := st.scheduler.runQueue.insert tid tcb.priority } } =
              projectState ctx observer st
          simp only [projectState]; congr 1
          · -- projectRunnable
            simp only [projectRunnable, SchedulerState.runnable]
            exact RunQueue.toList_filter_insert_neg _ _ _ _ hTidHigh hNotMem

/-- storeTcbIpcState at a non-observable object preserves projection (single-state). -/
private theorem storeTcbIpcState_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
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
      simp only [projectState]; congr 1
      · -- projectObjects: storeObject at non-observable tid.toObjId
        funext oid
        by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hStore)
        · simp [projectObjects, hObs]
      · -- projectRunnable: scheduler preserved by storeObject
        simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- projectCurrent: scheduler preserved by storeObject
        simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- projectServiceStatus: services unchanged
        unfold storeObject at hStore; cases hStore; funext sid; rfl
      · -- activeDomain: scheduler preserved by storeObject
        simp [projectActiveDomain, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- irqHandlers: preserved by storeObject
        funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st pair.2 tid.toObjId _ hStore]
      · -- objectIndex: non-observable target
        exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore
      · -- WS-H8: domainTimeRemaining
        simp [projectDomainTimeRemaining, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- WS-H8: domainSchedule
        simp [projectDomainSchedule, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- WS-H8: domainScheduleIndex
        simp [projectDomainScheduleIndex, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- WS-H10: machineRegs
        simp [projectMachineRegs, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore,
              storeObject_machine_eq st pair.2 tid.toObjId _ hStore]

/-- WS-H9: storeTcbPendingMessage at a non-observable object preserves projection. -/
private theorem storeTcbPendingMessage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hStore)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · unfold storeObject at hStore; cases hStore; funext sid; rfl
      · simp [projectActiveDomain, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st pair.2 tid.toObjId _ hStore]
      · exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore
      · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainSchedule, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectMachineRegs, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore,
              storeObject_machine_eq st pair.2 tid.toObjId _ hStore]

/-- WS-H9: storeTcbIpcStateAndMessage at a non-observable object preserves projection. -/
theorem storeTcbIpcStateAndMessage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hStore)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · unfold storeObject at hStore; cases hStore; funext sid; rfl
      · simp [projectActiveDomain, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st pair.2 tid.toObjId _ hStore]
      · exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore
      · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainSchedule, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectMachineRegs, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore,
              storeObject_machine_eq st pair.2 tid.toObjId _ hStore]

/-- storeObject at a non-observable object preserves projection (single-state). -/
theorem storeObject_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext o
    by_cases hObs : objectObservable ctx observer o
    · simp [projectObjects, hObs]
      by_cases hEq : o = oid
      · subst hEq; simp [hOidHigh] at hObs
      · exact congrArg (Option.map (projectKernelObject ctx observer))
          (storeObject_objects_ne st st' oid o obj hEq hStore)
    · simp [projectObjects, hObs]
  · simp [projectRunnable, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectCurrent, storeObject_scheduler_eq st st' oid obj hStore]
  · unfold storeObject at hStore; cases hStore; funext sid; rfl
  · simp [projectActiveDomain, storeObject_scheduler_eq st st' oid obj hStore]
  · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st st' oid obj hStore]
  · exact storeObject_preserves_projectObjectIndex ctx observer st st' oid obj hOidHigh hStore
  · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectDomainSchedule, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectMachineRegs, storeObject_scheduler_eq st st' oid obj hStore,
          storeObject_machine_eq st st' oid obj hStore]

-- ============================================================================
-- Non-interference theorem #1: chooseThread (WS-D2, F-05, TPI-D01)
-- ============================================================================

/-- Choosing the next thread does not leak high-domain scheduling decisions. -/
theorem chooseThread_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (next₁ next₂ : Option SeLe4n.ThreadId)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : chooseThread s₁ = .ok (next₁, s₁'))
    (hStep₂ : chooseThread s₂ = .ok (next₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hEq₁ : s₁' = s₁ := chooseThread_preserves_state s₁ s₁' next₁ hStep₁
  have hEq₂ : s₂' = s₂ := chooseThread_preserves_state s₂ s₂' next₂ hStep₂
  subst hEq₁; subst hEq₂
  exact hLow

-- ============================================================================
-- Non-interference theorem #3: cspaceMint (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- Minting a capability in a non-observable CNode preserves low-equivalence. -/
theorem cspaceMint_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (_hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceMint src dst rights badge s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMint src dst rights badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases cspaceMint_child_attenuates s₁ s₁' src dst rights badge hStep₁ with
    ⟨parent₁, child₁, hLookup₁, _, _⟩
  rcases cspaceMint_child_attenuates s₂ s₂' src dst rights badge hStep₂ with
    ⟨parent₂, child₂, hLookup₂, _, _⟩
  unfold cspaceMint at hStep₁ hStep₂
  rw [hLookup₁] at hStep₁; rw [hLookup₂] at hStep₂
  cases hMint₁ : mintDerivedCap parent₁ rights badge with
  | error e => simp [hMint₁] at hStep₁
  | ok c₁ =>
    cases hMint₂ : mintDerivedCap parent₂ rights badge with
    | error e => simp [hMint₂] at hStep₂
    | ok c₂ =>
      have hInsert₁ : cspaceInsertSlot dst c₁ s₁ = .ok ((), s₁') := by simpa [hMint₁] using hStep₁
      have hInsert₂ : cspaceInsertSlot dst c₂ s₂ = .ok ((), s₂') := by simpa [hMint₂] using hStep₂
      have hObjLow := congrArg ObservableState.objects hLow
      have hRunLow := congrArg ObservableState.runnable hLow
      have hCurLow := congrArg ObservableState.current hLow
      have hSched₁ := cspaceInsertSlot_preserves_scheduler s₁ s₁' dst c₁ hInsert₁
      have hSched₂ := cspaceInsertSlot_preserves_scheduler s₂ s₂' dst c₂ hInsert₂
      have hSvc₁ := cspaceInsertSlot_preserves_services s₁ s₁' dst c₁ hInsert₁
      have hSvc₂ := cspaceInsertSlot_preserves_services s₂ s₂' dst c₂ hInsert₂
      unfold lowEquivalent projectState
      congr 1
      · funext oid
        by_cases hObs : objectObservable ctx observer oid
        · have hNeDst : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
          have hObj₁ := cspaceInsertSlot_preserves_objects_ne s₁ s₁' dst c₁ oid hNeDst hInsert₁
          have hObj₂ := cspaceInsertSlot_preserves_objects_ne s₂ s₂' dst c₂ oid hNeDst hInsert₂
          simp only [projectObjects, hObs, ite_true]
          rw [hObj₁, hObj₂]
          have hBase := congrFun hObjLow oid
          simp only [projectState, projectObjects, hObs, ite_true] at hBase
          exact hBase
        · simp [projectObjects, hObs]
      · simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
      · simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
      · funext sid
        simp only [projectServiceStatus, lookupService]
        rw [show s₁'.services = s₁.services from hSvc₁, show s₂'.services = s₂.services from hSvc₂]
        have hBase := congrArg ObservableState.services hLow
        exact congrFun hBase sid
      · -- activeDomain
        simpa [projectActiveDomain, hSched₁, hSched₂] using congrArg ObservableState.activeDomain hLow
      · -- irqHandlers
        funext irq
        simp only [projectIrqHandlers]
        rw [cspaceInsertSlot_preserves_irqHandlers s₁ s₁' dst c₁ hInsert₁,
            cspaceInsertSlot_preserves_irqHandlers s₂ s₂' dst c₂ hInsert₂]
        exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
      · -- objectIndex
        rw [cspaceInsertSlot_preserves_projectObjectIndex s₁ s₁' dst c₁ hDstHigh hInsert₁,
            cspaceInsertSlot_preserves_projectObjectIndex s₂ s₂' dst c₂ hDstHigh hInsert₂]
        exact congrArg ObservableState.objectIndex hLow
      · -- domainTimeRemaining
        simpa [projectDomainTimeRemaining, hSched₁, hSched₂] using congrArg ObservableState.domainTimeRemaining hLow
      · -- domainSchedule
        simpa [projectDomainSchedule, hSched₁, hSched₂] using congrArg ObservableState.domainSchedule hLow
      · -- domainScheduleIndex
        simpa [projectDomainScheduleIndex, hSched₁, hSched₂] using congrArg ObservableState.domainScheduleIndex hLow
      · -- machineRegs
        simp [projectMachineRegs, hSched₁, hSched₂,
          cspaceInsertSlot_preserves_machine s₁ s₁' dst c₁ hInsert₁,
          cspaceInsertSlot_preserves_machine s₂ s₂' dst c₂ hInsert₂]
        exact congrArg ObservableState.machineRegs hLow

-- ============================================================================
-- Non-interference theorem #4: cspaceRevoke (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- Revoking capabilities in a non-observable CNode preserves low-equivalence. -/
theorem cspaceRevoke_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (addr : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCNodeHigh : objectObservable ctx observer addr.cnode = false)
    (hStep₁ : cspaceRevoke addr s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceRevoke addr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hObjLow := congrArg ObservableState.objects hLow
  have hRunLow := congrArg ObservableState.runnable hLow
  have hCurLow := congrArg ObservableState.current hLow
  have hSvcLow := congrArg ObservableState.services hLow
  unfold cspaceRevoke at hStep₁ hStep₂
  cases hL₁ : cspaceLookupSlot addr s₁ with
  | error e => simp [hL₁] at hStep₁
  | ok p₁ =>
    rcases p₁ with ⟨par₁, stL₁⟩
    have hEq₁ : stL₁ = s₁ := cspaceLookupSlot_preserves_state s₁ stL₁ addr par₁ hL₁
    subst stL₁
    cases hL₂ : cspaceLookupSlot addr s₂ with
    | error e => simp [hL₂] at hStep₂
    | ok p₂ =>
      rcases p₂ with ⟨par₂, stL₂⟩
      have hEq₂ : stL₂ = s₂ := cspaceLookupSlot_preserves_state s₂ stL₂ addr par₂ hL₂
      subst stL₂
      cases hC₁ : s₁.objects[addr.cnode]? with
      | none => simp [hL₁, hC₁] at hStep₁
      | some o₁ =>
        cases o₁ with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL₁, hC₁] at hStep₁
        | cnode cn₁ =>
          cases hC₂ : s₂.objects[addr.cnode]? with
          | none => simp [hL₂, hC₂] at hStep₂
          | some o₂ =>
            cases o₂ with
            | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL₂, hC₂] at hStep₂
            | cnode cn₂ =>
              simp [hL₁, hC₁, storeObject] at hStep₁
              simp [hL₂, hC₂, storeObject] at hStep₂
              cases hStep₁; cases hStep₂
              unfold lowEquivalent projectState
              congr 1
              · funext oid
                by_cases hObs : objectObservable ctx observer oid
                · have hNe : oid ≠ addr.cnode := by
                    intro hEq; subst hEq; simp [hCNodeHigh] at hObs
                  have hBase : projectObjects ctx observer s₁ oid = projectObjects ctx observer s₂ oid :=
                    congrFun hObjLow oid
                  simp [projectObjects, hObs] at hBase ⊢
                  rw [clearCapabilityRefsState_preserves_objects, clearCapabilityRefsState_preserves_objects]
                  simp [HashMap_getElem?_insert, Ne.symm hNe]
                  exact hBase
                · simp [projectObjects, hObs]
              · simp only [projectRunnable]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                simpa [projectRunnable] using hRunLow
              · simp only [projectCurrent]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                simpa [projectCurrent] using hCurLow
              · funext sid
                simp only [projectServiceStatus, clearCapabilityRefsState_lookupService]
                have hBase := congrArg ObservableState.services hLow
                have hSidBase := congrFun hBase sid
                simpa [projectServiceStatus] using hSidBase
              · -- activeDomain
                simp only [projectActiveDomain]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                exact congrArg ObservableState.activeDomain hLow
              · -- irqHandlers
                funext irq
                simp only [projectIrqHandlers]
                rw [clearCapabilityRefsState_preserves_irqHandlers, clearCapabilityRefsState_preserves_irqHandlers]
                exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
              · -- objectIndex
                simp only [projectObjectIndex]
                rw [clearCapabilityRefsState_preserves_objectIndex, clearCapabilityRefsState_preserves_objectIndex]
                have hIdx := congrArg ObservableState.objectIndex hLow
                -- Both sides: if objectIndexSet.contains addr.cnode then idx else addr.cnode :: idx
                -- Since hCNodeHigh filters addr.cnode out, prepending it is invisible
                split <;> split
                · exact hIdx
                · rw [List.filter_cons]; simp [hCNodeHigh]; exact hIdx
                · rw [List.filter_cons]; simp [hCNodeHigh]; exact hIdx
                · rw [List.filter_cons, List.filter_cons]; simp [hCNodeHigh]; exact hIdx
              · -- domainTimeRemaining
                simp only [projectDomainTimeRemaining]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                exact congrArg ObservableState.domainTimeRemaining hLow
              · -- domainSchedule
                simp only [projectDomainSchedule]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                exact congrArg ObservableState.domainSchedule hLow
              · -- domainScheduleIndex
                simp only [projectDomainScheduleIndex]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                exact congrArg ObservableState.domainScheduleIndex hLow
              · -- machineRegs
                simp only [projectMachineRegs]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler,
                    clearCapabilityRefsState_preserves_machine, clearCapabilityRefsState_preserves_machine]
                exact congrArg ObservableState.machineRegs hLow

-- ============================================================================
-- Non-interference theorem #5: lifecycleRetypeObject (WS-D2, F-05, TPI-D03)
-- ============================================================================

/-- Retyping a non-observable object preserves low-equivalence. -/
theorem lifecycleRetypeObject_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hStep₁ : lifecycleRetypeObject authority target newObj s₁ = .ok ((), s₁'))
    (hStep₂ : lifecycleRetypeObject authority target newObj s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases lifecycleRetypeObject_ok_as_storeObject s₁ s₁' authority target newObj hStep₁ with
    ⟨_, _, _, _, _, _, hStore₁⟩
  rcases lifecycleRetypeObject_ok_as_storeObject s₂ s₂' authority target newObj hStep₂ with
    ⟨_, _, _, _, _, _, hStore₂⟩
  exact storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer target newObj newObj s₁ s₂ s₁' s₂' hLow hTargetHigh hStore₁ hStore₂

-- ============================================================================
-- WS-F3/F-21: notificationSignal non-interference
-- ============================================================================

/-- WS-F3/F-21: notificationSignal at non-observable entities preserves projection. -/
theorem notificationSignal_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (st st' : SystemState)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hWaiterDomain : ∀ ntfn tid, st.objects[notificationId]? = some (.notification ntfn) →
        tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | nil =>
        -- No waiters: just storeObject on notification
        simp [hWaiters] at hStep
        exact storeObject_preserves_projection ctx observer st st' notificationId _ hNtfnHigh hStep
      | cons waiter rest =>
        simp [hWaiters] at hStep
        -- Waiter path: storeObject + storeTcbIpcState + ensureRunnable
        have hWaiterHigh := hWaiterDomain ntfn waiter hObj (hWaiters ▸ List.Mem.head rest)
        have hWaiterObjHigh := hCoherent waiter hWaiterHigh
        revert hStep
        cases hStore : storeObject notificationId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            rw [ensureRunnable_preserves_projection ctx observer st2 waiter hWaiterHigh,
                storeTcbIpcState_preserves_projection ctx observer pair.2 st2 waiter _ hWaiterObjHigh hTcb,
                storeObject_preserves_projection ctx observer st pair.2 notificationId _ hNtfnHigh hStore]

/-- WS-F3/F-21: notificationSignal preserves low-equivalence. -/
theorem notificationSignal_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hWaiterDomain₁ : ∀ ntfn tid, s₁.objects[notificationId]? = some (.notification ntfn) →
        tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
    (hWaiterDomain₂ : ∀ ntfn tid, s₂.objects[notificationId]? = some (.notification ntfn) →
        tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
    (hStep₁ : notificationSignal notificationId badge s₁ = .ok ((), s₁'))
    (hStep₂ : notificationSignal notificationId badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact notificationSignal_projection_preserved ctx observer notificationId badge s₂ s₂'
      hNtfnHigh hCoherent hWaiterDomain₂ hStep₂
  exact notificationSignal_projection_preserved ctx observer notificationId badge s₁ s₁'
    hNtfnHigh hCoherent hWaiterDomain₁ hStep₁

-- ============================================================================
-- WS-F3/F-21: notificationWait non-interference
-- ============================================================================

/-- WS-F3/F-21: notificationWait at non-observable entities preserves projection. -/
theorem notificationWait_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (st st' : SystemState)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Consume pending badge: storeObject + storeTcbIpcState
        simp [hBadge] at hStep; revert hStep
        cases hStore : storeObject notificationId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            rw [storeTcbIpcState_preserves_projection ctx observer pair.2 st2 waiter _ hWaiterObjHigh hTcb,
                storeObject_preserves_projection ctx observer st pair.2 notificationId _ hNtfnHigh hStore]
      | none =>
        -- WS-G7: Block path: lookupTcb → ipcState check → storeObject + storeTcbIpcState + removeRunnable
        simp [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          by_cases hBlocked : tcb.ipcState = .blockedOnNotification notificationId
          · simp [hBlocked] at hStep
          · simp [hBlocked] at hStep; revert hStep
            cases hStore : storeObject notificationId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hTcb : storeTcbIpcState pair.2 waiter _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                rw [removeRunnable_preserves_projection ctx observer st2 waiter hWaiterHigh,
                    storeTcbIpcState_preserves_projection ctx observer pair.2 st2 waiter _ hWaiterObjHigh hTcb,
                    storeObject_preserves_projection ctx observer st pair.2 notificationId _ hNtfnHigh hStore]

/-- WS-F3/F-21: notificationWait preserves low-equivalence. -/
theorem notificationWait_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result₁ result₂ : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
    (hStep₁ : notificationWait notificationId waiter s₁ = .ok (result₁, s₁'))
    (hStep₂ : notificationWait notificationId waiter s₂ = .ok (result₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact notificationWait_projection_preserved ctx observer notificationId waiter result₂ s₂ s₂'
      hNtfnHigh hWaiterHigh hWaiterObjHigh hStep₂
  exact notificationWait_projection_preserved ctx observer notificationId waiter result₁ s₁ s₁'
    hNtfnHigh hWaiterHigh hWaiterObjHigh hStep₁

-- ============================================================================
-- WS-F3/CRIT-03: Additional NI theorems for API coverage
-- ============================================================================

/-- WS-F3: cspaceInsertSlot at a non-observable CNode preserves low-equivalence. -/
theorem cspaceInsertSlot_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (dst : CSpaceAddr) (cap : Capability)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceInsertSlot dst cap s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceInsertSlot dst cap s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hSched₁ := cspaceInsertSlot_preserves_scheduler s₁ s₁' dst cap hStep₁
  have hSched₂ := cspaceInsertSlot_preserves_scheduler s₂ s₂' dst cap hStep₂
  have hSvc₁ := cspaceInsertSlot_preserves_services s₁ s₁' dst cap hStep₁
  have hSvc₂ := cspaceInsertSlot_preserves_services s₂ s₂' dst cap hStep₂
  unfold lowEquivalent projectState; congr 1
  · funext oid
    by_cases hObs : objectObservable ctx observer oid
    · have hNe : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
      simp only [projectObjects, hObs, ite_true]
      rw [cspaceInsertSlot_preserves_objects_ne s₁ s₁' dst cap oid hNe hStep₁,
          cspaceInsertSlot_preserves_objects_ne s₂ s₂' dst cap oid hNe hStep₂]
      have h := congrFun (congrArg ObservableState.objects hLow) oid
      simp only [projectState, projectObjects, hObs, ite_true] at h
      exact h
    · simp [projectObjects, hObs]
  · simpa [projectRunnable, hSched₁, hSched₂] using congrArg ObservableState.runnable hLow
  · simpa [projectCurrent, hSched₁, hSched₂] using congrArg ObservableState.current hLow
  · funext sid; simp only [projectServiceStatus, lookupService]
    rw [show s₁'.services = s₁.services from hSvc₁, show s₂'.services = s₂.services from hSvc₂]
    have h := congrFun (congrArg ObservableState.services hLow) sid
    simp only [projectState, projectServiceStatus] at h
    exact h
  · simpa [projectActiveDomain, hSched₁, hSched₂] using congrArg ObservableState.activeDomain hLow
  · funext irq; simp only [projectIrqHandlers]
    rw [cspaceInsertSlot_preserves_irqHandlers s₁ s₁' dst cap hStep₁,
        cspaceInsertSlot_preserves_irqHandlers s₂ s₂' dst cap hStep₂]
    exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
  · rw [cspaceInsertSlot_preserves_projectObjectIndex s₁ s₁' dst cap hDstHigh hStep₁,
        cspaceInsertSlot_preserves_projectObjectIndex s₂ s₂' dst cap hDstHigh hStep₂]
    exact congrArg ObservableState.objectIndex hLow
  · -- domainTimeRemaining
    simpa [projectDomainTimeRemaining, hSched₁, hSched₂] using congrArg ObservableState.domainTimeRemaining hLow
  · -- domainSchedule
    simpa [projectDomainSchedule, hSched₁, hSched₂] using congrArg ObservableState.domainSchedule hLow
  · -- domainScheduleIndex
    simpa [projectDomainScheduleIndex, hSched₁, hSched₂] using congrArg ObservableState.domainScheduleIndex hLow
  · -- machineRegs
    have hM₁ := cspaceInsertSlot_preserves_machine s₁ s₁' dst cap hStep₁
    have hM₂ := cspaceInsertSlot_preserves_machine s₂ s₂' dst cap hStep₂
    simp [projectMachineRegs, hSched₁, hSched₂, hM₁, hM₂]
    exact congrArg ObservableState.machineRegs hLow

