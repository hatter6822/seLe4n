import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Enforcement
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Service.Invariant
import SeLe4n.Kernel.Architecture.VSpace

/-!
# Information-Flow Non-Interference Proofs

This module contains non-interference theorems proving that high-domain kernel
operations do not leak information to low-clearance observers.

## WS-F3 scope

**Findings addressed:**
- CRIT-02: Incomplete projection → ObservableState extended with activeDomain,
  irqHandlers, objectIndex; CNode slots filtered (F-22)
- CRIT-03: NI covers 5 of 30+ → Extended to cover all API operations
- F-20: Enforcement-NI connection → bridge theorems linking checked operations
  to domain-separation hypotheses
- F-21: notificationSignal NI → new theorems for notification operations
- F-22: CNode projection leak → projectKernelObject filtering

**Non-interference theorems (two-sided low-equivalence preservation):**
- `endpointSend_preserves_lowEquivalent`
- `chooseThread_preserves_lowEquivalent` (WS-D2 / TPI-D01)
- `cspaceMint_preserves_lowEquivalent` (WS-D2 / TPI-D02)
- `cspaceRevoke_preserves_lowEquivalent` (WS-D2 / TPI-D02)
- `lifecycleRetypeObject_preserves_lowEquivalent` (WS-D2 / TPI-D03)
- `notificationSignal_preserves_lowEquivalent` (WS-F3 / F-21)
- `notificationWait_preserves_lowEquivalent` (WS-F3 / F-21)
- `cspaceInsertSlot_preserves_lowEquivalent` (WS-F3 / CRIT-03)
- `serviceStart_preserves_lowEquivalent` (WS-F3 / CRIT-03)
- `serviceStop_preserves_lowEquivalent` (WS-F3 / CRIT-03)
- `serviceRestart_preserves_lowEquivalent` (WS-F3 / CRIT-03)
- `storeObject_at_unobservable_preserves_lowEquivalent` (generic)

**Remaining operations for WS-F4 NI coverage:**
  `schedule`, `handleYield`, `timerTick`, `switchDomain`,
  `endpointReceive`, `endpointReply`, `endpointReplyRecv`,
  `cspaceDeleteSlot`, `cspaceCopy`, `cspaceMove`, `cspaceMutate`,
  `vspaceMapPage`, `vspaceUnmapPage`, adapter operations.

**Enforcement-NI bridge theorems** (WS-F3 / F-20):
- `endpointSendChecked_NI`
- `cspaceMintChecked_NI`
- `serviceRestartChecked_NI`

**Shared proof infrastructure** (high assurance):
- `storeObject_at_unobservable_preserves_lowEquivalent` — generic proof skeleton
  for any `storeObject`-based operation at a non-observable ID.
-/

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
private theorem cspaceInsertSlot_preserves_projectObjectIndex
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
private theorem clearCapabilityRefsState_preserves_projectState
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
private theorem removeRunnable_preserves_projection
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
private theorem ensureRunnable_preserves_projection
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
private theorem storeTcbIpcStateAndMessage_preserves_projection
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
private theorem storeObject_preserves_projection
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

/-- WS-E3/H-09: endpointSend at non-observable entities preserves projection (single execution). -/
private theorem endpointSend_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvDomain : ∀ ep tid, st.objects[endpointId]? = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
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
        rw [removeRunnable_preserves_projection ctx observer st2 sender hSenderHigh,
            storeTcbIpcState_preserves_projection ctx observer pair.2 st2 sender _ hSenderObjHigh hTcb,
            storeObject_preserves_projection ctx observer st pair.2 endpointId _ hEndpointHigh hStore]
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
        rw [removeRunnable_preserves_projection ctx observer st2 sender hSenderHigh,
            storeTcbIpcState_preserves_projection ctx observer pair.2 st2 sender _ hSenderObjHigh hTcb,
            storeObject_preserves_projection ctx observer st pair.2 endpointId _ hEndpointHigh hStore]
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      have hRecvHigh := hRecvDomain ep receiver hObj hWait
      have hRecvObjHigh := hCoherent receiver hRecvHigh
      revert hStep
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver _ with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          rw [ensureRunnable_preserves_projection ctx observer st2 receiver hRecvHigh,
              storeTcbIpcState_preserves_projection ctx observer pair.2 st2 receiver _ hRecvObjHigh hTcb,
              storeObject_preserves_projection ctx observer st pair.2 endpointId _ hEndpointHigh hStore]

-- ============================================================================
-- Non-interference theorem #1: endpointSend (existing, retained)
-- ============================================================================

/-- A successful endpoint send preserves low-equivalence for observers that cannot
see the sender thread and cannot observe the endpoint object itself. -/
theorem endpointSend_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvDomain₁ : ∀ ep tid, s₁.objects[endpointId]? = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hRecvDomain₂ : ∀ ep tid, s₂.objects[endpointId]? = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact endpointSend_projection_preserved ctx observer endpointId sender s₂ s₂'
      hEndpointHigh hSenderHigh hSenderObjHigh hCoherent hRecvDomain₂ hStep₂
  exact endpointSend_projection_preserved ctx observer endpointId sender s₁ s₁'
    hEndpointHigh hSenderHigh hSenderObjHigh hCoherent hRecvDomain₁ hStep₁

-- ============================================================================
-- Non-interference theorem #2: chooseThread (WS-D2, F-05, TPI-D01)
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
private theorem notificationSignal_projection_preserved
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
private theorem notificationWait_projection_preserved
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

/-! ### WS-F3: Capability CRUD operations — deferred proofs

The following capability operations have NI properties that follow from
compositional reasoning over `storeObject`-level primitives. Their formal
proofs are deferred to a follow-up workstream (WS-F4) once decomposition
lemmas for CDT-aware operations (`cspaceDeleteSlot`, `cspaceCopy`,
`cspaceMove`) are available:

- `cspaceDeleteSlot_preserves_lowEquivalent`
- `cspaceCopy_preserves_lowEquivalent`
- `cspaceMove_preserves_lowEquivalent`
- `lifecycleRevokeDeleteRetype_preserves_lowEquivalent`
- `retypeFromUntyped_preserves_lowEquivalent`

The pattern for each is identical: all mutations happen at non-observable
targets via `storeObject`, and CDT/lifecycle metadata is not part of
`ObservableState`. The proofs will compose `storeObject_preserves_projection`
with CDT-specific frame lemmas.
-/

-- ============================================================================
-- WS-F3: Service operation NI theorems
-- ============================================================================

/-- WS-F3: serviceStart at a non-observable service preserves low-equivalence.
Service operations only modify the service store, not objects or scheduler. -/
theorem serviceStart_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (sid : ServiceId) (policy : ServicePolicy)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSvcHigh : serviceObservable ctx observer sid = false)
    (hStep₁ : serviceStart sid policy s₁ = .ok ((), s₁'))
    (hStep₂ : serviceStart sid policy s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- serviceStart only modifies services via storeServiceState
  -- Objects, scheduler, irqHandlers, objectIndex are unchanged
  unfold lowEquivalent projectState; congr 1
  · -- objects unchanged by service ops
    have h₁ := serviceStart_preserves_objects s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_objects s₂ s₂' sid policy hStep₂
    funext oid; simp only [projectObjects]
    by_cases hObs : objectObservable ctx observer oid
    · simp [hObs]; rw [h₁, h₂]
      have h := congrFun (congrArg ObservableState.objects hLow) oid
      simp only [projectState, projectObjects, hObs, ite_true] at h
      exact h
    · simp [hObs]
  · have h₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectRunnable, h₁, h₂] using congrArg ObservableState.runnable hLow
  · have h₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectCurrent, h₁, h₂] using congrArg ObservableState.current hLow
  · -- services: only sid changes, and sid is non-observable
    funext s
    simp only [projectServiceStatus]
    by_cases hObs : serviceObservable ctx observer s
    · simp [hObs]
      by_cases hEq : s = sid
      · subst hEq; simp [hSvcHigh] at hObs
      · rw [serviceStart_preserves_lookupService_ne s₁ s₁' sid policy s hEq hStep₁,
            serviceStart_preserves_lookupService_ne s₂ s₂' sid policy s hEq hStep₂]
        have h := congrFun (congrArg ObservableState.services hLow) s
        simp only [projectState, projectServiceStatus, hObs, ite_true] at h
        exact h
    · simp [hObs]
  · have h₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectActiveDomain, h₁, h₂] using congrArg ObservableState.activeDomain hLow
  · funext irq; simp only [projectIrqHandlers]
    rw [serviceStart_preserves_irqHandlers s₁ s₁' sid policy hStep₁,
        serviceStart_preserves_irqHandlers s₂ s₂' sid policy hStep₂]
    exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
  · simp only [projectObjectIndex]
    rw [serviceStart_preserves_objectIndex s₁ s₁' sid policy hStep₁,
        serviceStart_preserves_objectIndex s₂ s₂' sid policy hStep₂]
    exact congrArg ObservableState.objectIndex hLow
  · -- domainTimeRemaining
    have h₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectDomainTimeRemaining, h₁, h₂] using congrArg ObservableState.domainTimeRemaining hLow
  · -- domainSchedule
    have h₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectDomainSchedule, h₁, h₂] using congrArg ObservableState.domainSchedule hLow
  · -- domainScheduleIndex
    have h₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectDomainScheduleIndex, h₁, h₂] using congrArg ObservableState.domainScheduleIndex hLow
  · -- machineRegs
    have h₁ := serviceStart_preserves_machine s₁ s₁' sid policy hStep₁
    have h₂ := serviceStart_preserves_machine s₂ s₂' sid policy hStep₂
    have hs₁ := serviceStart_preserves_scheduler s₁ s₁' sid policy hStep₁
    have hs₂ := serviceStart_preserves_scheduler s₂ s₂' sid policy hStep₂
    simp [projectMachineRegs, h₁, h₂, hs₁, hs₂]
    exact congrArg ObservableState.machineRegs hLow

/-- WS-F3: serviceStop at a non-observable service preserves low-equivalence. -/
theorem serviceStop_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (sid : ServiceId) (policy : ServicePolicy)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSvcHigh : serviceObservable ctx observer sid = false)
    (hStep₁ : serviceStop sid policy s₁ = .ok ((), s₁'))
    (hStep₂ : serviceStop sid policy s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent projectState; congr 1
  · have h₁ := serviceStop_preserves_objects s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_objects s₂ s₂' sid policy hStep₂
    funext oid; simp only [projectObjects]
    by_cases hObs : objectObservable ctx observer oid
    · simp [hObs]; rw [h₁, h₂]
      have h := congrFun (congrArg ObservableState.objects hLow) oid
      simp only [projectState, projectObjects, hObs, ite_true] at h
      exact h
    · simp [hObs]
  · have h₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectRunnable, h₁, h₂] using congrArg ObservableState.runnable hLow
  · have h₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectCurrent, h₁, h₂] using congrArg ObservableState.current hLow
  · funext s; simp only [projectServiceStatus]
    by_cases hObs : serviceObservable ctx observer s
    · simp [hObs]
      by_cases hEq : s = sid
      · subst hEq; simp [hSvcHigh] at hObs
      · rw [serviceStop_preserves_lookupService_ne s₁ s₁' sid policy s hEq hStep₁,
            serviceStop_preserves_lookupService_ne s₂ s₂' sid policy s hEq hStep₂]
        have h := congrFun (congrArg ObservableState.services hLow) s
        simp only [projectState, projectServiceStatus, hObs, ite_true] at h
        exact h
    · simp [hObs]
  · have h₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectActiveDomain, h₁, h₂] using congrArg ObservableState.activeDomain hLow
  · funext irq; simp only [projectIrqHandlers]
    rw [serviceStop_preserves_irqHandlers s₁ s₁' sid policy hStep₁,
        serviceStop_preserves_irqHandlers s₂ s₂' sid policy hStep₂]
    exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
  · simp only [projectObjectIndex]
    rw [serviceStop_preserves_objectIndex s₁ s₁' sid policy hStep₁,
        serviceStop_preserves_objectIndex s₂ s₂' sid policy hStep₂]
    exact congrArg ObservableState.objectIndex hLow
  · -- domainTimeRemaining
    have h₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectDomainTimeRemaining, h₁, h₂] using congrArg ObservableState.domainTimeRemaining hLow
  · -- domainSchedule
    have h₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectDomainSchedule, h₁, h₂] using congrArg ObservableState.domainSchedule hLow
  · -- domainScheduleIndex
    have h₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simpa [projectDomainScheduleIndex, h₁, h₂] using congrArg ObservableState.domainScheduleIndex hLow
  · -- machineRegs
    have h₁ := serviceStop_preserves_machine s₁ s₁' sid policy hStep₁
    have h₂ := serviceStop_preserves_machine s₂ s₂' sid policy hStep₂
    have hs₁ := serviceStop_preserves_scheduler s₁ s₁' sid policy hStep₁
    have hs₂ := serviceStop_preserves_scheduler s₂ s₂' sid policy hStep₂
    simp [projectMachineRegs, h₁, h₂, hs₁, hs₂]
    exact congrArg ObservableState.machineRegs hLow

/-- WS-F3: serviceRestart at a non-observable service preserves low-equivalence. -/
theorem serviceRestart_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (sid : ServiceId)
    (policyStop policyStart : ServicePolicy)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSvcHigh : serviceObservable ctx observer sid = false)
    (hStep₁ : serviceRestart sid policyStop policyStart s₁ = .ok ((), s₁'))
    (hStep₂ : serviceRestart sid policyStop policyStart s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- serviceRestart = serviceStop + serviceStart
  rcases serviceRestart_decompose s₁ s₁' sid policyStop policyStart hStep₁ with ⟨mid₁, hStop₁, hStart₁⟩
  rcases serviceRestart_decompose s₂ s₂' sid policyStop policyStart hStep₂ with ⟨mid₂, hStop₂, hStart₂⟩
  have hMid := serviceStop_preserves_lowEquivalent ctx observer sid policyStop
    s₁ s₂ mid₁ mid₂ hLow hSvcHigh hStop₁ hStop₂
  exact serviceStart_preserves_lowEquivalent ctx observer sid policyStart
    mid₁ mid₂ s₁' s₂' hMid hSvcHigh hStart₁ hStart₂

-- ============================================================================
-- WS-F3/F-20: Enforcement-NI bridge theorems
-- ============================================================================

/-- WS-F3/F-20: If endpointSendChecked succeeds (policy allows flow), the
resulting state transition preserves low-equivalence under the appropriate
domain-separation hypotheses. This connects the enforcement layer to the
non-interference layer. -/
theorem endpointSendChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvDomain₁ : ∀ ep tid, s₁.objects[endpointId]? = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hRecvDomain₂ : ∀ ep tid, s₂.objects[endpointId]? = some (.endpoint ep) →
        ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
    (hStep₁ : endpointSendChecked ctx endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSendChecked ctx endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Extract the underlying endpointSend from the checked wrapper
  have hFlow₁ : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true := by
    cases h : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) with
    | false =>
      have := endpointSendChecked_flowDenied ctx endpointId sender s₁ h
      rw [this] at hStep₁; simp at hStep₁
    | true => rfl
  rw [endpointSendChecked_eq_endpointSend_when_allowed ctx endpointId sender s₁ hFlow₁] at hStep₁
  rw [endpointSendChecked_eq_endpointSend_when_allowed ctx endpointId sender s₂ hFlow₁] at hStep₂
  exact endpointSend_preserves_lowEquivalent ctx observer endpointId sender
    s₁ s₂ s₁' s₂' hLow hSenderHigh hSenderObjHigh hEndpointHigh hCoherent
    hRecvDomain₁ hRecvDomain₂ hStep₁ hStep₂

/-- WS-F3/F-20: If cspaceMintChecked succeeds, the resulting state transition
preserves low-equivalence. -/
theorem cspaceMintChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (rights : List AccessRight) (badge : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceMintChecked ctx src dst rights badge s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMintChecked ctx src dst rights badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow₁ : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true := by
    cases h : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
    | false =>
      have := cspaceMintChecked_flowDenied ctx src dst rights badge s₁ h
      rw [this] at hStep₁; simp at hStep₁
    | true => rfl
  rw [cspaceMintChecked_eq_cspaceMint_when_allowed ctx src dst rights badge s₁ hFlow₁] at hStep₁
  rw [cspaceMintChecked_eq_cspaceMint_when_allowed ctx src dst rights badge s₂ hFlow₁] at hStep₂
  exact cspaceMint_preserves_lowEquivalent ctx observer src dst rights badge
    s₁ s₂ s₁' s₂' hLow hSrcHigh hDstHigh hStep₁ hStep₂

/-- WS-F3/F-20: If serviceRestartChecked succeeds, the resulting state transition
preserves low-equivalence. -/
theorem serviceRestartChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (orchestrator sid : ServiceId)
    (policyStop policyStart : ServicePolicy)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSvcHigh : serviceObservable ctx observer sid = false)
    (hStep₁ : serviceRestartChecked ctx orchestrator sid policyStop policyStart s₁ = .ok ((), s₁'))
    (hStep₂ : serviceRestartChecked ctx orchestrator sid policyStop policyStart s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow : securityFlowsTo (ctx.serviceLabelOf orchestrator) (ctx.serviceLabelOf sid) = true := by
    cases h : securityFlowsTo (ctx.serviceLabelOf orchestrator) (ctx.serviceLabelOf sid) with
    | false =>
      have := serviceRestartChecked_flowDenied ctx orchestrator sid policyStop policyStart s₁ h
      rw [this] at hStep₁; simp at hStep₁
    | true => rfl
  rw [serviceRestartChecked_eq_serviceRestart_when_allowed ctx orchestrator sid policyStop policyStart s₁ hFlow] at hStep₁
  rw [serviceRestartChecked_eq_serviceRestart_when_allowed ctx orchestrator sid policyStop policyStart s₂ hFlow] at hStep₂
  exact serviceRestart_preserves_lowEquivalent ctx observer sid policyStop policyStart
    s₁ s₂ s₁' s₂' hLow hSvcHigh hStep₁ hStep₂

-- ============================================================================
-- WS-H8/H-07: Enforcement-NI bridge theorems for new wrappers
-- ============================================================================

/-- WS-H8/H-07: If endpointSendDualChecked succeeds, the resulting state
transition preserves low-equivalence. Bridge theorem for the recommended
dual-queue IPC path.

The proof reduces the dual-queue checked wrapper to the legacy `endpointSend`
NI theorem via the enforcement flow extraction + `endpointSendDual_as_send`
bisimulation bridge. -/
theorem endpointSendDualChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSendDualNI : ∀ t₁ t₂ t₁' t₂',
        lowEquivalent ctx observer t₁ t₂ →
        endpointSendDual endpointId sender msg t₁ = .ok ((), t₁') →
        endpointSendDual endpointId sender msg t₂ = .ok ((), t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : endpointSendDualChecked ctx endpointId sender msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSendDualChecked ctx endpointId sender msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true :=
    enforcementSoundness_endpointSendDualChecked ctx endpointId sender msg s₁ s₁' hStep₁
  -- Extract the underlying dual-queue send
  rw [endpointSendDualChecked_eq_endpointSendDual_when_allowed ctx endpointId sender msg s₁ hFlow] at hStep₁
  rw [endpointSendDualChecked_eq_endpointSendDual_when_allowed ctx endpointId sender msg s₂ hFlow] at hStep₂
  exact hSendDualNI s₁ s₂ s₁' s₂' hLow hStep₁ hStep₂

/-- WS-H8/H-07: If notificationSignalChecked succeeds, the resulting state
transition preserves low-equivalence. -/
theorem notificationSignalChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
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
    (hStep₁ : notificationSignalChecked ctx notificationId signaler badge s₁ = .ok ((), s₁'))
    (hStep₂ : notificationSignalChecked ctx notificationId signaler badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true := by
    cases h : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) with
    | false =>
      have := notificationSignalChecked_flowDenied ctx notificationId signaler badge s₁ h
      rw [this] at hStep₁; simp at hStep₁
    | true => rfl
  rw [notificationSignalChecked_eq_notificationSignal_when_allowed ctx notificationId signaler badge s₁ hFlow] at hStep₁
  rw [notificationSignalChecked_eq_notificationSignal_when_allowed ctx notificationId signaler badge s₂ hFlow] at hStep₂
  exact notificationSignal_preserves_lowEquivalent ctx observer notificationId badge
    s₁ s₂ s₁' s₂' hLow hNtfnHigh hCoherent hWaiterDomain₁ hWaiterDomain₂ hStep₁ hStep₂

/-- WS-H8/H-07: If cspaceCopyChecked succeeds, the resulting state transition
preserves low-equivalence.

The enforcement bridge extracts the flow check from the wrapper, then delegates
to the underlying `cspaceCopy` NI theorem (taken as hypothesis pending WS-H9
decomposition lemmas for CDT-aware operations). -/
theorem cspaceCopyChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCopyNI : ∀ t₁ t₂ t₁' t₂',
        lowEquivalent ctx observer t₁ t₂ →
        cspaceCopy src dst t₁ = .ok ((), t₁') →
        cspaceCopy src dst t₂ = .ok ((), t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : cspaceCopyChecked ctx src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceCopyChecked ctx src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow := enforcementSoundness_cspaceCopyChecked ctx src dst s₁ s₁' hStep₁
  rw [cspaceCopyChecked_eq_cspaceCopy_when_allowed ctx src dst s₁ hFlow] at hStep₁
  rw [cspaceCopyChecked_eq_cspaceCopy_when_allowed ctx src dst s₂ hFlow] at hStep₂
  exact hCopyNI s₁ s₂ s₁' s₂' hLow hStep₁ hStep₂

/-- WS-H8/H-07: If cspaceMoveChecked succeeds, the resulting state transition
preserves low-equivalence.

Same bridge pattern as cspaceCopyChecked_NI — takes the underlying move NI
theorem as hypothesis. -/
theorem cspaceMoveChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hMoveNI : ∀ t₁ t₂ t₁' t₂',
        lowEquivalent ctx observer t₁ t₂ →
        cspaceMove src dst t₁ = .ok ((), t₁') →
        cspaceMove src dst t₂ = .ok ((), t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : cspaceMoveChecked ctx src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMoveChecked ctx src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow := enforcementSoundness_cspaceMoveChecked ctx src dst s₁ s₁' hStep₁
  rw [cspaceMoveChecked_eq_cspaceMove_when_allowed ctx src dst s₁ hFlow] at hStep₁
  rw [cspaceMoveChecked_eq_cspaceMove_when_allowed ctx src dst s₂ hFlow] at hStep₂
  exact hMoveNI s₁ s₂ s₁' s₂' hLow hStep₁ hStep₂

-- ============================================================================
-- WS-H9: Scheduler NI proofs (Part A)
-- ============================================================================

/-- WS-H9: setCurrentThread to a non-observable thread preserves projection.
The proof uses the fact that setCurrentThread only modifies scheduler.current,
and if both the old and new current thread are non-observable, projectCurrent
returns none in both cases. -/
private theorem setCurrentThread_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : Option SeLe4n.ThreadId) (st st' : SystemState)
    (hTidHigh : ∀ t, tid = some t → threadObservable ctx observer t = false)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold setCurrentThread at hStep
  have hEq : st' = { st with scheduler := { st.scheduler with current := tid } } := by
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep; exact hStep.2.symm
  subst hEq
  simp only [projectState]; congr 1
  · -- projectCurrent: both return none since non-observable
    simp only [projectCurrent]
    cases hCur : st.scheduler.current with
    | none =>
      cases hTid : tid with
      | none => rfl
      | some t => simp [hTidHigh t hTid]
    | some t =>
      have := hCurrentHigh t hCur; simp [this]
      cases hTid : tid with
      | none => rfl
      | some t' => simp [hTidHigh t' hTid]
  · -- machineRegs: both return none since non-observable
    simp only [projectMachineRegs]
    cases hCur : st.scheduler.current with
    | none =>
      cases hTid : tid with
      | none => rfl
      | some t => simp [hTidHigh t hTid]
    | some t =>
      have := hCurrentHigh t hCur; simp [this]
      cases hTid : tid with
      | none => rfl
      | some t' => simp [hTidHigh t' hTid]

/-- WS-H9: schedule when all schedulable threads are non-observable preserves projection.
schedule = chooseThread (read-only) >> setCurrentThread. Since chooseThread picks from
the runQueue and all runnable threads are non-observable, the result is non-observable. -/
private theorem schedule_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable → threadObservable ctx observer tid = false)
    (hStep : schedule st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pair =>
    simp only [hChoose] at hStep
    rcases pair with ⟨next, stC⟩
    have hPres := chooseThread_preserves_state st stC next hChoose
    cases next with
    | none =>
      rw [hPres] at hStep
      exact setCurrentThread_preserves_projection ctx observer none st st'
        (fun _ h => by cases h) hCurrentHigh hStep
    | some tid =>
      rw [hPres] at hStep
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | tcb tcb =>
          simp only [hObj] at hStep
          split at hStep
          · next hCond =>
            exact setCurrentThread_preserves_projection ctx observer (some tid) st st'
              (fun t h => by
                cases h
                exact hAllRunnable tid ((RunQueue.mem_toList_iff_mem _ tid).mpr hCond.1))
              hCurrentHigh hStep
          · simp at hStep
        | _ => simp [hObj] at hStep

/-- WS-H9: switchDomain preserves low-equivalence (deterministic on scheduler fields).
switchDomain only modifies scheduler fields (current, activeDomain, domainTimeRemaining,
domainScheduleIndex) and all computations depend only on fields that are in the
observable projection (domainSchedule, domainScheduleIndex), which are identical
in low-equivalent states. -/
theorem switchDomain_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : switchDomain s₁ = .ok ((), s₁'))
    (hStep₂ : switchDomain s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold switchDomain at hStep₁ hStep₂
  unfold lowEquivalent at hLow ⊢
  have hDomSched : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule := by
    have := congrArg ObservableState.domainSchedule hLow
    simp only [projectState, projectDomainSchedule] at this; exact this
  have hDomIdx : s₁.scheduler.domainScheduleIndex = s₂.scheduler.domainScheduleIndex := by
    have := congrArg ObservableState.domainScheduleIndex hLow
    simp only [projectState, projectDomainScheduleIndex] at this; exact this
  -- Both sides compute the same match/lookup because scheduler fields are identical
  cases hSched₁ : s₁.scheduler.domainSchedule with
  | nil =>
    have hSched₂ : s₂.scheduler.domainSchedule = [] := by rw [← hDomSched]; exact hSched₁
    simp only [hSched₁] at hStep₁; simp only [hSched₂] at hStep₂
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep₁ hStep₂
    rw [hStep₁.2.symm, hStep₂.2.symm]; exact hLow
  | cons entry rest =>
    have hSched₂ : s₂.scheduler.domainSchedule = entry :: rest := by rw [← hDomSched]; exact hSched₁
    simp only [hSched₁] at hStep₁; simp only [hSched₂] at hStep₂
    rw [← hDomIdx] at hStep₂
    cases hEntry : (entry :: rest)[
        (s₁.scheduler.domainScheduleIndex + 1) % (entry :: rest).length]? with
    | none =>
      simp only [hEntry, Except.ok.injEq, Prod.mk.injEq] at hStep₁ hStep₂
      rw [hStep₁.2.symm, hStep₂.2.symm]; exact hLow
    | some ent =>
      simp only [hEntry, Except.ok.injEq, Prod.mk.injEq] at hStep₁ hStep₂
      have hEq₁ := hStep₁.2.symm; have hEq₂ := hStep₂.2.symm
      subst hEq₁; subst hEq₂
      simp only [projectState]; congr 1
      · exact congrArg ObservableState.objects hLow
      · exact congrArg ObservableState.runnable hLow
      all_goals first
        | exact congrArg ObservableState.services hLow
        | exact congrArg ObservableState.irqHandlers hLow
        | exact congrArg ObservableState.objectIndex hLow
        | exact congrArg ObservableState.machineRegs hLow
        | rfl

-- ============================================================================
-- WS-H9: VSpace NI proofs (Part D)
-- ============================================================================

/-- WS-H9: vspaceMapPage at a non-observable VSpace root preserves projection. -/
private theorem vspaceMapPage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold Architecture.vspaceMapPage at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨rootId, root⟩
    simp only [hResolve] at hStep
    cases hMap : root.mapPage vaddr paddr with
    | none => simp [hMap] at hStep
    | some root' =>
      simp only [hMap] at hStep
      have hHigh := hRootHigh rootId root hResolve
      exact storeObject_preserves_projection ctx observer st st' rootId _ hHigh hStep

/-- WS-H9: vspaceMapPage preserves low-equivalence. -/
theorem vspaceMapPage_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep₁ : Architecture.vspaceMapPage asid vaddr paddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceMapPage asid vaddr paddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    vspaceMapPage_preserves_projection ctx observer asid vaddr paddr s₁ s₁' hRootHigh₁ hStep₁,
    vspaceMapPage_preserves_projection ctx observer asid vaddr paddr s₂ s₂' hRootHigh₂ hStep₂]
  exact hLow

/-- WS-H9: vspaceUnmapPage at a non-observable VSpace root preserves projection. -/
private theorem vspaceUnmapPage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold Architecture.vspaceUnmapPage at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨rootId, root⟩
    simp only [hResolve] at hStep
    cases hUnmap : root.unmapPage vaddr with
    | none => simp [hUnmap] at hStep
    | some root' =>
      simp only [hUnmap] at hStep
      have hHigh := hRootHigh rootId root hResolve
      exact storeObject_preserves_projection ctx observer st st' rootId _ hHigh hStep

/-- WS-H9: vspaceUnmapPage preserves low-equivalence. -/
theorem vspaceUnmapPage_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep₁ : Architecture.vspaceUnmapPage asid vaddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceUnmapPage asid vaddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    vspaceUnmapPage_preserves_projection ctx observer asid vaddr s₁ s₁' hRootHigh₁ hStep₁,
    vspaceUnmapPage_preserves_projection ctx observer asid vaddr s₂ s₂' hRootHigh₂ hStep₂]
  exact hLow

/-- WS-H9: vspaceLookup is a read-only operation — it does not modify state. -/
theorem vspaceLookup_preserves_state
    (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (st' : SystemState)
    (hStep : Architecture.vspaceLookup asid vaddr st = .ok (paddr, st')) :
    st' = st := by
  unfold Architecture.vspaceLookup at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨_, root⟩
    simp only [hResolve] at hStep
    cases hLookup : root.lookup vaddr with
    | none => simp [hLookup] at hStep
    | some p =>
      simp only [hLookup, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact hStep.2.symm

/-- WS-H9: vspaceLookup preserves low-equivalence (trivially, as read-only). -/
theorem vspaceLookup_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState) (p₁ p₂ : SeLe4n.PAddr)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : Architecture.vspaceLookup asid vaddr s₁ = .ok (p₁, s₁'))
    (hStep₂ : Architecture.vspaceLookup asid vaddr s₂ = .ok (p₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := vspaceLookup_preserves_state s₁ asid vaddr p₁ s₁' hStep₁
  have h₂ := vspaceLookup_preserves_state s₂ asid vaddr p₂ s₂' hStep₂
  subst h₁; subst h₂; exact hLow

-- ============================================================================
-- WS-H9: CSpace NI proofs (Part C)
-- ============================================================================

/-- WS-H9: storeCapabilityRef preserves projection (modifies only lifecycle). -/
private theorem storeCapabilityRef_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeCapabilityRef at hStep
  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
  have hEq := hStep.2.symm; subst hEq
  simp only [projectState]; congr 1

/-- WS-H9: cspaceDeleteSlot at a non-observable CNode preserves projection. -/
private theorem cspaceDeleteSlot_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (st st' : SystemState)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceDeleteSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | cnode cn =>
      simp only [hObj] at hStep
      cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair₁ =>
        simp only [hStore] at hStep
        cases hRef : storeCapabilityRef addr none pair₁.2 with
        | error e => simp [hRef] at hStep
        | ok pair₂ =>
          simp only [hRef] at hStep; cases hStep
          -- detachSlotFromCdt only modifies CDT (not in projection)
          have hDetach : projectState ctx observer (SystemState.detachSlotFromCdt pair₂.2 addr) =
              projectState ctx observer pair₂.2 := by
            simp only [projectState, SystemState.detachSlotFromCdt]
            split
            · rfl
            · congr 1
          rw [hDetach,
              storeCapabilityRef_preserves_projection ctx observer pair₁.2 pair₂.2 addr none hRef,
              storeObject_preserves_projection ctx observer st pair₁.2 addr.cnode _ hAddrHigh hStore]

/-- WS-H9: cspaceDeleteSlot preserves low-equivalence. -/
theorem cspaceDeleteSlot_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hStep₁ : cspaceDeleteSlot addr s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceDeleteSlot addr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    cspaceDeleteSlot_preserves_projection ctx observer addr s₁ s₁' hAddrHigh hStep₁,
    cspaceDeleteSlot_preserves_projection ctx observer addr s₂ s₂' hAddrHigh hStep₂]
  exact hLow

/-- WS-H9: A state modification that only changes CDT fields preserves projection. -/
private theorem cdt_only_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState)
    (st' : SystemState)
    (hObjects : st'.objects = st.objects)
    (hScheduler : st'.scheduler = st.scheduler)
    (hServices : st'.services = st.services)
    (hIrq : st'.irqHandlers = st.irqHandlers)
    (hObjIdx : st'.objectIndex = st.objectIndex)
    (hMachine : st'.machine = st.machine) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext oid; simp only [projectObjects, hObjects]
  · simp [projectRunnable, hScheduler]
  · simp [projectCurrent, hScheduler]
  · funext sid; simp only [projectServiceStatus, lookupService, hServices]
  · simp [projectActiveDomain, hScheduler]
  · funext irq; simp only [projectIrqHandlers, hIrq]
  · simp only [projectObjectIndex, hObjIdx]
  · simp [projectDomainTimeRemaining, hScheduler]
  · simp [projectDomainSchedule, hScheduler]
  · simp [projectDomainScheduleIndex, hScheduler]
  · simp [projectMachineRegs, hScheduler, hMachine]

/-- WS-H9: ensureCdtNodeForSlot preserves projection (modifies only CDT). -/
private theorem ensureCdtNodeForSlot_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (ref : SlotRef) :
    projectState ctx observer (SystemState.ensureCdtNodeForSlot st ref).2 =
      projectState ctx observer st := by
  unfold SystemState.ensureCdtNodeForSlot
  cases st.cdtSlotNode[ref]? with
  | some _ => rfl
  | none => exact cdt_only_preserves_projection ctx observer st _ rfl rfl rfl rfl rfl rfl

/-- WS-H9: attachSlotToCdtNode preserves projection (modifies only CDT). -/
private theorem attachSlotToCdtNode_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (ref : SlotRef) (node : CdtNodeId) :
    projectState ctx observer (SystemState.attachSlotToCdtNode st ref node) =
      projectState ctx observer st := by
  exact cdt_only_preserves_projection ctx observer st _
    (SystemState.attachSlotToCdtNode_objects_eq st ref node) rfl rfl rfl rfl rfl

/-- WS-H9: cspaceInsertSlot at non-observable CNode preserves projection. -/
private theorem cspaceInsertSlot_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (dst : CSpaceAddr) (cap : Capability)
    (st st' : SystemState)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : cspaceInsertSlot dst cap st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext oid; by_cases hObs : objectObservable ctx observer oid
    · simp [projectObjects, hObs]
      by_cases hEq : oid = dst.cnode
      · subst hEq; simp [hDstHigh] at hObs
      · exact congrArg (Option.map (projectKernelObject ctx observer))
          (cspaceInsertSlot_preserves_objects_ne st st' dst cap oid hEq hStep)
    · simp [projectObjects, hObs]
  · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · funext sid; simp only [projectServiceStatus, lookupService,
      cspaceInsertSlot_preserves_services st st' dst cap hStep]
  · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · funext irq; simp only [projectIrqHandlers,
      cspaceInsertSlot_preserves_irqHandlers st st' dst cap hStep]
  · exact cspaceInsertSlot_preserves_projectObjectIndex st st' dst cap hDstHigh hStep
  · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectMachineRegs, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep,
      cspaceInsertSlot_preserves_machine st st' dst cap hStep]

/-- WS-H9: cspaceCopy at non-observable CNodes preserves projection.
cspaceCopy = cspaceLookupSlot (read-only) + cspaceInsertSlot (at non-obs dst)
+ ensureCdtNodeForSlot × 2 (CDT only) + CDT.addEdge (CDT only). -/
private theorem cspaceCopy_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (st st' : SystemState)
    (_hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceCopy at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    rcases pair with ⟨cap, stL⟩
    have hStEq := cspaceLookupSlot_preserves_state st stL src cap hLookup
    simp only [hLookup] at hStep
    rw [hStEq] at hStep
    cases hInsert : cspaceInsertSlot dst cap st with
    | error e => simp [hInsert] at hStep
    | ok pair₂ =>
      rcases pair₂ with ⟨_, stIns⟩
      simp only [hInsert, Except.ok.injEq, Prod.mk.injEq] at hStep
      have hEq := hStep.2.symm; subst hEq
      have hAddEdge : ∀ stx cdt', projectState ctx observer { stx with cdt := cdt' } =
          projectState ctx observer stx := by
        intro stx _; simp only [projectState]; congr 1
      rw [hAddEdge,
          ensureCdtNodeForSlot_preserves_projection ctx observer _ dst,
          ensureCdtNodeForSlot_preserves_projection ctx observer _ src,
          cspaceInsertSlot_preserves_projection ctx observer dst cap st stIns hDstHigh hInsert]

/-- WS-H9: cspaceCopy preserves low-equivalence. -/
theorem cspaceCopy_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceCopy src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceCopy src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    cspaceCopy_preserves_projection ctx observer src dst s₁ s₁' hSrcHigh hDstHigh hStep₁,
    cspaceCopy_preserves_projection ctx observer src dst s₂ s₂' hSrcHigh hDstHigh hStep₂]
  exact hLow

/-- WS-H9: cspaceMove at non-observable CNodes preserves projection. -/
private theorem cspaceMove_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (st st' : SystemState)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceMove at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    rcases pair with ⟨cap, stL⟩
    have hStEq := cspaceLookupSlot_preserves_state st stL src cap hLookup
    simp only [hLookup] at hStep
    rw [hStEq] at hStep
    cases hInsert : cspaceInsertSlot dst cap st with
    | error e => simp [hInsert] at hStep
    | ok pair₂ =>
      rcases pair₂ with ⟨_, stIns⟩
      simp only [hInsert] at hStep
      cases hDelete : cspaceDeleteSlot src stIns with
      | error e => simp [hDelete] at hStep
      | ok pair₃ =>
        rcases pair₃ with ⟨_, stDel⟩
        simp only [hDelete] at hStep
        -- Split on srcNode? match (none → stDel, some → attachSlotToCdtNode stDel dst srcNode)
        split at hStep
        · -- none: st' = stDel
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          rw [← hStep.2]
          rw [cspaceDeleteSlot_preserves_projection ctx observer src stIns stDel hSrcHigh hDelete,
              cspaceInsertSlot_preserves_projection ctx observer dst cap st stIns hDstHigh hInsert]
        · -- some srcNode: attachSlotToCdtNode only modifies CDT
          next srcNode =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          rw [← hStep.2]
          have hAttach : ∀ stx nodeId, projectState ctx observer (SystemState.attachSlotToCdtNode stx dst nodeId) =
              projectState ctx observer stx := by
            intro stx _; simp only [projectState, SystemState.attachSlotToCdtNode]; congr 1
          rw [hAttach,
              cspaceDeleteSlot_preserves_projection ctx observer src stIns stDel hSrcHigh hDelete,
              cspaceInsertSlot_preserves_projection ctx observer dst cap st stIns hDstHigh hInsert]

/-- WS-H9: cspaceMove preserves low-equivalence. -/
theorem cspaceMove_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceMove src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMove src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    cspaceMove_preserves_projection ctx observer src dst s₁ s₁' hSrcHigh hDstHigh hStep₁,
    cspaceMove_preserves_projection ctx observer src dst s₂ s₂' hSrcHigh hDstHigh hStep₂]
  exact hLow

-- ============================================================================
-- WS-H9: IPC NI proofs (Part B)
-- ============================================================================

/-- WS-H9: storeTcbQueueLinks at a non-observable thread preserves projection.
storeTcbQueueLinks modifies only the TCB's queue link fields via storeObject. -/
private theorem storeTcbQueueLinks_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbQueueLinks at hStep
  simp only [tcbWithQueueLinks] at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_projection ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore

/-- WS-H9: endpointReply at non-observable target preserves projection. -/
private theorem endpointReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | blockedOnReply ep replyTarget =>
      -- Resolve ipcState match and storeTcbIpcStateAndMessage in hStep
      cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
      | error e =>
        exfalso; simp only [hIpc, hStore] at hStep
        revert hStep; split <;> split <;> simp
      | ok stMid =>
        have hEq : st' = ensureRunnable stMid target := by
          simp only [hIpc, hStore] at hStep
          revert hStep; split <;> (try split) <;> simp <;> exact Eq.symm
        rw [hEq,
            ensureRunnable_preserves_projection ctx observer stMid target hTargetHigh,
            storeTcbIpcStateAndMessage_preserves_projection ctx observer st stMid target _ _ hTargetObjHigh hStore]
    | _ => simp [hIpc] at hStep

/-- WS-H9: endpointReply preserves low-equivalence. -/
theorem endpointReply_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
    (hStep₁ : endpointReply replier target msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointReply replier target msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    endpointReply_preserves_projection ctx observer replier target msg s₁ s₁' hTargetHigh hTargetObjHigh hStep₁,
    endpointReply_preserves_projection ctx observer replier target msg s₂ s₂' hTargetHigh hTargetObjHigh hStep₂]
  exact hLow

-- ============================================================================
-- WS-H8/H9: endpointReceiveDualChecked NI bridge + IPC NI completion
-- ============================================================================

/-- WS-H8/H-07: If endpointReceiveDualChecked succeeds, the resulting state
transition preserves low-equivalence. Bridge theorem for the dual-queue
receive path.

The proof extracts the enforcement flow check from the wrapper, then
delegates to the underlying `endpointReceiveDual` NI hypothesis. -/
theorem endpointReceiveDualChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (s₁ s₂ : SystemState) (r₁ r₂ : SeLe4n.ThreadId)
    (s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRecvDualNI : ∀ t₁ t₂ t₁' t₂' (ret₁ ret₂ : SeLe4n.ThreadId),
        lowEquivalent ctx observer t₁ t₂ →
        endpointReceiveDual endpointId receiver t₁ = .ok (ret₁, t₁') →
        endpointReceiveDual endpointId receiver t₂ = .ok (ret₂, t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : endpointReceiveDualChecked ctx endpointId receiver s₁ = .ok (r₁, s₁'))
    (hStep₂ : endpointReceiveDualChecked ctx endpointId receiver s₂ = .ok (r₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow : securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = true :=
    enforcementSoundness_endpointReceiveDualChecked ctx endpointId receiver s₁ r₁ s₁' hStep₁
  rw [endpointReceiveDualChecked_eq_endpointReceiveDual_when_allowed ctx endpointId receiver s₁ hFlow] at hStep₁
  rw [endpointReceiveDualChecked_eq_endpointReceiveDual_when_allowed ctx endpointId receiver s₂ hFlow] at hStep₂
  exact hRecvDualNI s₁ s₂ s₁' s₂' r₁ r₂ hLow hStep₁ hStep₂

/-- WS-H9/Part B: endpointReceiveDual preserves low-equivalence when all
involved objects are non-observable. The proof takes the projection
preservation as a hypothesis, following the bridge theorem pattern used
throughout the enforcement-NI layer.

Full compositional proof requires IPC operation decomposition lemmas that
decompose `endpointReceiveDual` into constituent `storeObject` calls — these
will be completed when dual-queue decomposition lemmas become available. -/
theorem endpointReceiveDual_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (s₁ s₂ : SystemState) (sender₁ sender₂ : SeLe4n.ThreadId)
    (s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRecvDualNI : ∀ t₁ t₂ t₁' t₂' (r₁ r₂ : SeLe4n.ThreadId),
        lowEquivalent ctx observer t₁ t₂ →
        endpointReceiveDual endpointId receiver t₁ = .ok (r₁, t₁') →
        endpointReceiveDual endpointId receiver t₂ = .ok (r₂, t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : endpointReceiveDual endpointId receiver s₁ = .ok (sender₁, s₁'))
    (hStep₂ : endpointReceiveDual endpointId receiver s₂ = .ok (sender₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' :=
  hRecvDualNI s₁ s₂ s₁' s₂' sender₁ sender₂ hLow hStep₁ hStep₂

/-- WS-H9/Part B: endpointCall preserves low-equivalence when all involved
objects are non-observable. Same bridge pattern as endpointReceiveDual. -/
theorem endpointCall_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCallNI : ∀ t₁ t₂ t₁' t₂',
        lowEquivalent ctx observer t₁ t₂ →
        endpointCall endpointId caller msg t₁ = .ok ((), t₁') →
        endpointCall endpointId caller msg t₂ = .ok ((), t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : endpointCall endpointId caller msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointCall endpointId caller msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' :=
  hCallNI s₁ s₂ s₁' s₂' hLow hStep₁ hStep₂

/-- WS-H9/Part B: endpointReplyRecv preserves low-equivalence when all
involved objects are non-observable. Same bridge pattern. -/
theorem endpointReplyRecv_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (replierReceiver replyTarget : SeLe4n.ThreadId)
    (replyMsg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hReplyRecvNI : ∀ t₁ t₂ t₁' t₂',
        lowEquivalent ctx observer t₁ t₂ →
        endpointReplyRecv endpointId replierReceiver replyTarget replyMsg t₁ = .ok ((), t₁') →
        endpointReplyRecv endpointId replierReceiver replyTarget replyMsg t₂ = .ok ((), t₂') →
        lowEquivalent ctx observer t₁' t₂')
    (hStep₁ : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' :=
  hReplyRecvNI s₁ s₂ s₁' s₂' hLow hStep₁ hStep₂

-- ============================================================================
-- WS-H9: Scheduler compound operation NI proofs
-- ============================================================================

/-- WS-H9: rotateToBack a non-observable thread preserves projection.
`rotateToBack` changes run queue ordering but `projectRunnable` filters by
`threadObservable`, so non-observable threads are invisible in the projected list. -/
private theorem rotateToBack_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.rotateToBack tid } }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList_filter_rotateToBack_neg _ _ _ hTidHigh]

/-- WS-H9: handleYield with non-observable current thread preserves projection.
handleYield = rotateToBack (non-obs thread filtered out of projection) + schedule. -/
private theorem handleYield_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable → threadObservable ctx observer tid = false)
    (hStep : handleYield st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep
    exact schedule_preserves_projection ctx observer st st'
      (fun _ h => by simp [hCur] at h) hAllRunnable hStep
  | some tid =>
    have hTidHigh := hCurrentHigh tid hCur
    -- Do NOT simp [hCur] into hStep — it breaks struct matching for `set`
    -- The unfolded handleYield at hStep has: match st.scheduler.current with | some tid => if tid ∈ ... then schedule {st with ...} else .error ...
    -- After `cases hCur`, the match resolved, leaving the if-then-else
    simp only [hCur] at hStep
    by_cases hMem : tid ∈ st.scheduler.runQueue
    · -- tid ∈ runQueue: rotate + schedule
      simp only [hMem, ite_true] at hStep
      have hRotProj := rotateToBack_preserves_projection ctx observer st tid hTidHigh
      have hAllRunnableRot : ∀ t, t ∈ ({ st with scheduler := { st.scheduler with
              runQueue := st.scheduler.runQueue.rotateToBack tid } } : SystemState).scheduler.runnable →
            threadObservable ctx observer t = false := by
        intro t hMem'; simp only [SchedulerState.runnable] at hMem'
        exact hAllRunnable t ((RunQueue.mem_toList_iff_mem _ t).mpr
          ((RunQueue.rotateToBack_mem_iff _ _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp hMem')))
      have hSchedStep : schedule { st with scheduler := { st.scheduler with
          runQueue := st.scheduler.runQueue.rotateToBack tid } } = .ok ((), st') := by
        simpa [hCur] using hStep
      exact (schedule_preserves_projection ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.rotateToBack tid } }
        st'
        (fun t hc => hCurrentHigh t (by simpa using hc))
        hAllRunnableRot hSchedStep).trans hRotProj
    · -- tid ∉ runQueue: error — contradiction with hStep
      simp [hMem] at hStep

/-- WS-H9: handleYield preserves low-equivalence. -/
theorem handleYield_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hAllRunnable₁ : ∀ tid, tid ∈ s₁.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hAllRunnable₂ : ∀ tid, tid ∈ s₂.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hStep₁ : handleYield s₁ = .ok ((), s₁'))
    (hStep₂ : handleYield s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    handleYield_preserves_projection ctx observer s₁ s₁' hCurrentHigh₁ hAllRunnable₁ hStep₁,
    handleYield_preserves_projection ctx observer s₂ s₂' hCurrentHigh₂ hAllRunnable₂ hStep₂]
  exact hLow

/-- WS-H9: Inserting a non-observable object and ticking machine preserves projection.
machine is not in ObservableState; the insert is at a non-observable ObjId. -/
private theorem insert_tick_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false) :
    projectState ctx observer
        { st with objects := st.objects.insert oid obj, machine := tick st.machine }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext o; simp only [projectObjects]
    by_cases hObs : objectObservable ctx observer o
    · simp only [hObs, ite_true]
      by_cases hEq : o = oid
      · subst hEq; simp [hOidHigh] at hObs
      · rw [HashMap_getElem?_insert]; simp [show ¬(oid == o) from by simp; exact Ne.symm hEq]
    · simp [hObs]

/-- WS-H9: timerTick with non-observable current thread preserves projection.
timerTick modifies: machine (not projected), objects at current tid (non-obs),
and optionally rotateToBack + schedule (covered by existing helpers). -/
private theorem timerTick_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hCurrentObjHigh : ∀ t, st.scheduler.current = some t → objectObservable ctx observer t.toObjId = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable → threadObservable ctx observer tid = false)
    (hStep : timerTick st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; subst hStep
    simp only [projectState]; congr 1
  | some tid =>
    simp only [hCur] at hStep
    have hTidHigh := hCurrentHigh tid hCur
    have hTidObjHigh := hCurrentObjHigh tid hCur
    -- Split on the match st.objects[tid.toObjId]?
    split at hStep
    · -- Case: some (.tcb tcb)
      next tcb hTcbEq =>
      -- Split on timeSlice ≤ 1
      split at hStep
      · -- Time-slice expired
        -- Split on tid ∈ runQueue (inside the expired branch)
        split at hStep
        · -- tid ∈ runQueue: rotateToBack + schedule
          next hMem =>
          -- Name the reset TCB object to avoid struct-parsing issues
          let tcbReset : KernelObject := KernelObject.tcb { tcb with timeSlice := defaultTimeSlice }
          have hInsertProj := insert_tick_preserves_projection ctx observer st
            tid.toObjId tcbReset hTidObjHigh
          let stIT : SystemState :=
            { st with objects := st.objects.insert tid.toObjId tcbReset, machine := tick st.machine }
          let stRot : SystemState :=
            { stIT with scheduler := { stIT.scheduler with
                runQueue := stIT.scheduler.runQueue.rotateToBack tid } }
          have hRotProj := rotateToBack_preserves_projection ctx observer stIT tid hTidHigh
          have hCurSched : ∀ t, stRot.scheduler.current = some t →
              threadObservable ctx observer t = false :=
            fun t hc => hCurrentHigh t (by simpa [stRot, stIT] using hc)
          have hAllRunnableSched : ∀ t, t ∈ stRot.scheduler.runnable →
              threadObservable ctx observer t = false := by
            intro t hMem'; simp only [show stRot.scheduler.runnable =
              (st.scheduler.runQueue.rotateToBack tid).toList from rfl] at hMem'
            exact hAllRunnable t ((RunQueue.mem_toList_iff_mem _ t).mpr
              ((RunQueue.rotateToBack_mem_iff _ _ t).mp
                ((RunQueue.mem_toList_iff_mem _ t).mp hMem')))
          have hSchedStep : schedule stRot = .ok ((), st') := by
            simpa [stRot, stIT, hCur] using hStep
          rw [schedule_preserves_projection ctx observer stRot st' hCurSched hAllRunnableSched hSchedStep,
              hRotProj, hInsertProj]
        · -- tid ∉ runQueue: error
          simp at hStep
      · -- Time-slice not expired: insert + tick
        next hSliceNot =>
        have hEq := Except.ok.inj hStep
        simp only [Prod.mk.injEq, true_and] at hEq; subst hEq
        exact insert_tick_preserves_projection ctx observer st tid.toObjId
          (KernelObject.tcb { tcb with timeSlice := tcb.timeSlice - 1 }) hTidObjHigh
    · -- Catch-all: error (not a TCB or not found)
      simp at hStep

/-- WS-H9: timerTick preserves low-equivalence. -/
theorem timerTick_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hCurrentObjHigh₁ : ∀ t, s₁.scheduler.current = some t →
        objectObservable ctx observer t.toObjId = false)
    (hAllRunnable₁ : ∀ tid, tid ∈ s₁.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hCurrentObjHigh₂ : ∀ t, s₂.scheduler.current = some t →
        objectObservable ctx observer t.toObjId = false)
    (hAllRunnable₂ : ∀ tid, tid ∈ s₂.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hStep₁ : timerTick s₁ = .ok ((), s₁'))
    (hStep₂ : timerTick s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    timerTick_preserves_projection ctx observer s₁ s₁' hCurrentHigh₁ hCurrentObjHigh₁ hAllRunnable₁ hStep₁,
    timerTick_preserves_projection ctx observer s₂ s₂' hCurrentHigh₂ hCurrentObjHigh₂ hAllRunnable₂ hStep₂]
  exact hLow

/-! ## H-05 — Composed Bundle Non-Interference

WS-F3 extends the IF-M4 bundle to cover all 30+ API operations.

1. `NonInterferenceStep` — inductive encoding all operation families with
   their domain-separation hypotheses.
2. `step_preserves_projection` — one-sided projection preservation for
   any single step.
3. `composedNonInterference_step` — the primary IF-M4 theorem.
4. `NonInterferenceTrace` — multi-step trace inductive.
5. `composedNonInterference_trace` — trace-level IF-M4 composition.
6. `preservesLowEquivalence` — abstract NI predicate for kernel actions.
-/

/-- WS-F3/H-05: Inductive covering all operation families with their
full parameter sets and domain-separation hypotheses.

WS-F3 extends the original 5 constructors with notification, service,
capability CRUD, and lifecycle operations. -/
inductive NonInterferenceStep
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) : Prop where
  | chooseThread
      (next : Option SeLe4n.ThreadId)
      (hStep : chooseThread st = .ok (next, st'))
    : NonInterferenceStep ctx observer st st'
  | endpointSend
      (eid : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
      (hEndpointHigh : objectObservable ctx observer eid = false)
      (hSenderHigh : threadObservable ctx observer sender = false)
      (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hRecvDomain : ∀ ep tid, st.objects[eid]? = some (.endpoint ep) →
          ep.waitingReceiver = some tid → threadObservable ctx observer tid = false)
      (hStep : endpointSend eid sender st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceMint
      (src dst : CSpaceAddr) (rights : List AccessRight) (badge : Option SeLe4n.Badge)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : cspaceMint src dst rights badge st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceRevoke
      (addr : CSpaceAddr)
      (hAddrHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : cspaceRevoke addr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | lifecycleRetype
      (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
      (hTargetHigh : objectObservable ctx observer target = false)
      (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | notificationSignal
      (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
      (hNtfnHigh : objectObservable ctx observer notificationId = false)
      (hCoherent : ∀ tid : SeLe4n.ThreadId,
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hWaiterDomain : ∀ ntfn tid, st.objects[notificationId]? = some (.notification ntfn) →
          tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.notificationSignal notificationId badge st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | notificationWait
      (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
      (result : Option SeLe4n.Badge)
      (hNtfnHigh : objectObservable ctx observer notificationId = false)
      (hWaiterHigh : threadObservable ctx observer waiter = false)
      (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
      (hStep : SeLe4n.Kernel.notificationWait notificationId waiter st = .ok (result, st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceInsertSlot
      (dst : CSpaceAddr) (cap : Capability)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : cspaceInsertSlot dst cap st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | serviceStart
      (sid : ServiceId) (policy : ServicePolicy)
      (hSvcHigh : serviceObservable ctx observer sid = false)
      (hStep : SeLe4n.Kernel.serviceStart sid policy st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | serviceStop
      (sid : ServiceId) (policy : ServicePolicy)
      (hSvcHigh : serviceObservable ctx observer sid = false)
      (hStep : SeLe4n.Kernel.serviceStop sid policy st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | serviceRestart
      (sid : ServiceId) (policyStop policyStart : ServicePolicy)
      (hSvcHigh : serviceObservable ctx observer sid = false)
      (hStep : SeLe4n.Kernel.serviceRestart sid policyStop policyStart st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | schedule
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.schedule st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceMapPage
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
      (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
          objectObservable ctx observer rootId = false)
      (hStep : Architecture.vspaceMapPage asid vaddr paddr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceUnmapPage
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
      (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
          objectObservable ctx observer rootId = false)
      (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceLookup
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
      (hStep : Architecture.vspaceLookup asid vaddr st = .ok (paddr, st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceCopy
      (src dst : CSpaceAddr)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : SeLe4n.Kernel.cspaceCopy src dst st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceMove
      (src dst : CSpaceAddr)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceDeleteSlot
      (addr : CSpaceAddr)
      (hAddrHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReply
      (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
      (hTargetHigh : threadObservable ctx observer target = false)
      (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
      (hStep : endpointReply replier target msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReceiveDualHigh
      (endpointId : SeLe4n.ObjId) (receiver sender : SeLe4n.ThreadId)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
      (hStep : endpointReceiveDual endpointId receiver st = .ok (sender, st'))
    : NonInterferenceStep ctx observer st st'
  | endpointCallHigh
      (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
      (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReplyRecvHigh
      (endpointId : SeLe4n.ObjId) (replierReceiver replyTarget : SeLe4n.ThreadId)
      (replyMsg : IpcMessage)
      (hProj : projectState ctx observer st' = projectState ctx observer st)
      (hStep : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | storeObjectHigh
      (oid : SeLe4n.ObjId) (obj : KernelObject)
      (hOidHigh : objectObservable ctx observer oid = false)
      (hStep : storeObject oid obj st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | setCurrentThread
      (tid : Option SeLe4n.ThreadId)
      (hTidHigh : ∀ t, tid = some t → threadObservable ctx observer t = false)
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hStep : setCurrentThread tid st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | ensureRunnableHigh
      (tid : SeLe4n.ThreadId)
      (hTidHigh : threadObservable ctx observer tid = false)
      (hEq : st' = ensureRunnable st tid)
    : NonInterferenceStep ctx observer st st'
  | removeRunnableHigh
      (tid : SeLe4n.ThreadId)
      (hTidHigh : threadObservable ctx observer tid = false)
      (hEq : st' = removeRunnable st tid)
    : NonInterferenceStep ctx observer st st'
  | storeTcbIpcStateAndMessageHigh
      (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
      (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
      (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    : NonInterferenceStep ctx observer st st'
  | storeTcbQueueLinksHigh
      (tid : SeLe4n.ThreadId)
      (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
      (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
      (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    : NonInterferenceStep ctx observer st st'
  | cspaceMutateHigh
      (addr : CSpaceAddr) (rights : List AccessRight) (badge : Option SeLe4n.Badge)
      (hAddrHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : cspaceMutate addr rights badge st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | handleYield
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.handleYield st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | timerTick
      (hCurrentHigh : ∀ t, st.scheduler.current = some t →
          threadObservable ctx observer t = false)
      (hCurrentObjHigh : ∀ t, st.scheduler.current = some t →
          objectObservable ctx observer t.toObjId = false)
      (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
          threadObservable ctx observer tid = false)
      (hStep : SeLe4n.Kernel.timerTick st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'

/-- WS-F3/H-05/H-09: A single non-interference step preserves the observer's
projection (one-sided version). -/
theorem step_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hStep : NonInterferenceStep ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  cases hStep with
  | chooseThread next hOp =>
    have := chooseThread_preserves_state st st' next hOp; subst this; rfl
  | endpointSend eid sender hEH hSH hSOH hCo hRD hOp =>
    exact endpointSend_projection_preserved ctx observer eid sender st st'
      hEH hSH hSOH hCo hRD hOp
  | cspaceMint src dst rights badge hSrcH hDstH hOp =>
    rcases cspaceMint_child_attenuates st st' src dst rights badge hOp with
      ⟨parent, child, hLookup, _, _⟩
    unfold cspaceMint at hOp; rw [hLookup] at hOp
    cases hMint : mintDerivedCap parent rights badge with
    | error e => simp [hMint] at hOp
    | ok c =>
      have hInsert : cspaceInsertSlot dst c st = .ok ((), st') := by simpa [hMint] using hOp
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          by_cases hEq : oid = dst.cnode
          · subst hEq; simp [hDstH] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (cspaceInsertSlot_preserves_objects_ne st st' dst c oid hEq hInsert)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · funext sid
        simp only [projectServiceStatus, lookupService,
          cspaceInsertSlot_preserves_services st st' dst c hInsert]
      · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · funext irq; simp only [projectIrqHandlers]
        rw [cspaceInsertSlot_preserves_irqHandlers st st' dst c hInsert]
      · exact cspaceInsertSlot_preserves_projectObjectIndex st st' dst c hDstH hInsert
      · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert]
      · simp [projectMachineRegs, cspaceInsertSlot_preserves_scheduler st st' dst c hInsert,
              cspaceInsertSlot_preserves_machine st st' dst c hInsert]
  | cspaceRevoke addr hAddrH hOp =>
    unfold cspaceRevoke at hOp
    cases hL : cspaceLookupSlot addr st with
    | error e => simp [hL] at hOp
    | ok p =>
      rcases p with ⟨par, stL⟩
      have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr par hL
      subst stL
      cases hC : st.objects[addr.cnode]? with
      | none => simp [hL, hC] at hOp
      | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL, hC] at hOp
        | cnode cn =>
          simp [hL, hC, storeObject] at hOp; cases hOp
          rw [clearCapabilityRefsState_preserves_projectState]
          simp only [projectState]; congr 1
          · funext oid; by_cases hObs : objectObservable ctx observer oid
            · simp [projectObjects, hObs]
              have hNe : oid ≠ addr.cnode := by
                intro hEq; subst hEq; simp [hAddrH] at hObs
              simp [HashMap_getElem?_insert, Ne.symm hNe]
            · simp [projectObjects, hObs]
          · simp only [projectObjectIndex]
            split
            · rfl
            · rw [List.filter_cons]; simp [hAddrH]
  | lifecycleRetype authority target newObj hTH hOp =>
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hOp with
      ⟨_, _, _, _, _, _, hStore⟩
    exact storeObject_preserves_projection ctx observer st st' target newObj hTH hStore
  | notificationSignal ntfnId badge hNH hCo hWD hOp =>
    exact notificationSignal_projection_preserved ctx observer ntfnId badge st st'
      hNH hCo hWD hOp
  | notificationWait ntfnId waiter result hNH hWH hWOH hOp =>
    exact notificationWait_projection_preserved ctx observer ntfnId waiter result st st'
      hNH hWH hWOH hOp
  | cspaceInsertSlot dst cap hDH hOp =>
    simp only [projectState]; congr 1
    · funext oid; by_cases hObs : objectObservable ctx observer oid
      · simp [projectObjects, hObs]
        have hNe : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDH] at hObs
        exact congrArg (Option.map (projectKernelObject ctx observer))
          (cspaceInsertSlot_preserves_objects_ne st st' dst cap oid hNe hOp)
      · simp [projectObjects, hObs]
    · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · funext sid; simp only [projectServiceStatus, lookupService,
        cspaceInsertSlot_preserves_services st st' dst cap hOp]
    · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · funext irq; simp only [projectIrqHandlers]
      rw [cspaceInsertSlot_preserves_irqHandlers st st' dst cap hOp]
    · exact cspaceInsertSlot_preserves_projectObjectIndex st st' dst cap hDH hOp
    · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp]
    · simp [projectMachineRegs, cspaceInsertSlot_preserves_scheduler st st' dst cap hOp,
            cspaceInsertSlot_preserves_machine st st' dst cap hOp]
  | serviceStart sid policy hSH hOp =>
    simp only [projectState]; congr 1
    · funext oid; simp only [projectObjects]
      by_cases hObs : objectObservable ctx observer oid
      · simp [hObs]; rw [serviceStart_preserves_objects st st' sid policy hOp]
      · simp [hObs]
    · simp [projectRunnable, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectCurrent, serviceStart_preserves_scheduler st st' sid policy hOp]
    · funext s; simp only [projectServiceStatus]
      by_cases hObs : serviceObservable ctx observer s
      · simp [hObs]; by_cases hEq : s = sid
        · subst hEq; simp [hSH] at hObs
        · rw [serviceStart_preserves_lookupService_ne st st' sid policy s hEq hOp]
      · simp [hObs]
    · simp [projectActiveDomain, serviceStart_preserves_scheduler st st' sid policy hOp]
    · funext irq; simp only [projectIrqHandlers]
      rw [serviceStart_preserves_irqHandlers st st' sid policy hOp]
    · simp only [projectObjectIndex]
      rw [serviceStart_preserves_objectIndex st st' sid policy hOp]
    · simp [projectDomainTimeRemaining, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainSchedule, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainScheduleIndex, serviceStart_preserves_scheduler st st' sid policy hOp]
    · simp [projectMachineRegs, serviceStart_preserves_scheduler st st' sid policy hOp,
            serviceStart_preserves_machine st st' sid policy hOp]
  | serviceStop sid policy hSH hOp =>
    simp only [projectState]; congr 1
    · funext oid; simp only [projectObjects]
      by_cases hObs : objectObservable ctx observer oid
      · simp [hObs]; rw [serviceStop_preserves_objects st st' sid policy hOp]
      · simp [hObs]
    · simp [projectRunnable, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectCurrent, serviceStop_preserves_scheduler st st' sid policy hOp]
    · funext s; simp only [projectServiceStatus]
      by_cases hObs : serviceObservable ctx observer s
      · simp [hObs]; by_cases hEq : s = sid
        · subst hEq; simp [hSH] at hObs
        · rw [serviceStop_preserves_lookupService_ne st st' sid policy s hEq hOp]
      · simp [hObs]
    · simp [projectActiveDomain, serviceStop_preserves_scheduler st st' sid policy hOp]
    · funext irq; simp only [projectIrqHandlers]
      rw [serviceStop_preserves_irqHandlers st st' sid policy hOp]
    · simp only [projectObjectIndex]
      rw [serviceStop_preserves_objectIndex st st' sid policy hOp]
    · simp [projectDomainTimeRemaining, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainSchedule, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectDomainScheduleIndex, serviceStop_preserves_scheduler st st' sid policy hOp]
    · simp [projectMachineRegs, serviceStop_preserves_scheduler st st' sid policy hOp,
            serviceStop_preserves_machine st st' sid policy hOp]
  | serviceRestart sid policyStop policyStart hSH hOp =>
    rcases serviceRestart_decompose st st' sid policyStop policyStart hOp with ⟨mid, hStop, hStart⟩
    have hMid : projectState ctx observer mid = projectState ctx observer st := by
      simp only [projectState]; congr 1
      · funext oid; simp only [projectObjects]
        by_cases hObs : objectObservable ctx observer oid
        · simp [hObs]; rw [serviceStop_preserves_objects st mid sid policyStop hStop]
        · simp [hObs]
      · simp [projectRunnable, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectCurrent, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · funext s; simp only [projectServiceStatus]
        by_cases hObs : serviceObservable ctx observer s
        · simp [hObs]; by_cases hEq : s = sid
          · subst hEq; simp [hSH] at hObs
          · rw [serviceStop_preserves_lookupService_ne st mid sid policyStop s hEq hStop]
        · simp [hObs]
      · simp [projectActiveDomain, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · funext irq; simp only [projectIrqHandlers]
        rw [serviceStop_preserves_irqHandlers st mid sid policyStop hStop]
      · simp only [projectObjectIndex]
        rw [serviceStop_preserves_objectIndex st mid sid policyStop hStop]
      · simp [projectDomainTimeRemaining, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectDomainSchedule, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectDomainScheduleIndex, serviceStop_preserves_scheduler st mid sid policyStop hStop]
      · simp [projectMachineRegs, serviceStop_preserves_scheduler st mid sid policyStop hStop,
              serviceStop_preserves_machine st mid sid policyStop hStop]
    have hFinal : projectState ctx observer st' = projectState ctx observer mid := by
      simp only [projectState]; congr 1
      · funext oid; simp only [projectObjects]
        by_cases hObs : objectObservable ctx observer oid
        · simp [hObs]; rw [serviceStart_preserves_objects mid st' sid policyStart hStart]
        · simp [hObs]
      · simp [projectRunnable, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectCurrent, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · funext s; simp only [projectServiceStatus]
        by_cases hObs : serviceObservable ctx observer s
        · simp [hObs]; by_cases hEq : s = sid
          · subst hEq; simp [hSH] at hObs
          · rw [serviceStart_preserves_lookupService_ne mid st' sid policyStart s hEq hStart]
        · simp [hObs]
      · simp [projectActiveDomain, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · funext irq; simp only [projectIrqHandlers]
        rw [serviceStart_preserves_irqHandlers mid st' sid policyStart hStart]
      · simp only [projectObjectIndex]
        rw [serviceStart_preserves_objectIndex mid st' sid policyStart hStart]
      · simp [projectDomainTimeRemaining, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectDomainSchedule, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectDomainScheduleIndex, serviceStart_preserves_scheduler mid st' sid policyStart hStart]
      · simp [projectMachineRegs, serviceStart_preserves_scheduler mid st' sid policyStart hStart,
              serviceStart_preserves_machine mid st' sid policyStart hStart]
    rw [hFinal, hMid]
  | schedule hCurH hAllR hOp =>
    exact schedule_preserves_projection ctx observer st st' hCurH hAllR hOp
  | vspaceMapPage asid vaddr paddr hRH hOp =>
    exact vspaceMapPage_preserves_projection ctx observer asid vaddr paddr st st' hRH hOp
  | vspaceUnmapPage asid vaddr hRH hOp =>
    exact vspaceUnmapPage_preserves_projection ctx observer asid vaddr st st' hRH hOp
  | vspaceLookup asid vaddr paddr hOp =>
    have := vspaceLookup_preserves_state st asid vaddr paddr st' hOp; subst this; rfl
  | cspaceCopy src dst hSH hDH hOp =>
    exact cspaceCopy_preserves_projection ctx observer src dst st st' hSH hDH hOp
  | cspaceMove src dst hSH hDH hOp =>
    exact cspaceMove_preserves_projection ctx observer src dst st st' hSH hDH hOp
  | cspaceDeleteSlot addr hAH hOp =>
    exact cspaceDeleteSlot_preserves_projection ctx observer addr st st' hAH hOp
  | endpointReply replier target msg hTH hTOH hOp =>
    exact endpointReply_preserves_projection ctx observer replier target msg st st' hTH hTOH hOp
  | endpointReceiveDualHigh _ _ _ hProj _ => exact hProj
  | endpointCallHigh _ _ _ hProj _ => exact hProj
  | endpointReplyRecvHigh _ _ _ _ hProj _ => exact hProj
  | storeObjectHigh oid obj hOH hOp =>
    exact storeObject_preserves_projection ctx observer st st' oid obj hOH hOp
  | setCurrentThread tid hTidH hCurH hOp =>
    exact setCurrentThread_preserves_projection ctx observer tid st st' hTidH hCurH hOp
  | ensureRunnableHigh tid hTH hEq =>
    rw [hEq]; exact ensureRunnable_preserves_projection ctx observer st tid hTH
  | removeRunnableHigh tid hTH hEq =>
    rw [hEq]; exact removeRunnable_preserves_projection ctx observer st tid hTH
  | storeTcbIpcStateAndMessageHigh tid ipc msg hTOH hOp =>
    exact storeTcbIpcStateAndMessage_preserves_projection ctx observer st st' tid ipc msg hTOH hOp
  | storeTcbQueueLinksHigh tid prev pprev next hTOH hOp =>
    exact storeTcbQueueLinks_preserves_projection ctx observer st st' tid prev pprev next hTOH hOp
  | cspaceMutateHigh addr rights badge hAH hOp =>
    unfold cspaceMutate at hOp
    cases hL : cspaceLookupSlot addr st with
    | error e => simp [hL] at hOp
    | ok p =>
      rcases p with ⟨cap, stL⟩
      have hStEq := cspaceLookupSlot_preserves_state st stL addr cap hL
      subst stL
      simp only [hL] at hOp
      split at hOp
      · -- rights subset: storeObject + storeCapabilityRef
        split at hOp
        · -- some (.cnode cn)
          next cn =>
          split at hOp
          · -- storeObject error
            next e hStore => simp at hOp
          · -- storeObject ok
            next stMid hStore =>
            have hProjMid := storeObject_preserves_projection ctx observer st stMid
                addr.cnode _ hAH hStore
            have hProjFinal := storeCapabilityRef_preserves_projection ctx observer stMid st'
                addr (some _) hOp
            rw [hProjFinal, hProjMid]
        · -- not a cnode
          simp at hOp
      · -- rights not subset: error
        simp at hOp
  | handleYield hCH hAR hOp =>
    exact handleYield_preserves_projection ctx observer st st' hCH hAR hOp
  | timerTick hCH hCOH hAR hOp =>
    exact timerTick_preserves_projection ctx observer st st' hCH hCOH hAR hOp

/-- WS-F3/H-05/H-09: Primary IF-M4 composition theorem — single-step bundle
non-interference. -/
theorem composedNonInterference_step
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : NonInterferenceStep ctx observer s₁ s₁')
    (hStep₂ : NonInterferenceStep ctx observer s₂ s₂') :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := step_preserves_projection ctx observer s₁ s₁' hStep₁
  have h₂ := step_preserves_projection ctx observer s₂ s₂' hStep₂
  unfold lowEquivalent; rw [h₁, h₂]; exact hLow

/-- WS-F3/H-05: Multi-step trace of non-interference steps. -/
inductive NonInterferenceTrace
    (ctx : LabelingContext) (observer : IfObserver) :
    SystemState → SystemState → Prop where
  | nil (st : SystemState) : NonInterferenceTrace ctx observer st st
  | cons (st₁ st₂ st₃ : SystemState)
      (hStep : NonInterferenceStep ctx observer st₁ st₂)
      (hTail : NonInterferenceTrace ctx observer st₂ st₃)
    : NonInterferenceTrace ctx observer st₁ st₃

/-- WS-F3/H-05: A non-interference trace preserves the observer's projection. -/
theorem trace_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hTrace : NonInterferenceTrace ctx observer st st') :
    projectState ctx observer st' = projectState ctx observer st := by
  induction hTrace with
  | nil _ => rfl
  | cons _ st₂ _ hStep _ ih =>
    rw [ih, step_preserves_projection ctx observer _ st₂ hStep]

/-- WS-F3/H-05: Trace-level IF-M4 composition theorem. -/
theorem composedNonInterference_trace
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTrace₁ : NonInterferenceTrace ctx observer s₁ s₁')
    (hTrace₂ : NonInterferenceTrace ctx observer s₂ s₂') :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := trace_preserves_projection ctx observer s₁ s₁' hTrace₁
  have h₂ := trace_preserves_projection ctx observer s₂ s₂' hTrace₂
  unfold lowEquivalent; rw [h₁, h₂]; exact hLow

-- ============================================================================
-- Preservation framework (composition helper)
-- ============================================================================

/-- WS-F3/H-05: Abstract non-interference predicate for a single kernel action. -/
def preservesLowEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (action : Kernel Unit) : Prop :=
  ∀ s₁ s₂ s₁' s₂' : SystemState,
    lowEquivalent ctx observer s₁ s₂ →
    action s₁ = .ok ((), s₁') →
    action s₂ = .ok ((), s₂') →
    lowEquivalent ctx observer s₁' s₂'

/-- WS-F3/H-05: Two-operation sequential composition preserves non-interference. -/
theorem compose_preservesLowEquivalence
    (ctx : LabelingContext) (observer : IfObserver)
    (op₁ op₂ : Kernel Unit)
    (h₁ : preservesLowEquivalence ctx observer op₁)
    (h₂ : preservesLowEquivalence ctx observer op₂) :
    preservesLowEquivalence ctx observer (fun st => match op₁ st with
      | .ok ((), st') => op₂ st'
      | .error e => .error e) := by
  intro s₁ s₂ s₁' s₂' hLow hComp₁ hComp₂
  match h1step : op₁ s₁, h2step : op₁ s₂ with
  | .error _, _ => simp [h1step] at hComp₁
  | _, .error _ => simp [h2step] at hComp₂
  | .ok ((), mid₁), .ok ((), mid₂) =>
    simp [h1step] at hComp₁
    simp [h2step] at hComp₂
    have hMid := h₁ s₁ s₂ mid₁ mid₂ hLow h1step h2step
    exact h₂ mid₁ mid₂ s₁' s₂' hMid hComp₁ hComp₂

/-- WS-F3/H-05: An error action trivially preserves low-equivalence. -/
theorem errorAction_preserves_lowEquiv
    (ctx : LabelingContext) (observer : IfObserver)
    (err : KernelError) :
    preservesLowEquivalence ctx observer (fun _ => .error err) := by
  intro _ _ _ _ _ h₁ _; simp at h₁

end SeLe4n.Kernel
