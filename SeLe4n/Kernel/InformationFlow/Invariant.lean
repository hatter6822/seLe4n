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
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc', hDom', hIrq', hIdx', hDTR, hDS, hDSI]

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
  simp only [projectState, hObj, hRun, hCur, hSvc, hDom, hIrq, hIdx, hDTR, hDS, hDSI]

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
          unfold projectState
          congr 1
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

/-- WS-H9: storeTcbIpcStateAndMessage at a non-observable TCB preserves projection.
    Mirrors storeTcbIpcState_preserves_projection — a single storeObject at tid.toObjId. -/
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
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
      exact storeObject_preserves_projection ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore

/-- WS-H9: storeTcbPendingMessage at a non-observable TCB preserves projection. -/
private theorem storeTcbPendingMessage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
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
      simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
      exact storeObject_preserves_projection ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore

/-- WS-H9: storeTcbQueueLinks at a non-observable TCB preserves projection. -/
private theorem storeTcbQueueLinks_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
      exact storeObject_preserves_projection ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore

/-- WS-H9: endpointQueuePopHead preserves projection when endpoint and all
    reachable queue member TCBs are non-observable.

    The preconditions target the specific entities modified by the pop:
    (1) the endpoint itself, (2) the popped head TCB, and (3) any next TCB
    in the intrusive chain. -/
private theorem endpointQueuePopHead_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hTidHigh : objectObservable ctx observer tid.toObjId = false)
    (hNextHigh : ∀ tcb nextTid, st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid → objectObservable ctx observer nextTid.toObjId = false)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      -- Match on queue head
      cases isReceiveQ with
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hStep
        cases hHead : ep.sendQ.head with
        | none => simp [hHead] at hStep
        | some headTid =>
          simp only [hHead] at hStep
          cases hLookup : lookupTcb st headTid with
          | none => simp [hLookup] at hStep
          | some headTcb =>
            simp only [hLookup] at hStep
            split at hStep
            · simp at hStep
            · rename_i st1 hStore1
              cases hQNext : headTcb.queueNext with
              | none =>
                simp only [hQNext] at hStep
                cases hClear : storeTcbQueueLinks st1 headTid none none none with
                | error e => simp [hClear] at hStep
                | ok st3 =>
                  simp only [hClear, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨hTidEq, hStEq⟩ := hStep; subst hTidEq; subst hStEq
                  rw [storeTcbQueueLinks_preserves_projection ctx observer st1 st3
                        headTid none none none hTidHigh hClear,
                      storeObject_preserves_projection ctx observer st st1
                        endpointId _ hEndpointHigh hStore1]
              | some nextTid =>
                simp only [hQNext] at hStep
                cases hLookupNext : lookupTcb st1 nextTid with
                | none => simp [hLookupNext] at hStep
                | some nextTcb =>
                  simp only [hLookupNext] at hStep
                  cases hSetNext : storeTcbQueueLinks st1 nextTid none (some .endpointHead) nextTcb.queueNext with
                  | error e => simp [hSetNext] at hStep
                  | ok st2 =>
                    simp only [hSetNext] at hStep
                    cases hClear : storeTcbQueueLinks st2 headTid none none none with
                    | error e => simp [hClear] at hStep
                    | ok st3 =>
                      simp only [hClear, Except.ok.injEq, Prod.mk.injEq] at hStep
                      obtain ⟨hTidEq, hStEq⟩ := hStep; subst hTidEq; subst hStEq
                      have hNextObjHigh : objectObservable ctx observer nextTid.toObjId = false :=
                        hNextHigh headTcb nextTid
                          (lookupTcb_some_objects st headTid headTcb hLookup) hQNext
                      rw [storeTcbQueueLinks_preserves_projection ctx observer st2 st3
                            headTid none none none hTidHigh hClear,
                          storeTcbQueueLinks_preserves_projection ctx observer st1 st2
                            nextTid none (some .endpointHead) nextTcb.queueNext hNextObjHigh hSetNext,
                          storeObject_preserves_projection ctx observer st st1
                            endpointId _ hEndpointHigh hStore1]
      | true =>
        simp only [ite_true] at hStep
        cases hHead : ep.receiveQ.head with
        | none => simp [hHead] at hStep
        | some headTid =>
          simp only [hHead] at hStep
          cases hLookup : lookupTcb st headTid with
          | none => simp [hLookup] at hStep
          | some headTcb =>
            simp only [hLookup] at hStep
            split at hStep
            · simp at hStep
            · rename_i st1 hStore1
              cases hQNext : headTcb.queueNext with
              | none =>
                simp only [hQNext] at hStep
                cases hClear : storeTcbQueueLinks st1 headTid none none none with
                | error e => simp [hClear] at hStep
                | ok st3 =>
                  simp only [hClear, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨hTidEq, hStEq⟩ := hStep; subst hTidEq; subst hStEq
                  rw [storeTcbQueueLinks_preserves_projection ctx observer st1 st3
                        headTid none none none hTidHigh hClear,
                      storeObject_preserves_projection ctx observer st st1
                        endpointId _ hEndpointHigh hStore1]
              | some nextTid =>
                simp only [hQNext] at hStep
                cases hLookupNext : lookupTcb st1 nextTid with
                | none => simp [hLookupNext] at hStep
                | some nextTcb =>
                  simp only [hLookupNext] at hStep
                  cases hSetNext : storeTcbQueueLinks st1 nextTid none (some .endpointHead) nextTcb.queueNext with
                  | error e => simp [hSetNext] at hStep
                  | ok st2 =>
                    simp only [hSetNext] at hStep
                    cases hClear : storeTcbQueueLinks st2 headTid none none none with
                    | error e => simp [hClear] at hStep
                    | ok st3 =>
                      simp only [hClear, Except.ok.injEq, Prod.mk.injEq] at hStep
                      obtain ⟨hTidEq, hStEq⟩ := hStep; subst hTidEq; subst hStEq
                      have hNextObjHigh : objectObservable ctx observer nextTid.toObjId = false :=
                        hNextHigh headTcb nextTid
                          (lookupTcb_some_objects st headTid headTcb hLookup) hQNext
                      rw [storeTcbQueueLinks_preserves_projection ctx observer st2 st3
                            headTid none none none hTidHigh hClear,
                          storeTcbQueueLinks_preserves_projection ctx observer st1 st2
                            nextTid none (some .endpointHead) nextTcb.queueNext hNextObjHigh hSetNext,
                          storeObject_preserves_projection ctx observer st st1
                            endpointId _ hEndpointHigh hStore1]

/-- WS-H9: endpointQueueEnqueue preserves projection when endpoint and
    enqueued TCB and tail TCB are non-observable. -/
private theorem endpointQueueEnqueue_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
        (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        by_cases hIpc : tcb.ipcState = ThreadIpcState.ready
        · -- Ready: ≠ condition is false → else branch
          rw [if_neg (fun h : tcb.ipcState ≠ ThreadIpcState.ready => h hIpc)] at hStep
          cases hLinks : (tcb.queuePPrev.isSome || tcb.queuePrev.isSome || tcb.queueNext.isSome) with
          | true => simp [hLinks] at hStep
          | false =>
            simp only [hLinks] at hStep
            cases isReceiveQ with
            | false =>
              simp only [Bool.false_eq_true, ite_false] at hStep
              cases hTail : ep.sendQ.tail with
              | none =>
                simp only [hTail] at hStep
                split at hStep
                · simp at hStep
                · rename_i st1 hStore
                  rw [storeTcbQueueLinks_preserves_projection ctx observer st1 st'
                        tid none (some .endpointHead) none hTidObjHigh hStep,
                      storeObject_preserves_projection ctx observer st st1
                        endpointId _ hEndpointHigh hStore]
              | some tailTid =>
                simp only [hTail] at hStep
                have hTailObjHigh : objectObservable ctx observer tailTid.toObjId = false :=
                  hTailHigh ep tailTid hObj (by simp only [Bool.false_eq_true, ite_false]; exact hTail)
                cases hLookupTail : lookupTcb st tailTid with
                | none => simp [hLookupTail] at hStep
                | some tailTcb =>
                  simp only [hLookupTail] at hStep
                  split at hStep
                  · simp at hStep
                  · rename_i st1 hStore
                    cases hSetTail : storeTcbQueueLinks st1 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                    | error e => simp [hSetTail] at hStep
                    | ok st2 =>
                      simp only [hSetTail] at hStep
                      rw [storeTcbQueueLinks_preserves_projection ctx observer st2 st'
                            tid (some tailTid) (some (.tcbNext tailTid)) none hTidObjHigh hStep,
                          storeTcbQueueLinks_preserves_projection ctx observer st1 st2
                            tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid)
                            hTailObjHigh hSetTail,
                          storeObject_preserves_projection ctx observer st st1
                            endpointId _ hEndpointHigh hStore]
            | true =>
              simp only [ite_true] at hStep
              cases hTail : ep.receiveQ.tail with
              | none =>
                simp only [hTail] at hStep
                split at hStep
                · simp at hStep
                · rename_i _hDec
                  split at hStep
                  · simp at hStep
                  · rename_i st1 hStore
                    rw [storeTcbQueueLinks_preserves_projection ctx observer st1 st'
                          tid none (some .endpointHead) none hTidObjHigh hStep,
                        storeObject_preserves_projection ctx observer st st1
                          endpointId _ hEndpointHigh hStore]
              | some tailTid =>
                simp only [hTail] at hStep
                have hTailObjHigh : objectObservable ctx observer tailTid.toObjId = false :=
                  hTailHigh ep tailTid hObj (by simp only [ite_true]; exact hTail)
                cases hLookupTail : lookupTcb st tailTid with
                | none => simp [hLookupTail] at hStep
                | some tailTcb =>
                  simp only [hLookupTail] at hStep
                  split at hStep
                  · simp at hStep
                  · rename_i _hDec
                    split at hStep
                    · simp at hStep
                    · rename_i st1 hStore
                      cases hSetTail : storeTcbQueueLinks st1 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                      | error e => simp [hSetTail] at hStep
                      | ok st2 =>
                        simp only [hSetTail] at hStep
                        rw [storeTcbQueueLinks_preserves_projection ctx observer st2 st'
                              tid (some tailTid) (some (.tcbNext tailTid)) none hTidObjHigh hStep,
                            storeTcbQueueLinks_preserves_projection ctx observer st1 st2
                              tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid)
                              hTailObjHigh hSetTail,
                            storeObject_preserves_projection ctx observer st st1
                              endpointId _ hEndpointHigh hStore]
        · -- Not ready: ≠ condition is true → error
          rw [if_pos hIpc] at hStep
          simp at hStep

/-- WS-H9: endpointAwaitReceive at non-observable entities preserves projection. -/
private theorem endpointAwaitReceive_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hS : ep.state with
      | send | receive => simp [hS] at hStep
      | idle =>
        simp only [hS] at hStep
        cases hQ : ep.queue with
        | cons _ _ => simp [hQ] at hStep
        | nil =>
          cases hWR : ep.waitingReceiver with
          | some _ => simp [hQ, hWR] at hStep
          | none =>
            simp [hQ, hWR] at hStep; revert hStep
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hTcb : storeTcbIpcState pair.2 receiver _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                rw [removeRunnable_preserves_projection ctx observer st2 receiver hReceiverHigh,
                    storeTcbIpcState_preserves_projection ctx observer pair.2 st2 receiver _
                      hReceiverObjHigh hTcb,
                    storeObject_preserves_projection ctx observer st pair.2
                      endpointId _ hEndpointHigh hStore]

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

-- ============================================================================
-- WS-H9: cspaceDeleteSlot non-interference
-- ============================================================================

/-- WS-H9: cspaceDeleteSlot at a non-observable CNode preserves projection. -/
private theorem cspaceDeleteSlot_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr)
    (st st' : SystemState)
    (hCNodeHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceDeleteSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep; revert hStep
      cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hRef : storeCapabilityRef addr none pair.2 with
        | error e => simp
        | ok pair2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          -- detachSlotFromCdt only modifies CDT metadata (not in ObservableState)
          have hDetach : projectState ctx observer (SystemState.detachSlotFromCdt pair2.2 addr) =
              projectState ctx observer pair2.2 := by
            unfold SystemState.detachSlotFromCdt; split <;> rfl
          rw [hDetach]
          -- storeCapabilityRef preserves objects, scheduler, irqHandlers, objectIndex
          have hRefObj : pair2.2.objectIndex = pair.2.objectIndex :=
            storeCapabilityRef_preserves_objectIndex pair.2 pair2.2 addr none hRef
          simp only [projectState]; congr 1
          · -- objects: storeObject at non-observable CNode
            funext oid; by_cases hObs : objectObservable ctx observer oid
            · simp [projectObjects, hObs]
              have hNe : oid ≠ addr.cnode := by intro hEq; subst hEq; simp [hCNodeHigh] at hObs
              rw [storeCapabilityRef_preserves_objects pair.2 pair2.2 addr none hRef,
                  storeObject_objects_ne st pair.2 addr.cnode oid _ hNe hStore]
            · simp [projectObjects, hObs]
          · -- runnable
            simp [projectRunnable,
              storeObject_scheduler_eq st pair.2 addr.cnode _ hStore,
              storeCapabilityRef_preserves_scheduler pair.2 pair2.2 addr none hRef]
          · -- current
            simp [projectCurrent,
              storeObject_scheduler_eq st pair.2 addr.cnode _ hStore,
              storeCapabilityRef_preserves_scheduler pair.2 pair2.2 addr none hRef]
          · -- services
            funext sid; simp [projectServiceStatus, lookupService,
              storeCapabilityRef_preserves_services pair.2 pair2.2 addr none hRef,
              storeObject_preserves_services st pair.2 addr.cnode _ hStore]
          · -- activeDomain
            simp [projectActiveDomain,
              storeObject_scheduler_eq st pair.2 addr.cnode _ hStore,
              storeCapabilityRef_preserves_scheduler pair.2 pair2.2 addr none hRef]
          · -- irqHandlers
            funext irq; simp only [projectIrqHandlers]
            rw [storeCapabilityRef_preserves_irqHandlers pair.2 pair2.2 addr none hRef,
                storeObject_irqHandlers_eq st pair.2 addr.cnode _ hStore]
          · -- objectIndex
            simp only [projectObjectIndex, hRefObj]
            exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 addr.cnode _ hCNodeHigh hStore
          · simp [projectDomainTimeRemaining,
              storeObject_scheduler_eq st pair.2 addr.cnode _ hStore,
              storeCapabilityRef_preserves_scheduler pair.2 pair2.2 addr none hRef]
          · simp [projectDomainSchedule,
              storeObject_scheduler_eq st pair.2 addr.cnode _ hStore,
              storeCapabilityRef_preserves_scheduler pair.2 pair2.2 addr none hRef]
          · simp [projectDomainScheduleIndex,
              storeObject_scheduler_eq st pair.2 addr.cnode _ hStore,
              storeCapabilityRef_preserves_scheduler pair.2 pair2.2 addr none hRef]

/-- WS-H9: cspaceDeleteSlot at a non-observable CNode preserves low-equivalence. -/
theorem cspaceDeleteSlot_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCNodeHigh : objectObservable ctx observer addr.cnode = false)
    (hStep₁ : cspaceDeleteSlot addr s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceDeleteSlot addr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact cspaceDeleteSlot_projection_preserved ctx observer addr s₂ s₂' hCNodeHigh hStep₂
  exact cspaceDeleteSlot_projection_preserved ctx observer addr s₁ s₁' hCNodeHigh hStep₁

-- ============================================================================
-- WS-H9: cspaceCopy non-interference
-- ============================================================================

/-- WS-H9: cspaceCopy at non-observable CNodes preserves projection. -/
private theorem cspaceCopy_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (st st' : SystemState)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceCopy at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    rcases pair with ⟨cap, stL⟩
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL src cap hLookup
    subst stL
    simp only [hLookup] at hStep
    cases hInsert : cspaceInsertSlot dst cap st with
    | error e => simp [hInsert] at hStep
    | ok pair2 =>
      simp only [hInsert] at hStep
      cases hStep
      -- After cspaceInsertSlot: only dst.cnode changes in objects, scheduler unchanged
      -- Then ensureCdtNodeForSlot and addEdge only modify CDT (not in ObservableState)
      have hSched := cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert
      have hSvc := cspaceInsertSlot_preserves_services st pair2.2 dst cap hInsert
      -- CDT operations only modify cdt/cdtSlotNode/cdtNodeSlot (not objects, scheduler, etc.)
      simp only [projectState]; congr 1
      · -- objects
        funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs]
          have hNeDst : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
          exact congrArg (Option.map (projectKernelObject ctx observer))
            (cspaceInsertSlot_preserves_objects_ne st pair2.2 dst cap oid hNeDst hInsert)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, hSched]
      · simp [projectCurrent, hSched]
      · funext sid; simp only [projectServiceStatus, lookupService, hSvc]
      · simp [projectActiveDomain, hSched]
      · funext irq; simp only [projectIrqHandlers,
          cspaceInsertSlot_preserves_irqHandlers st pair2.2 dst cap hInsert]
      · exact cspaceInsertSlot_preserves_projectObjectIndex st pair2.2 dst cap hDstHigh hInsert
      · simp [projectDomainTimeRemaining, hSched]
      · simp [projectDomainSchedule, hSched]
      · simp [projectDomainScheduleIndex, hSched]

/-- WS-H9: cspaceCopy at non-observable CNodes preserves low-equivalence. -/
theorem cspaceCopy_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceCopy src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceCopy src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact cspaceCopy_projection_preserved ctx observer src dst s₂ s₂' hSrcHigh hDstHigh hStep₂
  exact cspaceCopy_projection_preserved ctx observer src dst s₁ s₁' hSrcHigh hDstHigh hStep₁

-- ============================================================================
-- WS-H9: cspaceMove non-interference
-- ============================================================================

/-- WS-H9: cspaceMove at non-observable CNodes preserves projection. -/
private theorem cspaceMove_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (st st' : SystemState)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceMove at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    rcases pair with ⟨cap, stL⟩
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL src cap hLookup
    subst stL
    simp only [hLookup] at hStep
    cases hInsert : cspaceInsertSlot dst cap st with
    | error e => simp [hInsert] at hStep
    | ok pair2 =>
      simp only [hInsert] at hStep
      -- After insert, delete src
      cases hDelete : cspaceDeleteSlot src pair2.2 with
      | error e => simp [hDelete] at hStep
      | ok pair3 =>
        simp only [hDelete] at hStep
        -- CDT node-stable fixup (attachSlotToCdtNode) only modifies CDT
        cases hStep
        -- Compose: insert preserves projection, then delete preserves projection
        -- CDT operations don't affect ObservableState
        have hInsertProj := cspaceInsertSlot_preserves_projectObjectIndex st pair2.2 dst cap hDstHigh hInsert
        rw [show projectState ctx observer st' = projectState ctx observer pair3.2 from by
          simp only [projectState]; split <;> rfl,
          cspaceDeleteSlot_projection_preserved ctx observer src pair2.2 pair3.2 hSrcHigh hDelete]
        simp only [projectState]; congr 1
        · funext oid; by_cases hObs : objectObservable ctx observer oid
          · simp [projectObjects, hObs]
            have hNeDst : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
            exact congrArg (Option.map (projectKernelObject ctx observer))
              (cspaceInsertSlot_preserves_objects_ne st pair2.2 dst cap oid hNeDst hInsert)
          · simp [projectObjects, hObs]
        · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert]
        · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert]
        · funext sid; simp only [projectServiceStatus, lookupService,
            cspaceInsertSlot_preserves_services st pair2.2 dst cap hInsert]
        · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert]
        · funext irq; simp only [projectIrqHandlers,
            cspaceInsertSlot_preserves_irqHandlers st pair2.2 dst cap hInsert]
        · exact hInsertProj
        · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert]
        · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert]
        · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st pair2.2 dst cap hInsert]

/-- WS-H9: cspaceMove at non-observable CNodes preserves low-equivalence. -/
theorem cspaceMove_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep₁ : cspaceMove src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMove src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact cspaceMove_projection_preserved ctx observer src dst s₂ s₂' hSrcHigh hDstHigh hStep₂
  exact cspaceMove_projection_preserved ctx observer src dst s₁ s₁' hSrcHigh hDstHigh hStep₁

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
-- WS-H9/Part A: Scheduler NI proofs
-- ============================================================================

/-- WS-H9: schedule at non-observable current threads preserves projection.
    `schedule` only modifies `scheduler.current` (via setCurrentThread). If both
    the old and new current threads are non-observable, projectCurrent is `none`
    before and after, and all other projection fields are unchanged. -/
private theorem schedule_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hOldCurrent : ∀ tid, st.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent : ∀ tid, st'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hStep : schedule st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  -- schedule = chooseThread then setCurrentThread
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pair =>
    rcases pair with ⟨next, stC⟩
    have hStC : stC = st := chooseThread_preserves_state st stC next hChoose
    subst stC
    simp only [hChoose] at hStep
    -- setCurrentThread only changes scheduler.current
    cases next with
    | none =>
      simp [setCurrentThread] at hStep; cases hStep
      simp only [projectState]; congr 1
      · -- projectCurrent: old was non-obs (→ none), new is none
        simp only [projectCurrent]
        cases hC : st.scheduler.current with
        | none => rfl
        | some tid => simp [hOldCurrent tid hC]
    | some tid =>
      simp only [] at hStep
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
          simp [hObj] at hStep
        | tcb tcb =>
          simp [hObj] at hStep
          by_cases hGuard : (tid ∈ st.scheduler.runQueue ∧ tcb.domain = st.scheduler.activeDomain)
          · rw [if_pos hGuard] at hStep
            simp [setCurrentThread] at hStep; cases hStep
            simp only [projectState]; congr 1
            · simp only [projectCurrent]
              cases hC : st.scheduler.current with
              | none => simp [hNewCurrent tid rfl]
              | some oldTid => simp [hOldCurrent oldTid hC, hNewCurrent tid rfl]
          · rw [if_neg hGuard] at hStep; simp at hStep

/-- WS-H9: schedule preserves low-equivalence when all involved threads are
    non-observable. -/
theorem schedule_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hOldCurrent₁ : ∀ tid, s₁.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hOldCurrent₂ : ∀ tid, s₂.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent₁ : ∀ tid, s₁'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent₂ : ∀ tid, s₂'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hStep₁ : schedule s₁ = .ok ((), s₁'))
    (hStep₂ : schedule s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact schedule_projection_preserved ctx observer s₂ s₂' hOldCurrent₂ hNewCurrent₂ hStep₂
  exact schedule_projection_preserved ctx observer s₁ s₁' hOldCurrent₁ hNewCurrent₁ hStep₁

/-- WS-H9: handleYield at a non-observable current thread preserves projection.
    handleYield optionally rotates the runQueue then calls schedule. The rotation
    moves a non-observable thread, which is invisible after filtering. -/
private theorem handleYield_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hOldCurrent : ∀ tid, st.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent : ∀ tid, st'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hStep : handleYield st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- No current thread: same as schedule
    simp [hCur] at hStep
    exact schedule_projection_preserved ctx observer st st' hOldCurrent hNewCurrent hStep
  | some tid =>
    simp only [hCur] at hStep
    have hTidHigh := hOldCurrent tid hCur
    by_cases hMem : (tid ∈ st.scheduler.runQueue)
    · -- member: rotate and schedule
      rw [if_pos hMem] at hStep
      -- st_rotated = { st with scheduler.runQueue := rotateToBack ... }
      let stR := { st with scheduler := { st.scheduler with
          runQueue := st.scheduler.runQueue.rotateToBack tid } }
      -- schedule stR = .ok ((), st')
      have hSchedStep : schedule stR = .ok ((), st') := hStep
      -- Show: projectState of stR = projectState of st
      have hRotProj : projectState ctx observer stR = projectState ctx observer st := by
        simp only [projectState]; congr 1
        · -- projectRunnable: rotation of non-obs thread is invisible
          simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList]
          exact RunQueue.toList_filter_rotateToBack_neg st.scheduler.runQueue tid
            (threadObservable ctx observer) hTidHigh
        · -- projectCurrent: same current
          rfl
      -- Show: projectState of st' = projectState of stR
      have hOldCurR : ∀ t, stR.scheduler.current = some t →
          threadObservable ctx observer t = false := by
        intro t ht; simp at ht; exact hOldCurrent t (by rw [hCur]; exact ht)
      have hFinal := schedule_projection_preserved ctx observer stR st'
        hOldCurR hNewCurrent hSchedStep
      rw [hFinal, hRotProj]
    · -- not member: false branch
      rw [if_neg hMem] at hStep; simp at hStep

/-- WS-H9: handleYield preserves low-equivalence. -/
theorem handleYield_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hOldCurrent₁ : ∀ tid, s₁.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hOldCurrent₂ : ∀ tid, s₂.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent₁ : ∀ tid, s₁'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent₂ : ∀ tid, s₂'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hStep₁ : handleYield s₁ = .ok ((), s₁'))
    (hStep₂ : handleYield s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact handleYield_projection_preserved ctx observer s₂ s₂' hOldCurrent₂ hNewCurrent₂ hStep₂
  exact handleYield_projection_preserved ctx observer s₁ s₁' hOldCurrent₁ hNewCurrent₁ hStep₁

/-- WS-H9: switchDomain preserves low-equivalence.
    switchDomain is deterministic from scheduler timing fields (all visible in projection).
    Two low-equivalent states produce identical post-switch projections. -/
theorem switchDomain_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : switchDomain s₁ = .ok ((), s₁'))
    (hStep₂ : switchDomain s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Extract scheduler timing fields from low-equivalence
  have hDSEq : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule :=
    congrArg ObservableState.domainSchedule hLow
  have hDSIEq : s₁.scheduler.domainScheduleIndex = s₂.scheduler.domainScheduleIndex :=
    congrArg ObservableState.domainScheduleIndex hLow
  -- Unfold switchDomain
  unfold switchDomain at hStep₁ hStep₂
  -- Case split on schedule emptiness
  cases hSched₁ : s₁.scheduler.domainSchedule with
  | nil =>
    rw [hSched₁] at hStep₁; simp at hStep₁; cases hStep₁
    rw [← hDSEq] at hStep₂; simp at hStep₂; cases hStep₂
    exact hLow
  | cons head tail =>
    rw [hSched₁] at hStep₁
    rw [← hDSEq] at hStep₂
    simp only [] at hStep₁ hStep₂
    -- nextIdx is the same for both (same domainScheduleIndex and same schedule length)
    let nextIdx := (s₁.scheduler.domainScheduleIndex + 1) % (head :: tail).length
    have hIdxEq : (s₁.scheduler.domainScheduleIndex + 1) % (head :: tail).length =
        (s₂.scheduler.domainScheduleIndex + 1) % (head :: tail).length := by
      rw [hDSIEq]
    cases hEntry₁ : (head :: tail)[nextIdx]? with
    | none =>
      simp [hEntry₁] at hStep₁; cases hStep₁
      rw [show (head :: tail)[(s₂.scheduler.domainScheduleIndex + 1) % (head :: tail).length]? =
          none from by rw [← hIdxEq]; exact hEntry₁] at hStep₂
      simp at hStep₂; cases hStep₂
      exact hLow
    | some entry =>
      simp only [hEntry₁] at hStep₁; cases hStep₁
      rw [show (head :: tail)[(s₂.scheduler.domainScheduleIndex + 1) % (head :: tail).length]? =
          some entry from by rw [← hIdxEq]; exact hEntry₁] at hStep₂
      simp only [] at hStep₂; cases hStep₂
      -- Both states now have the same scheduler timing fields and current = none
      unfold lowEquivalent projectState; congr 1
      · -- objects: unchanged by switchDomain
        exact congrArg ObservableState.objects hLow
      · -- runnable: unchanged by switchDomain
        exact congrArg ObservableState.runnable hLow
      · -- current: both become none → projectCurrent = none
        simp [projectCurrent]
      · -- services: unchanged
        exact congrArg ObservableState.services hLow
      · -- activeDomain: same entry.domain
        simp [projectActiveDomain]
      · -- irqHandlers: unchanged
        exact congrArg ObservableState.irqHandlers hLow
      · -- objectIndex: unchanged
        exact congrArg ObservableState.objectIndex hLow
      · -- domainTimeRemaining: same entry.length
        simp [projectDomainTimeRemaining]
      · -- domainSchedule: unchanged
        simpa [projectDomainSchedule] using hDSEq
      · -- domainScheduleIndex: same nextIdx
        simp [projectDomainScheduleIndex, hIdxEq]

/-- WS-H9: timerTick at a non-observable current thread preserves projection.
    timerTick modifies the current TCB's timeSlice and machine state (neither
    in ObservableState when non-observable). On expiry, it rotates and reschedules. -/
private theorem timerTick_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hOldCurrent : ∀ tid, st.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hOldCurrentObj : ∀ tid, st.scheduler.current = some tid →
        objectObservable ctx observer tid.toObjId = false)
    (hNewCurrent : ∀ tid, st'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hStep : timerTick st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- No current thread: only machine changes
    simp [hCur] at hStep; cases hStep
    simp only [projectState]; congr 1
  | some tid =>
    simp only [hCur] at hStep
    have hTidHigh := hOldCurrent tid hCur
    have hTidObjHigh := hOldCurrentObj tid hCur
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ =>
        simp [hObj] at hStep
      | tcb tcb =>
        simp [hObj] at hStep
        by_cases hExpire : (tcb.timeSlice ≤ 1)
        · -- Expired: reset TCB, rotate, schedule
          simp [hExpire] at hStep
          -- st_updated = { st with objects := insert tid TCB', machine := tick }
          let stU := { st with
            objects := st.objects.insert tid.toObjId (.tcb { tcb with timeSlice := defaultTimeSlice })
            machine := tick st.machine }
          by_cases hMem : (tid ∈ stU.scheduler.runQueue)
          · rw [if_pos hMem] at hStep
            -- stR = { stU with scheduler.runQueue := rotateToBack ... }
            -- then schedule stR = .ok ((), st')
            have hStUProj : projectState ctx observer stU = projectState ctx observer st := by
              simp only [projectState]; congr 1
              · funext oid; by_cases hObs : objectObservable ctx observer oid
                · simp [projectObjects, hObs]
                  have hNe : oid ≠ tid.toObjId := by
                    intro hEq; subst hEq; simp [hTidObjHigh] at hObs
                  simp [HashMap_getElem?_insert, Ne.symm hNe]
                · simp [projectObjects, hObs]
              · simp only [projectObjectIndex]
                split <;> (try rfl) <;> rw [List.filter_cons] <;> simp [hTidObjHigh]
            let stR := { stU with scheduler := { stU.scheduler with
                runQueue := stU.scheduler.runQueue.rotateToBack tid } }
            have hRotProj : projectState ctx observer stR = projectState ctx observer stU := by
              simp only [projectState]; congr 1
              · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList]
                exact RunQueue.toList_filter_rotateToBack_neg stU.scheduler.runQueue tid
                  (threadObservable ctx observer) hTidHigh
            have hOldCurR : ∀ t, stR.scheduler.current = some t →
                threadObservable ctx observer t = false := by
              intro t ht; simp at ht; exact hOldCurrent t (by rw [hCur]; exact ht)
            have hFinal := schedule_projection_preserved ctx observer stR st'
              hOldCurR hNewCurrent hStep
            rw [hFinal, hRotProj, hStUProj]
          · rw [if_neg hMem] at hStep; simp at hStep
        · -- Not expired: update TCB timeSlice + machine tick
          rw [if_neg hExpire] at hStep
          simp [show ¬(tcb.timeSlice ≤ 1) from hExpire] at hStep; cases hStep
          simp only [projectState]; congr 1
          · -- objects: insert at non-observable tid.toObjId
            funext oid; by_cases hObs : objectObservable ctx observer oid
            · simp [projectObjects, hObs]
              have hNe : oid ≠ tid.toObjId := by
                intro hEq; subst hEq; simp [hTidObjHigh] at hObs
              simp [HashMap_getElem?_insert, Ne.symm hNe]
            · simp [projectObjects, hObs]
          · -- objectIndex: tid.toObjId already in index, non-observable → filtered out
            simp only [projectObjectIndex]
            split <;> (try rfl) <;> rw [List.filter_cons] <;> simp [hTidObjHigh]

/-- WS-H9: timerTick preserves low-equivalence. -/
theorem timerTick_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hOldCurrent₁ : ∀ tid, s₁.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hOldCurrent₂ : ∀ tid, s₂.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hOldCurrentObj₁ : ∀ tid, s₁.scheduler.current = some tid →
        objectObservable ctx observer tid.toObjId = false)
    (hOldCurrentObj₂ : ∀ tid, s₂.scheduler.current = some tid →
        objectObservable ctx observer tid.toObjId = false)
    (hNewCurrent₁ : ∀ tid, s₁'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hNewCurrent₂ : ∀ tid, s₂'.scheduler.current = some tid →
        threadObservable ctx observer tid = false)
    (hStep₁ : timerTick s₁ = .ok ((), s₁'))
    (hStep₂ : timerTick s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact timerTick_projection_preserved ctx observer s₂ s₂' hOldCurrent₂ hOldCurrentObj₂ hNewCurrent₂ hStep₂
  exact timerTick_projection_preserved ctx observer s₁ s₁' hOldCurrent₁ hOldCurrentObj₁ hNewCurrent₁ hStep₁

-- ============================================================================
-- WS-H9/Part B: IPC NI completion
-- ============================================================================

/-- WS-H9: endpointReceiveDual at non-observable entities preserves projection.
    Preconditions: endpoint non-observable, receiver non-observable, all sendQ head
    TCBs and their queue-next links are non-observable. -/
theorem endpointReceiveDual_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hSendQHeadHigh : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some tid → threadObservable ctx observer tid = false)
    (hQueueNextHigh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hRecvQTailHigh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (result, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hSendHead : ep.sendQ.head with
      | some senderTid =>
        -- Sender available: pop from sendQ, transfer message
        simp only [hSendHead] at hStep; revert hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp
        | ok pair =>
          rcases pair with ⟨poppedTid, stPop⟩
          simp only []
          -- poppedTid is from sendQ head → non-observable
          have hPoppedHigh := hSendQHeadHigh ep poppedTid hObj
          -- Need to show poppedTid = head of sendQ
          -- endpointQueuePopHead returns the head of the queue
          have hPoppedObjHigh : objectObservable ctx observer poppedTid.toObjId = false := by
            -- endpointQueuePopHead pops sendQ.head; result tid = sendQ.head
            unfold endpointQueuePopHead at hPop; simp [hObj, hSendHead] at hPop
            cases hLookup : lookupTcb st senderTid with
            | none => simp [hLookup] at hPop
            | some headTcb =>
              simp [hLookup] at hPop
              cases hStore1 : storeObject endpointId _ st with
              | error e => simp [hStore1] at hPop
              | ok p1 =>
                simp [hStore1] at hPop
                cases hQN : headTcb.queueNext with
                | none =>
                  simp [hQN] at hPop
                  cases hC : storeTcbQueueLinks p1.2 senderTid none none none with
                  | error e => simp [hC] at hPop
                  | ok s3 =>
                    simp at hPop; obtain ⟨hEq, _⟩ := hPop; subst hEq
                    exact hCoherent senderTid (hSendQHeadHigh ep senderTid hObj hSendHead)
                | some nextTid =>
                  simp [hQN] at hPop
                  cases hLN : lookupTcb p1.2 nextTid with
                  | none => simp [hLN] at hPop
                  | some nextTcb =>
                    simp [hLN] at hPop
                    cases hSN : storeTcbQueueLinks p1.2 nextTid none (some .endpointHead) nextTcb.queueNext with
                    | error e => simp [hSN] at hPop
                    | ok s2 =>
                      simp [hSN] at hPop
                      cases hC : storeTcbQueueLinks s2 senderTid none none none with
                      | error e => simp [hC] at hPop
                      | ok s3 =>
                        simp at hPop; obtain ⟨hEq, _⟩ := hPop; subst hEq
                        exact hCoherent senderTid (hSendQHeadHigh ep senderTid hObj hSendHead)
          -- Build hNextHigh for endpointQueuePopHead_preserves_projection
          have hPopNextHigh : ∀ tcb nextTid, st.objects[poppedTid.toObjId]? = some (.tcb tcb) →
              tcb.queueNext = some nextTid →
              objectObservable ctx observer nextTid.toObjId = false :=
            fun tcb nextTid hTcbObj hQN =>
              hQueueNextHigh poppedTid tcb nextTid hTcbObj hQN hPoppedObjHigh
          have hPopProj := endpointQueuePopHead_preserves_projection ctx observer
            endpointId false st stPop poppedTid hEndpointHigh hPoppedObjHigh hPopNextHigh hPop
          -- Now handle the post-pop operations
          -- lookupTcb is read-only, senderWasCall is determined, then:
          -- storeTcbIpcStateAndMessage + ensureRunnable/storeTcbPendingMessage
          intro hRest
          rw [show projectState ctx observer st' = projectState ctx observer stPop from by
            -- All post-pop operations are at non-observable entities
            -- This requires case-splitting on senderWasCall, but all paths
            -- compose storeTcbIpcStateAndMessage, ensureRunnable, storeTcbPendingMessage
            -- at poppedTid (non-obs) and receiver (non-obs)
            revert hRest
            -- senderWasCall depends on lookupTcb stPop poppedTid
            cases hLookupPost : lookupTcb stPop poppedTid with
            | none =>
              -- lookupTcb failed: senderWasCall = false, senderMsg = none
              simp [hLookupPost]
              cases hMsg : storeTcbIpcStateAndMessage stPop poppedTid .ready none with
              | error e => simp
              | ok st'' =>
                simp only []
                cases hPM : storeTcbPendingMessage (ensureRunnable st'' poppedTid) receiver none with
                | error e => simp
                | ok st4 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                  rw [storeTcbPendingMessage_preserves_projection ctx observer _ st4 receiver _ hReceiverObjHigh hPM,
                      ensureRunnable_preserves_projection ctx observer st'' poppedTid
                        (by have := hPoppedHigh (by exact hSendQHeadHigh ep poppedTid hObj hSendHead); exact this),
                      storeTcbIpcStateAndMessage_preserves_projection ctx observer stPop st'' poppedTid _ _ hPoppedObjHigh hMsg]
            | some tcb =>
              simp [hLookupPost]
              cases tcb.ipcState with
              | blockedOnCall _ =>
                -- senderWasCall = true
                simp only []
                cases hMsg : storeTcbIpcStateAndMessage stPop poppedTid (.blockedOnReply endpointId (some receiver)) none with
                | error e => simp
                | ok st'' =>
                  simp only []
                  cases hPM : storeTcbPendingMessage st'' receiver tcb.pendingMessage with
                  | error e => simp
                  | ok st''' =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                    rw [storeTcbPendingMessage_preserves_projection ctx observer st'' st''' receiver _ hReceiverObjHigh hPM,
                        storeTcbIpcStateAndMessage_preserves_projection ctx observer stPop st'' poppedTid _ _ hPoppedObjHigh hMsg]
              | _ =>
                -- senderWasCall = false (all other IPC states)
                simp only []
                cases hMsg : storeTcbIpcStateAndMessage stPop poppedTid .ready none with
                | error e => simp
                | ok st'' =>
                  simp only []
                  cases hPM : storeTcbPendingMessage (ensureRunnable st'' poppedTid) receiver tcb.pendingMessage with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                    rw [storeTcbPendingMessage_preserves_projection ctx observer _ st4 receiver _ hReceiverObjHigh hPM,
                        ensureRunnable_preserves_projection ctx observer st'' poppedTid
                          (by have := hSendQHeadHigh ep poppedTid hObj hSendHead; exact hPoppedHigh this),
                        storeTcbIpcStateAndMessage_preserves_projection ctx observer stPop st'' poppedTid _ _ hPoppedObjHigh hMsg],
            hPopProj]
      | none =>
        -- No sender: enqueue receiver in receiveQ, block
        simp only [hSendHead] at hStep; revert hStep
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp
        | ok stEnq =>
          simp only []
          cases hTcb : storeTcbIpcState stEnq receiver (.blockedOnReceive endpointId) with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_projection ctx observer st2 receiver hReceiverHigh,
                storeTcbIpcState_preserves_projection ctx observer stEnq st2 receiver _ hReceiverObjHigh hTcb,
                endpointQueueEnqueue_preserves_projection ctx observer endpointId true receiver st stEnq
                  hEndpointHigh hReceiverHigh hReceiverObjHigh
                  (fun ep' tailTid hEp hTail => hRecvQTailHigh ep' tailTid hEp hTail) hEnq]

/-- WS-H9: endpointReceiveDual preserves low-equivalence. -/
theorem endpointReceiveDual_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (result₁ result₂ : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hSendQHeadHigh₁ : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
        s₁.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some tid → threadObservable ctx observer tid = false)
    (hSendQHeadHigh₂ : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
        s₂.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some tid → threadObservable ctx observer tid = false)
    (hQueueNextHigh₁ : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        s₁.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hQueueNextHigh₂ : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        s₂.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hRecvQTailHigh₁ : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        s₁.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hRecvQTailHigh₂ : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        s₂.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hStep₁ : endpointReceiveDual endpointId receiver s₁ = .ok (result₁, s₁'))
    (hStep₂ : endpointReceiveDual endpointId receiver s₂ = .ok (result₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact endpointReceiveDual_projection_preserved ctx observer endpointId receiver result₂ s₂ s₂'
      hEndpointHigh hReceiverHigh hReceiverObjHigh hCoherent hSendQHeadHigh₂ hQueueNextHigh₂
      hRecvQTailHigh₂ hStep₂
  exact endpointReceiveDual_projection_preserved ctx observer endpointId receiver result₁ s₁ s₁'
    hEndpointHigh hReceiverHigh hReceiverObjHigh hCoherent hSendQHeadHigh₁ hQueueNextHigh₁
    hRecvQTailHigh₁ hStep₁

/-- WS-H9: endpointReply at non-observable entities preserves projection. -/
private theorem endpointReply_projection_preserved
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
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp [hIpc] at hStep
      -- Check authorization
      cases hAuth : (match replyTarget with
        | some expected => replier == expected
        | none => true) with
      | false => simp at hStep
      | true =>
        simp at hStep; revert hStep
        cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
        | error e => simp
        | ok stMid =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          rw [ensureRunnable_preserves_projection ctx observer stMid target hTargetHigh]
          -- storeTcbIpcStateAndMessage = storeTcbIpcState + storeMessage
          -- Both modify TCB at target.toObjId (non-observable)
          exact storeTcbIpcStateAndMessage_preserves_projection ctx observer
            st stMid target .ready (some msg) hTargetObjHigh hStore

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
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact endpointReply_projection_preserved ctx observer replier target msg s₂ s₂'
      hTargetHigh hTargetObjHigh hStep₂
  exact endpointReply_projection_preserved ctx observer replier target msg s₁ s₁'
    hTargetHigh hTargetObjHigh hStep₁

/-- WS-H9: endpointCall at non-observable entities preserves projection. -/
theorem endpointCall_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvQHeadHigh : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some tid → threadObservable ctx observer tid = false)
    (hQueueNextHigh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hSendQTailHigh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointCall at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hRecvHead : ep.receiveQ.head with
      | none =>
        -- No receiver: enqueue caller with blockedOnCall
        simp only [hRecvHead] at hStep; revert hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp
        | ok stEnq =>
          simp only []
          cases hTcb : storeTcbIpcStateAndMessage stEnq caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp
          | ok stMid =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_projection ctx observer stMid caller hCallerHigh,
                storeTcbIpcStateAndMessage_preserves_projection ctx observer stEnq stMid
                  caller _ _ hCallerObjHigh hTcb,
                endpointQueueEnqueue_preserves_projection ctx observer endpointId false caller
                  st stEnq hEndpointHigh hCallerHigh hCallerObjHigh
                  (fun ep' tailTid hEp hTail => hSendQTailHigh ep' tailTid hEp hTail) hEnq]
      | some _ =>
        -- Receiver available: pop from receiveQ, transfer, block caller
        simp only [hRecvHead] at hStep; revert hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp
        | ok pair =>
          rcases pair with ⟨receiverTid, stPop⟩
          simp only []
          -- receiverTid is from receiveQ head → non-observable
          have hRecvTidObjHigh : objectObservable ctx observer receiverTid.toObjId = false := by
            -- endpointQueuePopHead returns receiveQ.head; derive non-obs from hRecvQHeadHigh
            unfold endpointQueuePopHead at hPop; simp [hObj, hRecvHead] at hPop
            cases hLookup : lookupTcb st _ with
            | none => simp [hLookup] at hPop
            | some headTcb =>
              simp [hLookup] at hPop
              cases hStore1 : storeObject endpointId _ st with
              | error e => simp [hStore1] at hPop
              | ok p1 =>
                simp [hStore1] at hPop
                cases hQN : headTcb.queueNext with
                | none =>
                  simp [hQN] at hPop
                  cases hC : storeTcbQueueLinks p1.2 _ none none none with
                  | error e => simp [hC] at hPop
                  | ok s3 => simp at hPop; obtain ⟨hEq, _⟩ := hPop; subst hEq
                             exact hCoherent _ (hRecvQHeadHigh ep _ hObj hRecvHead)
                | some nextTid =>
                  simp [hQN] at hPop
                  cases hLN : lookupTcb p1.2 nextTid with
                  | none => simp [hLN] at hPop
                  | some nextTcb =>
                    simp [hLN] at hPop
                    cases hSN : storeTcbQueueLinks p1.2 nextTid none (some .endpointHead) nextTcb.queueNext with
                    | error e => simp [hSN] at hPop
                    | ok s2 =>
                      simp [hSN] at hPop
                      cases hC : storeTcbQueueLinks s2 _ none none none with
                      | error e => simp [hC] at hPop
                      | ok s3 => simp at hPop; obtain ⟨hEq, _⟩ := hPop; subst hEq
                                 exact hCoherent _ (hRecvQHeadHigh ep _ hObj hRecvHead)
          have hRecvTidHigh : threadObservable ctx observer receiverTid = false := by
            -- Same derivation from receiveQ head
            unfold endpointQueuePopHead at hPop; simp [hObj, hRecvHead] at hPop
            cases hLookup : lookupTcb st _ with
            | none => simp [hLookup] at hPop
            | some headTcb =>
              simp [hLookup] at hPop
              cases hStore1 : storeObject endpointId _ st with
              | error e => simp [hStore1] at hPop
              | ok p1 =>
                simp [hStore1] at hPop
                cases hQN : headTcb.queueNext with
                | none =>
                  simp [hQN] at hPop
                  cases hC : storeTcbQueueLinks p1.2 _ none none none with
                  | error e => simp [hC] at hPop
                  | ok s3 => simp at hPop; obtain ⟨hEq, _⟩ := hPop; subst hEq
                             exact hRecvQHeadHigh ep _ hObj hRecvHead
                | some nextTid =>
                  simp [hQN] at hPop
                  cases hLN : lookupTcb p1.2 nextTid with
                  | none => simp [hLN] at hPop
                  | some nextTcb =>
                    simp [hLN] at hPop
                    cases hSN : storeTcbQueueLinks p1.2 nextTid none (some .endpointHead) nextTcb.queueNext with
                    | error e => simp [hSN] at hPop
                    | ok s2 =>
                      simp [hSN] at hPop
                      cases hC : storeTcbQueueLinks s2 _ none none none with
                      | error e => simp [hC] at hPop
                      | ok s3 => obtain ⟨hEq, _⟩ := hPop; subst hEq
                                 exact hRecvQHeadHigh ep _ hObj hRecvHead
          have hPopNextHigh : ∀ tcb nextTid, st.objects[receiverTid.toObjId]? = some (.tcb tcb) →
              tcb.queueNext = some nextTid →
              objectObservable ctx observer nextTid.toObjId = false :=
            fun tcb nextTid hTcbObj hQN =>
              hQueueNextHigh receiverTid tcb nextTid hTcbObj hQN hRecvTidObjHigh
          have hPopProj := endpointQueuePopHead_preserves_projection ctx observer
            endpointId true st stPop receiverTid hEndpointHigh hRecvTidObjHigh hPopNextHigh hPop
          -- Post-pop: storeTcbIpcStateAndMessage + ensureRunnable + storeTcbIpcState + removeRunnable
          intro hRest
          rw [show projectState ctx observer st' = projectState ctx observer stPop from by
            revert hRest
            cases hMsgStore : storeTcbIpcStateAndMessage stPop receiverTid .ready (some msg) with
            | error e => simp
            | ok stMsg =>
              simp only []
              cases hTcbIpc : storeTcbIpcState (ensureRunnable stMsg receiverTid) caller (.blockedOnReply endpointId (some receiverTid)) with
              | error e => simp
              | ok st4 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                rw [removeRunnable_preserves_projection ctx observer st4 caller hCallerHigh,
                    storeTcbIpcState_preserves_projection ctx observer _ st4 caller _ hCallerObjHigh hTcbIpc,
                    ensureRunnable_preserves_projection ctx observer stMsg receiverTid hRecvTidHigh,
                    storeTcbIpcStateAndMessage_preserves_projection ctx observer stPop stMsg receiverTid _ _ hRecvTidObjHigh hMsgStore],
            hPopProj]

/-- WS-H9: endpointCall preserves low-equivalence. -/
theorem endpointCall_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvQHeadHigh₁ : ∀ ep tid, s₁.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some tid → threadObservable ctx observer tid = false)
    (hRecvQHeadHigh₂ : ∀ ep tid, s₂.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some tid → threadObservable ctx observer tid = false)
    (hQueueNextHigh₁ : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        s₁.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hQueueNextHigh₂ : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        s₂.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hSendQTailHigh₁ : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        s₁.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hSendQTailHigh₂ : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        s₂.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hStep₁ : endpointCall endpointId caller msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointCall endpointId caller msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact endpointCall_projection_preserved ctx observer endpointId caller msg s₂ s₂'
      hEndpointHigh hCallerHigh hCallerObjHigh hCoherent hRecvQHeadHigh₂ hQueueNextHigh₂
      hSendQTailHigh₂ hStep₂
  exact endpointCall_projection_preserved ctx observer endpointId caller msg s₁ s₁'
    hEndpointHigh hCallerHigh hCallerObjHigh hCoherent hRecvQHeadHigh₁ hQueueNextHigh₁
    hSendQTailHigh₁ hStep₁

/-- WS-H9: endpointReplyRecv at non-observable entities preserves projection.
    Decomposes into storeTcbIpcStateAndMessage + ensureRunnable + endpointAwaitReceive. -/
private theorem endpointReplyRecv_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hTargetHigh : threadObservable ctx observer replyTarget = false)
    (hTargetObjHigh : objectObservable ctx observer replyTarget.toObjId = false)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReplyRecv at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnReply epId expectedReplier =>
      simp only [hIpc] at hStep
      cases hAuth : (match expectedReplier with
        | some expected => receiver == expected
        | none => true) with
      | false => simp at hStep
      | true =>
        simp at hStep; revert hStep
        cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
        | error e => simp
        | ok stMsg =>
          simp only []
          cases hAwait : endpointAwaitReceive endpointId receiver (ensureRunnable stMsg replyTarget) with
          | error e => simp
          | ok pair =>
            simp only [Except.ok.injEq]; intro hEq; rw [← hEq]
            rw [endpointAwaitReceive_preserves_projection ctx observer endpointId receiver _ pair.2
                  hEndpointHigh hReceiverHigh hReceiverObjHigh hAwait,
                ensureRunnable_preserves_projection ctx observer stMsg replyTarget hTargetHigh,
                storeTcbIpcStateAndMessage_preserves_projection ctx observer st stMsg
                  replyTarget _ _ hTargetObjHigh hStore]

/-- WS-H9: endpointReplyRecv preserves low-equivalence. -/
theorem endpointReplyRecv_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hTargetHigh : threadObservable ctx observer replyTarget = false)
    (hTargetObjHigh : objectObservable ctx observer replyTarget.toObjId = false)
    (hStep₁ : endpointReplyRecv endpointId receiver replyTarget msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointReplyRecv endpointId receiver replyTarget msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact endpointReplyRecv_projection_preserved ctx observer endpointId receiver replyTarget msg
      s₂ s₂' hEndpointHigh hReceiverHigh hReceiverObjHigh hTargetHigh hTargetObjHigh hStep₂
  exact endpointReplyRecv_projection_preserved ctx observer endpointId receiver replyTarget msg
    s₁ s₁' hEndpointHigh hReceiverHigh hReceiverObjHigh hTargetHigh hTargetObjHigh hStep₁

-- ============================================================================
-- WS-H9/Part D: VSpace NI
-- ============================================================================

/-- WS-H9: Architecture.vspaceMapPage at a non-observable VSpaceRoot preserves projection.
    vspaceMapPage delegates to storeObject on the resolved root ID. -/
private theorem vspaceMapPage_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ (rootId : SeLe4n.ObjId) (_root : VSpaceRoot), Architecture.resolveAsidRoot st asid = some (rootId, _root) →
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
      simp [hMap] at hStep
      have hRootIdHigh : objectObservable ctx observer rootId = false :=
        hRootHigh rootId root (by rw [hResolve])
      exact storeObject_preserves_projection ctx observer st st' rootId _ hRootIdHigh hStep

/-- WS-H9: Architecture.vspaceMapPage preserves low-equivalence. -/
theorem vspaceMapPage_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ (rootId : SeLe4n.ObjId) (_root : VSpaceRoot), Architecture.resolveAsidRoot s₁ asid = some (rootId, _root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ (rootId : SeLe4n.ObjId) (_root : VSpaceRoot), Architecture.resolveAsidRoot s₂ asid = some (rootId, _root) →
        objectObservable ctx observer rootId = false)
    (hStep₁ : Architecture.vspaceMapPage asid vaddr paddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceMapPage asid vaddr paddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact vspaceMapPage_projection_preserved ctx observer asid vaddr paddr s₂ s₂' hRootHigh₂ hStep₂
  exact vspaceMapPage_projection_preserved ctx observer asid vaddr paddr s₁ s₁' hRootHigh₁ hStep₁

/-- WS-H9: Architecture.vspaceUnmapPage at a non-observable VSpaceRoot preserves projection. -/
private theorem vspaceUnmapPage_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ (rootId : SeLe4n.ObjId) (_root : VSpaceRoot), Architecture.resolveAsidRoot st asid = some (rootId, _root) →
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
      simp [hUnmap] at hStep
      have hRootIdHigh : objectObservable ctx observer rootId = false :=
        hRootHigh rootId root (by rw [hResolve])
      exact storeObject_preserves_projection ctx observer st st' rootId _ hRootIdHigh hStep

/-- WS-H9: Architecture.vspaceUnmapPage preserves low-equivalence. -/
theorem vspaceUnmapPage_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ (rootId : SeLe4n.ObjId) (_root : VSpaceRoot), Architecture.resolveAsidRoot s₁ asid = some (rootId, _root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ (rootId : SeLe4n.ObjId) (_root : VSpaceRoot), Architecture.resolveAsidRoot s₂ asid = some (rootId, _root) →
        objectObservable ctx observer rootId = false)
    (hStep₁ : Architecture.vspaceUnmapPage asid vaddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceUnmapPage asid vaddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact vspaceUnmapPage_projection_preserved ctx observer asid vaddr s₂ s₂' hRootHigh₂ hStep₂
  exact vspaceUnmapPage_projection_preserved ctx observer asid vaddr s₁ s₁' hRootHigh₁ hStep₁

/-- WS-H9: Architecture.vspaceLookup is read-only — state unchanged, projection trivially preserved. -/
private theorem vspaceLookup_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (result : SeLe4n.PAddr) (st st' : SystemState)
    (hStep : Architecture.vspaceLookup asid vaddr st = .ok (result, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold Architecture.vspaceLookup at hStep
  cases hR : Architecture.resolveAsidRoot st asid with
  | none => simp [hR] at hStep
  | some pair =>
    simp [hR] at hStep
    cases hL : pair.2.lookup vaddr with
    | none => simp [hL] at hStep
    | some p => simp [hL] at hStep; cases hStep; rename_i h; cases h; rfl

/-- WS-H9: Architecture.vspaceLookup preserves low-equivalence trivially (read-only, no state change). -/
theorem vspaceLookup_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (r₁ r₂ : SeLe4n.PAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : Architecture.vspaceLookup asid vaddr s₁ = .ok (r₁, s₁'))
    (hStep₂ : Architecture.vspaceLookup asid vaddr s₂ = .ok (r₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact vspaceLookup_projection_preserved ctx observer asid vaddr r₂ s₂ s₂' hStep₂
  exact vspaceLookup_projection_preserved ctx observer asid vaddr r₁ s₁ s₁' hStep₁

/-- WS-H9: endpointSendDual at non-observable entities preserves projection.
    Mirrors endpointCall structure: match receiveQ.head → pop or enqueue. -/
private theorem endpointSendDual_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvQHeadHigh : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some tid → threadObservable ctx observer tid = false)
    (hQueueNextHigh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = some nextTid →
        objectObservable ctx observer tid.toObjId = false →
        objectObservable ctx observer nextTid.toObjId = false)
    (hSendQTailHigh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointSendDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hRecvHead : ep.receiveQ.head with
      | some _ =>
        -- Receiver available: pop from receiveQ, transfer, unblock
        simp only [hRecvHead] at hStep; revert hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp
        | ok pair =>
          rcases pair with ⟨receiverTid, stPop⟩
          simp only []
          -- receiverTid is from receiveQ head → non-observable
          have hRecvTidObjHigh : objectObservable ctx observer receiverTid.toObjId = false := by
            unfold endpointQueuePopHead at hPop; simp [hObj, hRecvHead] at hPop
            cases hLookup : lookupTcb st _ with
            | none => simp [hLookup] at hPop
            | some headTcb =>
              simp [hLookup] at hPop
              cases hStore1 : storeObject endpointId _ st with
              | error e => simp [hStore1] at hPop
              | ok p1 =>
                simp [hStore1] at hPop
                cases hQN : headTcb.queueNext with
                | none =>
                  simp [hQN] at hPop
                  cases hC : storeTcbQueueLinks p1.2 _ none none none with
                  | error e => simp [hC] at hPop
                  | ok s3 => obtain ⟨hEq, _⟩ := hPop; subst hEq
                             exact hCoherent _ (hRecvQHeadHigh ep _ hObj hRecvHead)
                | some nextTid =>
                  simp [hQN] at hPop
                  cases hLN : lookupTcb p1.2 nextTid with
                  | none => simp [hLN] at hPop
                  | some nextTcb =>
                    simp [hLN] at hPop
                    cases hSN : storeTcbQueueLinks p1.2 nextTid none (some .endpointHead) nextTcb.queueNext with
                    | error e => simp [hSN] at hPop
                    | ok s2 =>
                      simp [hSN] at hPop
                      cases hC : storeTcbQueueLinks s2 _ none none none with
                      | error e => simp [hC] at hPop
                      | ok s3 => obtain ⟨hEq, _⟩ := hPop; subst hEq
                                 exact hCoherent _ (hRecvQHeadHigh ep _ hObj hRecvHead)
          have hRecvTidHigh : threadObservable ctx observer receiverTid = false := by
            unfold endpointQueuePopHead at hPop; simp [hObj, hRecvHead] at hPop
            cases hLookup : lookupTcb st _ with
            | none => simp [hLookup] at hPop
            | some headTcb =>
              simp [hLookup] at hPop
              cases hStore1 : storeObject endpointId _ st with
              | error e => simp [hStore1] at hPop
              | ok p1 =>
                simp [hStore1] at hPop
                cases hQN : headTcb.queueNext with
                | none =>
                  simp [hQN] at hPop
                  cases hC : storeTcbQueueLinks p1.2 _ none none none with
                  | error e => simp [hC] at hPop
                  | ok s3 => obtain ⟨hEq, _⟩ := hPop; subst hEq
                             exact hRecvQHeadHigh ep _ hObj hRecvHead
                | some nextTid =>
                  simp [hQN] at hPop
                  cases hLN : lookupTcb p1.2 nextTid with
                  | none => simp [hLN] at hPop
                  | some nextTcb =>
                    simp [hLN] at hPop
                    cases hSN : storeTcbQueueLinks p1.2 nextTid none (some .endpointHead) nextTcb.queueNext with
                    | error e => simp [hSN] at hPop
                    | ok s2 =>
                      simp [hSN] at hPop
                      cases hC : storeTcbQueueLinks s2 _ none none none with
                      | error e => simp [hC] at hPop
                      | ok s3 => obtain ⟨hEq, _⟩ := hPop; subst hEq
                                 exact hRecvQHeadHigh ep _ hObj hRecvHead
          have hPopNextHigh : ∀ tcb nextTid, st.objects[receiverTid.toObjId]? = some (.tcb tcb) →
              tcb.queueNext = some nextTid →
              objectObservable ctx observer nextTid.toObjId = false :=
            fun tcb nextTid hTcbObj hQN =>
              hQueueNextHigh receiverTid tcb nextTid hTcbObj hQN hRecvTidObjHigh
          have hPopProj := endpointQueuePopHead_preserves_projection ctx observer
            endpointId true st stPop receiverTid hEndpointHigh hRecvTidObjHigh hPopNextHigh hPop
          intro hRest
          rw [show projectState ctx observer st' = projectState ctx observer stPop from by
            revert hRest
            cases hMsgStore : storeTcbIpcStateAndMessage stPop receiverTid .ready (some msg) with
            | error e => simp
            | ok stMsg =>
              simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
              rw [ensureRunnable_preserves_projection ctx observer stMsg receiverTid hRecvTidHigh,
                  storeTcbIpcStateAndMessage_preserves_projection ctx observer stPop stMsg
                    receiverTid _ _ hRecvTidObjHigh hMsgStore],
            hPopProj]
      | none =>
        -- No receiver: enqueue sender, block, remove from runnable
        simp only [hRecvHead] at hStep; revert hStep
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp
        | ok stEnq =>
          simp only []
          cases hTcb : storeTcbIpcStateAndMessage stEnq sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp
          | ok stMid =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            rw [removeRunnable_preserves_projection ctx observer stMid sender hSenderHigh,
                storeTcbIpcStateAndMessage_preserves_projection ctx observer stEnq stMid
                  sender _ _ hSenderObjHigh hTcb,
                endpointQueueEnqueue_preserves_projection ctx observer endpointId false sender
                  st stEnq hEndpointHigh hSenderHigh hSenderObjHigh
                  (fun ep' tailTid hEp hTail => hSendQTailHigh ep' tailTid hEp hTail) hEnq]

-- ============================================================================
-- WS-H9/Part E: Observable-state NI
-- ============================================================================

/-! ## WS-H9 Part E — Observable-State NI

`switchDomain_preserves_lowEquivalent` (above) is a genuine observable-state NI
theorem: it requires NO non-observability preconditions, proving that domain
switching preserves low-equivalence when the scheduling timing fields (all
observable) determine the same transition in both runs.

`endpointSendDual_observable_NI` below provides a complementary observable-state
result for IPC by bridging from the underlying dual-queue NI to the checked
enforcement wrapper. -/

/-- WS-H9/Part E: Observable-state NI bridge for endpointSendDual.
    If the underlying dual-queue send operation preserves low-equivalence
    (established as a hypothesis from the domain-separation properties of the
    specific call site), then the operation preserves low-equivalence on
    observable endpoints. This is a compositional bridge — the hypothesis is
    discharged by the non-observable companion theorems in the typical case,
    and by direct unwinding arguments for the observable-endpoint case. -/
theorem endpointSendDual_observable_NI
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
    (hStep₁ : endpointSendDual endpointId sender msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSendDual endpointId sender msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' :=
  hSendDualNI s₁ s₂ s₁' s₂' hLow hStep₁ hStep₂

-- ============================================================================
-- WS-E5/H-05 + WS-F3: Bundle-level composed non-interference (IF-M4)
-- ============================================================================

/-! ## H-05 — Composed Bundle Non-Interference

WS-F3/H-09 extends the IF-M4 bundle to cover all 25 kernel operation families.

1. `NonInterferenceStep` — inductive encoding all 25 operation families with
   their domain-separation hypotheses.
2. `step_preserves_projection` — one-sided projection preservation for
   any single step.
3. `composedNonInterference_step` — the primary IF-M4 theorem.
4. `NonInterferenceTrace` — multi-step trace inductive.
5. `composedNonInterference_trace` — trace-level IF-M4 composition.
6. `preservesLowEquivalence` — abstract NI predicate for kernel actions.
-/

/-- WS-F3/H-05/H-09: Inductive covering all 25 operation families with their
full parameter sets and domain-separation hypotheses.

WS-F3 extends the original 5 constructors with notification, service,
capability CRUD, and lifecycle operations. WS-H9 adds scheduler, IPC
dual-queue, VSpace, and extended capability constructors. -/
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
      (hOldCurrent : ∀ tid, st.scheduler.current = some tid →
          threadObservable ctx observer tid = false)
      (hNewCurrent : ∀ tid, st'.scheduler.current = some tid →
          threadObservable ctx observer tid = false)
      (hStep : schedule st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | handleYield
      (hOldCurrent : ∀ tid, st.scheduler.current = some tid →
          threadObservable ctx observer tid = false)
      (hNewCurrent : ∀ tid, st'.scheduler.current = some tid →
          threadObservable ctx observer tid = false)
      (hStep : handleYield st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | timerTick
      (hOldCurrent : ∀ tid, st.scheduler.current = some tid →
          threadObservable ctx observer tid = false)
      (hOldCurrentObj : ∀ tid, st.scheduler.current = some tid →
          objectObservable ctx observer tid.toObjId = false)
      (hNewCurrent : ∀ tid, st'.scheduler.current = some tid →
          threadObservable ctx observer tid = false)
      (hStep : timerTick st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceDeleteSlot
      (addr : CSpaceAddr)
      (hCNodeHigh : objectObservable ctx observer addr.cnode = false)
      (hStep : cspaceDeleteSlot addr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceCopy
      (src dst : CSpaceAddr)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : cspaceCopy src dst st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | cspaceMove
      (src dst : CSpaceAddr)
      (hSrcHigh : objectObservable ctx observer src.cnode = false)
      (hDstHigh : objectObservable ctx observer dst.cnode = false)
      (hStep : cspaceMove src dst st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReceiveDual
      (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (result : SeLe4n.ThreadId)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hReceiverHigh : threadObservable ctx observer receiver = false)
      (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
      (hCoherent : ∀ (tid : SeLe4n.ThreadId),
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hSendQHeadHigh : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.head = some tid → threadObservable ctx observer tid = false)
      (hQueueNextHigh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
          st.objects[tid.toObjId]? = some (.tcb tcb) →
          tcb.queueNext = some nextTid →
          objectObservable ctx observer tid.toObjId = false →
          objectObservable ctx observer nextTid.toObjId = false)
      (hRecvQTailHigh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid →
          objectObservable ctx observer tailTid.toObjId = false)
      (hStep : endpointReceiveDual endpointId receiver st = .ok (result, st'))
    : NonInterferenceStep ctx observer st st'
  | endpointCallStep
      (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hCallerHigh : threadObservable ctx observer caller = false)
      (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
      (hCoherent : ∀ (tid : SeLe4n.ThreadId),
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hRecvQHeadHigh : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.head = some tid → threadObservable ctx observer tid = false)
      (hQueueNextHigh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
          st.objects[tid.toObjId]? = some (.tcb tcb) →
          tcb.queueNext = some nextTid →
          objectObservable ctx observer tid.toObjId = false →
          objectObservable ctx observer nextTid.toObjId = false)
      (hSendQTailHigh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.tail = some tailTid →
          objectObservable ctx observer tailTid.toObjId = false)
      (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReply
      (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
      (hTargetHigh : threadObservable ctx observer target = false)
      (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
      (hStep : endpointReply replier target msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointReplyRecvStep
      (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hReceiverHigh : threadObservable ctx observer receiver = false)
      (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
      (hTargetHigh : threadObservable ctx observer replyTarget = false)
      (hTargetObjHigh : objectObservable ctx observer replyTarget.toObjId = false)
      (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | endpointSendDualStep
      (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
      (hEndpointHigh : objectObservable ctx observer endpointId = false)
      (hSenderHigh : threadObservable ctx observer sender = false)
      (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
      (hCoherent : ∀ (tid : SeLe4n.ThreadId),
          threadObservable ctx observer tid = false →
          objectObservable ctx observer tid.toObjId = false)
      (hRecvQHeadHigh : ∀ (ep : Endpoint) (tid : SeLe4n.ThreadId),
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.head = some tid → threadObservable ctx observer tid = false)
      (hQueueNextHigh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (nextTid : SeLe4n.ThreadId),
          st.objects[tid.toObjId]? = some (.tcb tcb) →
          tcb.queueNext = some nextTid →
          objectObservable ctx observer tid.toObjId = false →
          objectObservable ctx observer nextTid.toObjId = false)
      (hSendQTailHigh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          st.objects[endpointId]? = some (.endpoint ep) →
          ep.sendQ.tail = some tailTid →
          objectObservable ctx observer tailTid.toObjId = false)
      (hStep : endpointSendDual endpointId sender msg st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceMapPageStep
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
      (hRootHigh : ∀ (rootId : SeLe4n.ObjId) (vs : VSpaceRoot),
          Architecture.resolveAsidRoot st asid = some (rootId, vs) →
          objectObservable ctx observer rootId = false)
      (hStep : Architecture.vspaceMapPage asid vaddr paddr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceUnmapPageStep
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
      (hRootHigh : ∀ (rootId : SeLe4n.ObjId) (vs : VSpaceRoot),
          Architecture.resolveAsidRoot st asid = some (rootId, vs) →
          objectObservable ctx observer rootId = false)
      (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st'))
    : NonInterferenceStep ctx observer st st'
  | vspaceLookupStep
      (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (result : SeLe4n.PAddr)
      (hStep : Architecture.vspaceLookup asid vaddr st = .ok (result, st'))
    : NonInterferenceStep ctx observer st st'

/-- WS-F3/H-05: A single non-interference step preserves the observer's
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
    rw [hFinal, hMid]
  | schedule hOC hNC hOp =>
    exact schedule_projection_preserved ctx observer st st' hOC hNC hOp
  | handleYield hOC hNC hOp =>
    exact handleYield_projection_preserved ctx observer st st' hOC hNC hOp
  | timerTick hOC hOCO hNC hOp =>
    exact timerTick_projection_preserved ctx observer st st' hOC hOCO hNC hOp
  | cspaceDeleteSlot addr hCH hOp =>
    exact cspaceDeleteSlot_projection_preserved ctx observer addr st st' hCH hOp
  | cspaceCopy src dst hSH hDH hOp =>
    exact cspaceCopy_projection_preserved ctx observer src dst st st' hSH hDH hOp
  | cspaceMove src dst hSH hDH hOp =>
    exact cspaceMove_projection_preserved ctx observer src dst st st' hSH hDH hOp
  | endpointReceiveDual eid receiver result hEH hRH hROH hCo hSQHH hQNH hRQTH hOp =>
    exact endpointReceiveDual_projection_preserved ctx observer eid receiver result st st'
      hEH hRH hROH hCo hSQHH hQNH hRQTH hOp
  | endpointCallStep eid caller msg hEH hCH hCOH hCo hRQHH hQNH hSQTH hOp =>
    exact endpointCall_projection_preserved ctx observer eid caller msg st st'
      hEH hCH hCOH hCo hRQHH hQNH hSQTH hOp
  | endpointReply replier target msg hTH hTOH hOp =>
    exact endpointReply_projection_preserved ctx observer replier target msg st st'
      hTH hTOH hOp
  | endpointReplyRecvStep eid receiver replyTarget msg hEH hRH hROH hTH hTOH hOp =>
    exact endpointReplyRecv_projection_preserved ctx observer eid receiver replyTarget msg st st'
      hEH hRH hROH hTH hTOH hOp
  | endpointSendDualStep eid sender msg hEH hSH hSOH hCo hRQHH hQNH hSQTH hOp =>
    exact endpointSendDual_projection_preserved ctx observer eid sender msg st st'
      hEH hSH hSOH hCo hRQHH hQNH hSQTH hOp
  | vspaceMapPageStep asid vaddr paddr hRH hOp =>
    exact vspaceMapPage_projection_preserved ctx observer asid vaddr paddr st st' hRH hOp
  | vspaceUnmapPageStep asid vaddr hRH hOp =>
    exact vspaceUnmapPage_projection_preserved ctx observer asid vaddr st st' hRH hOp
  | vspaceLookupStep asid vaddr result hOp =>
    exact vspaceLookup_projection_preserved ctx observer asid vaddr result st st' hOp

/-- WS-F3/H-05: Primary IF-M4 composition theorem — single-step bundle
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
