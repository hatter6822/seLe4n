import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Enforcement
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Service.Invariant

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
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc', hDom', hIrq', hIdx']

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
  simp only [projectState, hObj, hRun, hCur, hSvc, hDom, hIrq, hIdx]

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
-- WS-E5/H-05 + WS-F3: Bundle-level composed non-interference (IF-M4)
-- ============================================================================

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
    rw [hFinal, hMid]

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
