/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Invariant.Helpers

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ### WS-F3/K-F5: Capability CRUD and Lifecycle NI proofs — all completed

The following capability and lifecycle operations have NI properties that
follow from compositional reasoning over `storeObject`-level primitives.

**CSpace operations (completed WS-H9):**
- `cspaceDeleteSlot_preserves_lowEquivalent` — line 978
- `cspaceCopy_preserves_lowEquivalent` — line 1099
- `cspaceMove_preserves_lowEquivalent` — line 1158

**Lifecycle operations (completed WS-K-F5):**
- `lifecycleRetypeObject_preserves_lowEquivalent` — Helpers.lean:670
- `retypeFromUntyped_preserves_lowEquivalent` — end of this file
- `lifecycleRevokeDeleteRetype_preserves_projection` — end of this file
- `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` — end of this file

The pattern for each is identical: all mutations happen at non-observable
targets via `storeObject`, and CDT/lifecycle metadata is not part of
`ObservableState`. The proofs compose `storeObject_preserves_projection`
with CDT-specific frame lemmas.
-/

-- ============================================================================
-- WS-F3: Service operation NI theorems
-- ============================================================================

/-- WS-F3: serviceStart at a non-observable service preserves low-equivalence.
Service operations only modify the service store, not objects or scheduler. -/
private theorem serviceStart_preserves_lowEquivalent
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
private theorem serviceStop_preserves_lowEquivalent
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

/-- WS-F3/F-20: If cspaceMintChecked succeeds, the resulting state transition
preserves low-equivalence. -/
theorem cspaceMintChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
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

The proof reduces the dual-queue checked wrapper to `endpointSendDual`
via the enforcement flow extraction. The NI property for the underlying
`endpointSendDual` is taken as a hypothesis. -/
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
private theorem cspaceCopyChecked_NI
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
theorem setCurrentThread_preserves_projection
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

/-- WS-H12b: Removing a non-observable thread from the run queue preserves projection.
The `RunQueue.remove` operation only drops the given thread; since it's non-observable,
the filtered `projectRunnable` list is unchanged. -/
private theorem remove_rq_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.remove tid } }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList_filter_remove_neg _ _ _ hTidHigh]

/-- WS-H12b: Inserting a non-observable thread into the run queue preserves projection,
provided the thread was not already in the queue. -/
private theorem insert_rq_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId) (prio : Priority)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hNotMem : ¬(tid ∈ st.scheduler.runQueue)) :
    projectState ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.insert tid prio } }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList_filter_insert_neg _ _ _ _ hTidHigh hNotMem]


/-- WS-H12c: saveOutgoingContext produces a state whose non-objects, non-scheduler
fields are identical to the original. -/
private theorem saveOutgoingContext_machine (st : SystemState) :
    (saveOutgoingContext st).machine = st.machine := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

private theorem saveOutgoingContext_services (st : SystemState) :
    (saveOutgoingContext st).services = st.services := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

private theorem saveOutgoingContext_irqHandlers (st : SystemState) :
    (saveOutgoingContext st).irqHandlers = st.irqHandlers := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

private theorem saveOutgoingContext_objectIndex (st : SystemState) :
    (saveOutgoingContext st).objectIndex = st.objectIndex := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

/-- WS-H12c: saveOutgoingContext preserves projectObjects because
projectKernelObject strips registerContext from TCBs. -/
private theorem saveOutgoingContext_preserves_projectObjects
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (oid : SeLe4n.ObjId) :
    projectObjects ctx observer (saveOutgoingContext st) oid =
    projectObjects ctx observer st oid := by
  simp only [projectObjects]
  split
  · next hObs =>
      simp only [saveOutgoingContext]
      cases hCur : st.scheduler.current with
      | none => rfl
      | some outTid =>
          cases hOut : st.objects[outTid.toObjId]? with
          | none => simp_all
          | some outObj =>
              cases outObj with
              | tcb outTcb =>
                  simp only [hOut, Option.map]
                  rw [HashMap_getElem?_insert]
                  by_cases hEq : outTid.toObjId == oid
                  · simp only [hEq, ↓reduceIte, projectKernelObject]
                    have hEq' := beq_iff_eq.mp hEq
                    subst hEq'; simp only [hOut]
                  · simp [hEq]
              | endpoint _ => simp_all
              | notification _ => simp_all
              | cnode _ => simp_all
              | vspaceRoot _ => simp_all
              | untyped _ => simp_all
  · rfl

/-- WS-H12c: saveOutgoingContext preserves the information-flow projection.
The context save only modifies `registerContext` in one TCB. Since
`projectKernelObject` strips `registerContext` (replacing it with `default`),
this does not change the projected objects. -/
private theorem saveOutgoingContext_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    projectState ctx observer (saveOutgoingContext st) = projectState ctx observer st := by
  simp only [saveOutgoingContext]
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases hOut : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              simp only [hOut]
              -- Now: projectState ctx observer { st with objects := st.objects.insert ... } = projectState ctx observer st
              simp only [projectState]
              congr 1
              · -- objects field
                exact funext (fun oid => by
                  simp only [projectObjects]
                  split
                  · simp only [Option.map]
                    rw [HashMap_getElem?_insert]
                    by_cases hEq : outTid.toObjId == oid
                    · simp only [hEq, ↓reduceIte, projectKernelObject]
                      have hEq' := beq_iff_eq.mp hEq
                      subst hEq'; simp only [hOut]
                    · simp [hEq]
                  · rfl)
          | endpoint _ => simp_all
          | notification _ => simp_all
          | cnode _ => simp_all
          | vspaceRoot _ => simp_all
          | untyped _ => simp_all

/-- WS-H12c: restoreIncomingContext preserves the information-flow projection
when the current thread is non-observable. -/
private theorem restoreIncomingContext_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false) :
    projectState ctx observer (restoreIncomingContext st tid) = projectState ctx observer st := by
  simp only [restoreIncomingContext]
  cases hTcb : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      cases obj with
      | tcb inTcb =>
          simp only []
          -- Goal: projectState ctx observer { st with machine := { st.machine with regs := inTcb.registerContext } } = projectState ctx observer st
          -- Only machine.regs changes; all other projection fields are unchanged
          simp only [projectState]
          congr 1
          · -- machineRegs: current is non-observable, so regs projected as none regardless
            simp only [projectMachineRegs]
            cases hCur : st.scheduler.current with
            | none => rfl
            | some t => simp [hCurrentHigh t hCur]
      | endpoint _ => simp_all
      | notification _ => simp_all
      | cnode _ => simp_all
      | vspaceRoot _ => simp_all
      | untyped _ => simp_all

/-- WS-H12c: projectObjects depends only on the objects field. -/
private theorem projectObjects_ext_objects
    (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState)
    (hObjs : s₁.objects = s₂.objects) :
    (fun oid => projectObjects ctx observer s₁ oid) =
    (fun oid => projectObjects ctx observer s₂ oid) := by
  ext oid; simp only [projectObjects, hObjs]

/-- WS-H12c: saveOutgoingContext with a scheduler override preserves projection
relative to the same scheduler override on the original state. -/
private theorem saveOutgoingContext_with_sched_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (sched : SchedulerState) :
    projectState ctx observer { (saveOutgoingContext st) with scheduler := sched }
    = projectState ctx observer { st with scheduler := sched } := by
  simp only [saveOutgoingContext]
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases hOut : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              simp only [hOut]
              -- Goal: projectState ctx observer { { st with objects := st.objects.insert ... } with scheduler := sched }
              --     = projectState ctx observer { st with scheduler := sched }
              -- The LHS has objects changed, everything else (incl. scheduler override) same
              simp only [projectState]
              congr 1
              · -- objects field: same proof as saveOutgoingContext_preserves_projection
                exact funext (fun oid => by
                  simp only [projectObjects]
                  split
                  · simp only [Option.map]
                    rw [HashMap_getElem?_insert]
                    by_cases hEq : outTid.toObjId == oid
                    · simp only [hEq, ↓reduceIte, projectKernelObject]
                      have hEq' := beq_iff_eq.mp hEq
                      subst hEq'; simp only [hOut]
                    · simp [hEq]
                  · rfl)
          | endpoint _ => simp_all
          | notification _ => simp_all
          | cnode _ => simp_all
          | vspaceRoot _ => simp_all
          | untyped _ => simp_all

/-- WS-H9/H12c: schedule when all schedulable threads are non-observable preserves projection.
schedule = chooseThread >> save >> dequeue >> restore >> setCurrentThread.
Context save/restore and dequeue preserve the projection. -/
theorem schedule_preserves_projection
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
      exact (setCurrentThread_preserves_projection ctx observer none (saveOutgoingContext st) st'
        (fun _ h => by cases h)
        (fun t h => by rw [saveOutgoingContext_scheduler] at h; exact hCurrentHigh t h)
        hStep).trans (saveOutgoingContext_preserves_projection ctx observer st)
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
            have hTidHigh : threadObservable ctx observer tid = false :=
              hAllRunnable tid ((RunQueue.mem_toList_iff_mem _ tid).mpr hCond.1)
            have hSavedSched : (saveOutgoingContext st).scheduler = st.scheduler :=
              saveOutgoingContext_scheduler st
            let stSaved := saveOutgoingContext st
            let stDequeued := { stSaved with scheduler :=
                { stSaved.scheduler with runQueue := stSaved.scheduler.runQueue.remove tid } }
            let stRestored := restoreIncomingContext stDequeued tid
            have hSetProj := setCurrentThread_preserves_projection ctx observer (some tid) stRestored st'
              (fun t h => by cases h; exact hTidHigh)
              (fun t hc => by
                simp only [stRestored, restoreIncomingContext_scheduler, stDequeued] at hc
                rw [hSavedSched] at hc
                exact hCurrentHigh t hc)
              hStep
            have hRestoreProj := restoreIncomingContext_preserves_projection ctx observer stDequeued tid
              (fun t h => by
                simp only [stDequeued] at h
                rw [hSavedSched] at h
                exact hCurrentHigh t h)
            have hDeqProj : projectState ctx observer stDequeued = projectState ctx observer st := by
              have hDeqEq : stDequeued = { saveOutgoingContext st with scheduler :=
                  { st.scheduler with runQueue := st.scheduler.runQueue.remove tid } } := by
                simp only [stDequeued, stSaved, hSavedSched]
              rw [hDeqEq]
              exact (saveOutgoingContext_with_sched_preserves_projection ctx observer st _).trans
                (remove_rq_preserves_projection ctx observer st tid hTidHigh)
            exact hSetProj.trans (hRestoreProj.trans hDeqProj)
          · simp at hStep
        | _ => simp [hObj] at hStep

/-- WS-H9/H12b: switchDomain preserves low-equivalence (deterministic on scheduler fields).
switchDomain only modifies scheduler fields (current, activeDomain, domainTimeRemaining,
domainScheduleIndex) and optionally re-enqueues a non-observable current thread.
All computations depend only on fields that are in the observable projection
(domainSchedule, domainScheduleIndex), which are identical in low-equivalent states.
WS-H12b: requires current threads to be non-observable so the re-enqueue
does not affect the projected runnable list. -/
theorem switchDomain_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t → threadObservable ctx observer t = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t → threadObservable ctx observer t = false)
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
      -- WS-H12b: Helper to reduce the match-based runQueue to the original runQueue
      -- in the filtered (projected) list. Non-observable current thread's insert is invisible.
      have rq_filter_reduce : ∀ (s : SystemState),
          (∀ t, s.scheduler.current = some t → threadObservable ctx observer t = false) →
          (match s.scheduler.current with
            | none => s.scheduler.runQueue
            | some tid => match s.objects[tid.toObjId]? with
              | some (KernelObject.tcb tcb) => s.scheduler.runQueue.insert tid tcb.priority
              | _ => s.scheduler.runQueue).toList.filter (threadObservable ctx observer)
          = s.scheduler.runQueue.toList.filter (threadObservable ctx observer) := by
        intro s hCurH
        split
        · -- current = none
          rfl
        · -- current = some tid, split on objects lookup
          next tid hCur =>
          have hH := hCurH tid hCur
          split
          · -- objects = some (.tcb tcb)
            next tcb _ => exact RunQueue.toList_filter_insert_neg' _ _ _ _ hH
          · -- objects = not tcb (catch-all)
            rfl
      simp only [projectState]; congr 1
      · exact congrArg ObservableState.objects hLow
      · -- WS-H12b: runnable field uses rq_filter_reduce
        simp only [projectRunnable, SchedulerState.runnable]
        have h₁ := rq_filter_reduce s₁ hCurrentHigh₁
        have h₂ := rq_filter_reduce s₂ hCurrentHigh₂
        have hBase := congrArg ObservableState.runnable hLow
        simp only [projectState, projectRunnable, SchedulerState.runnable] at hBase
        exact h₁.trans (hBase.trans h₂.symm)
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
theorem vspaceMapPage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr default st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold Architecture.vspaceMapPage at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨rootId, root⟩
    simp only [hResolve] at hStep
    simp only [PagePermissions.default_wxCompliant, Bool.not_true] at hStep
    cases hMap : root.mapPage vaddr paddr default with
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
    (hStep₁ : Architecture.vspaceMapPage asid vaddr paddr default s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceMapPage asid vaddr paddr default s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    vspaceMapPage_preserves_projection ctx observer asid vaddr paddr s₁ s₁' hRootHigh₁ hStep₁,
    vspaceMapPage_preserves_projection ctx observer asid vaddr paddr s₂ s₂' hRootHigh₂ hStep₂]
  exact hLow

/-- WS-H9: vspaceUnmapPage at a non-observable VSpace root preserves projection. -/
theorem vspaceUnmapPage_preserves_projection
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
    cases hLookup : root.lookupAddr vaddr with
    | none => simp [hLookup] at hStep
    | some p =>
      simp only [hLookup, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact hStep.2.symm

-- WS-H9: vspaceLookup preserves low-equivalence (trivially, as read-only).
/-- WS-I2/R-16: VSpace map preserves low-equivalence under optional memory
ownership projection when the mapped physical address is non-observable. The
operation updates only VSpace metadata, not machine memory, so projection
preservation follows from the base theorem. -/
theorem vspaceMapPage_preserves_lowEquivalent_memoryOwnedHigh
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (_hOwnerHigh : ∀ mo dom,
      ctx.memoryOwnership = some mo →
      mo.regionOwner paddr = some dom →
      securityFlowsTo (mo.domainLabelOf dom) observer.clearance = false)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep₁ : Architecture.vspaceMapPage asid vaddr paddr default s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceMapPage asid vaddr paddr default s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  exact vspaceMapPage_preserves_lowEquivalent ctx observer asid vaddr paddr
    s₁ s₂ s₁' s₂' hLow hRootHigh₁ hRootHigh₂ hStep₁ hStep₂

/-- WS-I2/R-16: VSpace unmap preserves low-equivalence under optional memory
ownership projection. Unmapping mutates VSpace metadata only. -/
theorem vspaceUnmapPage_preserves_lowEquivalent_memoryOwnedHigh
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (_hOwnerHigh : ∀ mo paddr dom,
      ctx.memoryOwnership = some mo →
      mo.regionOwner paddr = some dom →
      securityFlowsTo (mo.domainLabelOf dom) observer.clearance = false)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hStep₁ : Architecture.vspaceUnmapPage asid vaddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceUnmapPage asid vaddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  exact vspaceUnmapPage_preserves_lowEquivalent ctx observer asid vaddr
    s₁ s₂ s₁' s₂' hLow hRootHigh₁ hRootHigh₂ hStep₁ hStep₂

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
theorem storeCapabilityRef_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeCapabilityRef at hStep
  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
  have hEq := hStep.2.symm; subst hEq
  simp only [projectState]; congr 1

/-- WS-H9: cspaceDeleteSlot at a non-observable CNode preserves projection. -/
theorem cspaceDeleteSlot_preserves_projection
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
private theorem cspaceDeleteSlot_preserves_lowEquivalent
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

/-- cspaceRevoke at a non-observable CNode preserves projection.
Extracted as a standalone theorem for compositional reasoning in
`lifecycleRevokeDeleteRetype_preserves_projection`. -/
theorem cspaceRevoke_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (st st' : SystemState)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceRevoke at hStep
  cases hL : cspaceLookupSlot addr st with
  | error e => simp [hL] at hStep
  | ok p =>
    rcases p with ⟨par, stL⟩
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr par hL
    subst stL
    cases hC : st.objects[addr.cnode]? with
    | none => simp [hL, hC] at hStep
    | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL, hC] at hStep
      | cnode cn =>
        simp [hL, hC, storeObject] at hStep; cases hStep
        rw [revokeAndClearRefsState_preserves_projectState]
        simp only [projectState]; congr 1
        · funext oid; by_cases hObs : objectObservable ctx observer oid
          · simp [projectObjects, hObs]
            have hNe : oid ≠ addr.cnode := by
              intro hEq; subst hEq; simp [hAddrHigh] at hObs
            simp [HashMap_getElem?_insert, Ne.symm hNe]
          · simp [projectObjects, hObs]
        · simp only [projectObjectIndex]
          split
          · rfl
          · rw [List.filter_cons]; simp [hAddrHigh]

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
theorem cspaceCopy_preserves_projection
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
private theorem cspaceCopy_preserves_lowEquivalent
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
theorem cspaceMove_preserves_projection
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
private theorem cspaceMove_preserves_lowEquivalent
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
theorem storeTcbQueueLinks_preserves_projection
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
theorem endpointReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
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
theorem handleYield_preserves_projection
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
    simp only [hCur] at hStep
    -- WS-H12b: new handleYield does match on objects, then insert + rotateToBack + schedule
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        -- hStep : schedule { st with scheduler.runQueue := (rq.insert tid prio).rotateToBack tid } = .ok ((), st')
        let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
        let stIR : SystemState :=
          { st with scheduler := { st.scheduler with runQueue := rq' } }
        -- Show insert + rotateToBack preserves projection
        have hInsertRotProj : projectState ctx observer stIR = projectState ctx observer st := by
          simp only [projectState]; congr 1
          · simp only [projectRunnable, SchedulerState.runnable]
            rw [RunQueue.toList_filter_rotateToBack_neg _ _ _ hTidHigh,
                RunQueue.toList_filter_insert_neg' _ _ _ _ hTidHigh]
        have hAllRunnableIR : ∀ t, t ∈ stIR.scheduler.runnable →
            threadObservable ctx observer t = false := by
          intro t hMem'; simp only [SchedulerState.runnable] at hMem'
          have hMemRot := (RunQueue.rotateToBack_mem_iff _ _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp hMem')
          rcases (RunQueue.mem_insert _ _ _ t).mp hMemRot with hOrig | hEq
          · exact hAllRunnable t ((RunQueue.mem_toList_iff_mem _ t).mpr hOrig)
          · subst hEq; exact hTidHigh
        have hSchedStep : schedule stIR = .ok ((), st') := by
          simpa [stIR, rq', hCur] using hStep
        exact (schedule_preserves_projection ctx observer stIR st'
          (fun t hc => hCurrentHigh t (by simpa [stIR] using hc))
          hAllRunnableIR hSchedStep).trans hInsertRotProj
      | _ => simp [hObj] at hStep

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
theorem timerTick_preserves_projection
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
      · -- Time-slice expired: insert back into runQueue + schedule
        -- WS-H12b: new timerTick does insert (re-enqueue) then schedule, no if-then-else
        let tcbReset : KernelObject := KernelObject.tcb { tcb with timeSlice := defaultTimeSlice }
        have hInsertTickProj := insert_tick_preserves_projection ctx observer st
          tid.toObjId tcbReset hTidObjHigh
        let stIT : SystemState :=
          { st with objects := st.objects.insert tid.toObjId tcbReset, machine := tick st.machine }
        -- stIT has the same runQueue as st
        let stInsert : SystemState :=
          { stIT with scheduler := { stIT.scheduler with
              runQueue := stIT.scheduler.runQueue.insert tid tcb.priority } }
        -- Show insert preserves projection (non-observable thread)
        have hInsertRqProj : projectState ctx observer stInsert = projectState ctx observer stIT := by
          simp only [projectState]; congr 1
          · simp only [projectRunnable, SchedulerState.runnable]
            exact RunQueue.toList_filter_insert_neg' _ _ _ _ hTidHigh
        have hCurSched : ∀ t, stInsert.scheduler.current = some t →
            threadObservable ctx observer t = false :=
          fun t hc => hCurrentHigh t (by simpa [stInsert, stIT] using hc)
        have hAllRunnableSched : ∀ t, t ∈ stInsert.scheduler.runnable →
            threadObservable ctx observer t = false := by
          intro t hMem'; simp only [SchedulerState.runnable] at hMem'
          rcases (RunQueue.mem_insert _ _ _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp hMem') with hOrig | hEq
          · exact hAllRunnable t ((RunQueue.mem_toList_iff_mem _ t).mpr hOrig)
          · subst hEq; exact hTidHigh
        have hSchedStep : schedule stInsert = .ok ((), st') := by
          simpa [stInsert, stIT, hCur] using hStep
        rw [schedule_preserves_projection ctx observer stInsert st' hCurSched hAllRunnableSched hSchedStep,
            hInsertRqProj, hInsertTickProj]
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

-- ============================================================================
-- WS-K-F5: Lifecycle NI proofs — completing deferred proof list
-- ============================================================================

/-- WS-K-F5: `retypeFromUntyped` at non-observable targets preserves
low-equivalence. The operation decomposes (via `retypeFromUntyped_ok_decompose`)
into a read-only `cspaceLookupSlot` followed by two `storeObject` calls —
one for the untyped watermark advance and one for the new child. Both targets
are non-observable, so each store preserves low-equivalence. -/
theorem retypeFromUntyped_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hUntypedHigh : objectObservable ctx observer untypedId = false)
    (hChildHigh : objectObservable ctx observer childId = false)
    (hStep₁ : retypeFromUntyped authority untypedId childId newObj allocSize s₁ = .ok ((), s₁'))
    (hStep₂ : retypeFromUntyped authority untypedId childId newObj allocSize s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Decompose each step into constituent storeObject calls
  rcases retypeFromUntyped_ok_decompose s₁ s₁' authority untypedId childId newObj allocSize hStep₁ with
    ⟨ut₁, ut₁', cap₁, stL₁, stUt₁, _, _, _, _, hLookup₁, _, _, hStoreUt₁, hStoreChild₁⟩
  rcases retypeFromUntyped_ok_decompose s₂ s₂' authority untypedId childId newObj allocSize hStep₂ with
    ⟨ut₂, ut₂', cap₂, stL₂, stUt₂, _, _, _, _, hLookup₂, _, _, hStoreUt₂, hStoreChild₂⟩
  -- Lookup is read-only: stL₁ = s₁, stL₂ = s₂
  have hEqL₁ := cspaceLookupSlot_ok_state_eq s₁ authority cap₁ stL₁ hLookup₁
  have hEqL₂ := cspaceLookupSlot_ok_state_eq s₂ authority cap₂ stL₂ hLookup₂
  rw [hEqL₁] at hStoreUt₁; rw [hEqL₂] at hStoreUt₂
  -- First storeObject (untyped update) at non-observable untypedId
  have hMid := storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer untypedId (.untyped ut₁') (.untyped ut₂') s₁ s₂ stUt₁ stUt₂
    hLow hUntypedHigh hStoreUt₁ hStoreUt₂
  -- Second storeObject (child creation) at non-observable childId
  exact storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer childId newObj newObj stUt₁ stUt₂ s₁' s₂'
    hMid hChildHigh hStoreChild₁ hStoreChild₂

-- ============================================================================
-- lifecycleRevokeDeleteRetype NI proofs
-- ============================================================================

/-- `lifecycleRevokeDeleteRetype` at non-observable cleanup CNode and target
preserves projection. The operation decomposes (via
`lifecycleRevokeDeleteRetype_ok_implies_staged_steps`) into:
1. `cspaceRevoke` at `cleanup` — projection preserved by `cspaceRevoke_preserves_projection`,
2. `cspaceDeleteSlot` at `cleanup` — projection preserved by `cspaceDeleteSlot_preserves_projection`,
3. `cspaceLookupSlot` at `cleanup` — read-only (fails with `invalidCapability`, no state change),
4. `lifecycleRetypeObject` at `target` — projection preserved via `storeObject_preserves_projection`. -/
theorem lifecycleRevokeDeleteRetype_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (authority cleanup : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (hCleanupHigh : objectObservable ctx observer cleanup.cnode = false)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _, hRevoke, hDelete, _, hRetype⟩
  rcases lifecycleRetypeObject_ok_as_storeObject stDeleted st' authority target newObj hRetype with
    ⟨_, _, _, _, _, _, hStore⟩
  rw [storeObject_preserves_projection ctx observer stDeleted st' target newObj hTargetHigh hStore,
      cspaceDeleteSlot_preserves_projection ctx observer cleanup stRevoked stDeleted hCleanupHigh hDelete,
      cspaceRevoke_preserves_projection ctx observer cleanup st stRevoked hCleanupHigh hRevoke]

/-- `lifecycleRevokeDeleteRetype` at non-observable cleanup CNode and target
preserves low-equivalence. Composes low-equivalence preservation across
three sub-operations: `cspaceRevoke`, `cspaceDeleteSlot`, and
`lifecycleRetypeObject`. -/
theorem lifecycleRevokeDeleteRetype_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (authority cleanup : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCleanupHigh : objectObservable ctx observer cleanup.cnode = false)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hStep₁ : lifecycleRevokeDeleteRetype authority cleanup target newObj s₁ = .ok ((), s₁'))
    (hStep₂ : lifecycleRevokeDeleteRetype authority cleanup target newObj s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    lifecycleRevokeDeleteRetype_preserves_projection ctx observer authority cleanup target
      newObj s₁ s₁' hCleanupHigh hTargetHigh hStep₁,
    lifecycleRevokeDeleteRetype_preserves_projection ctx observer authority cleanup target
      newObj s₂ s₂' hCleanupHigh hTargetHigh hStep₂]
  exact hLow

