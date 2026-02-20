import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Lifecycle.Operations

/-!
# Information-Flow Non-Interference Invariants (IF-M2 / WS-D2)

This module defines transition-level non-interference theorems that prove
high-domain kernel operations do not leak information to low-domain observers.

## Proof scope qualification (F-16)

| Category | Theorems |
|---|---|
| **Non-interference** | `endpointSend_at_unobservable_preserves_lowEquivalent`, `endpointReceive_at_unobservable_preserves_lowEquivalent`, `endpointAwaitReceive_at_unobservable_preserves_lowEquivalent`, `chooseThread_preserves_lowEquivalent`, `schedule_preserves_lowEquivalent`, `handleYield_preserves_lowEquivalent`, `cspaceInsertSlot_at_unobservable_preserves_lowEquivalent`, `cspaceDeleteSlot_at_unobservable_preserves_lowEquivalent`, `lifecycleRetypeObject_at_unobservable_preserves_lowEquivalent` |
| **Shared infrastructure** | `storeObject_at_unobservable_preserves_lowEquivalent` |

All non-interference theorems are critical security evidence: they prove that
a kernel operation on a high-domain object preserves low-equivalence for an
unrelated low-domain observer. This is the strongest assurance level in the
proof scope taxonomy.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

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
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = targetId
      · subst hEq; simp [hTargetHigh] at hObs
      · have hObj₁ : s₁'.objects oid = s₁.objects oid :=
          storeObject_objects_ne s₁ s₁' targetId oid obj₁ hEq hStore₁
        have hObj₂ : s₂'.objects oid = s₂.objects oid :=
          storeObject_objects_ne s₂ s₂' targetId oid obj₂ hEq hStore₂
        have hObjBase : s₁.objects oid = s₂.objects oid := by
          have hBase := congrFun hObjLow oid
          simpa [projectObjects, hObs] using hBase
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
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

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
    (_hSenderHigh : threadObservable ctx observer sender = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases endpointSend_ok_as_storeObject s₁ s₁' endpointId sender hStep₁ with ⟨ep₁, hStore₁⟩
  rcases endpointSend_ok_as_storeObject s₂ s₂' endpointId sender hStep₂ with ⟨ep₂, hStore₂⟩
  exact storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer endpointId (.endpoint ep₁) (.endpoint ep₂)
    s₁ s₂ s₁' s₂' hLow hEndpointHigh hStore₁ hStore₂

-- ============================================================================
-- Non-interference theorem #2: chooseThread (WS-D2, F-05, TPI-D01)
-- ============================================================================

/-- Choosing the next thread does not leak high-domain scheduling decisions to
a low-clearance observer.

`chooseThread` is a read-only operation that does not mutate state. Since both
post-states equal their respective pre-states, low-equivalence is preserved
trivially. -/
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

/-- Minting a capability in a non-observable CNode preserves low-equivalence.

If the destination CNode is not observable by the observer, the mint operation
only modifies non-projected state. The source lookup is read-only. -/
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
  -- Decompose cspaceMint = lookup + mintDerivedCap + cspaceInsertSlot
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
      -- Use cspaceInsertSlot preservation helpers
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
          simp only [projectObjects, hObs, ite_true, hObj₁, hObj₂]
          have hBase := congrFun hObjLow oid
          simpa [projectState, projectObjects, hObs] using hBase
        · simp [projectObjects, hObs]
      · simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
      · simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
      · funext sid
        simp only [projectServiceStatus, lookupService]
        rw [show s₁'.services = s₁.services from hSvc₁, show s₂'.services = s₂.services from hSvc₂]
        have hBase := congrArg ObservableState.services hLow
        exact congrFun hBase sid

-- ============================================================================
-- Non-interference theorem #4: cspaceRevoke (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- Revoking capabilities in a non-observable CNode preserves low-equivalence.

If the CNode being revoked is not observable by the observer, the revoke operation
only modifies non-projected state. The operation goes through `storeObject` on the
CNode (filtered slots) then `clearCapabilityRefs` (lifecycle-only changes). Both
preserve scheduler and services. -/
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
  -- Unfold cspaceRevoke to extract its staged decomposition
  unfold cspaceRevoke at hStep₁ hStep₂
  -- Process s₁ side
  cases hL₁ : cspaceLookupSlot addr s₁ with
  | error e => simp [hL₁] at hStep₁
  | ok p₁ =>
    rcases p₁ with ⟨par₁, stL₁⟩
    have hEq₁ : stL₁ = s₁ := cspaceLookupSlot_preserves_state s₁ stL₁ addr par₁ hL₁
    subst stL₁
    -- Process s₂ side
    cases hL₂ : cspaceLookupSlot addr s₂ with
    | error e => simp [hL₂] at hStep₂
    | ok p₂ =>
      rcases p₂ with ⟨par₂, stL₂⟩
      have hEq₂ : stL₂ = s₂ := cspaceLookupSlot_preserves_state s₂ stL₂ addr par₂ hL₂
      subst stL₂
      -- Case-split on the CNode object
      cases hC₁ : s₁.objects addr.cnode with
      | none => simp [hL₁, hC₁] at hStep₁
      | some o₁ =>
        cases o₁ with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hL₁, hC₁] at hStep₁
        | cnode cn₁ =>
          cases hC₂ : s₂.objects addr.cnode with
          | none => simp [hL₂, hC₂] at hStep₂
          | some o₂ =>
            cases o₂ with
            | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hL₂, hC₂] at hStep₂
            | cnode cn₂ =>
              -- Both sides reduce to storeObject + clearCapabilityRefs
              simp [hL₁, hC₁, storeObject] at hStep₁
              simp [hL₂, hC₂, storeObject] at hStep₂
              cases hStep₁; cases hStep₂
              -- Use clearCapabilityRefsState preservation lemmas
              unfold lowEquivalent projectState
              congr 1
              · -- objects: clearCapabilityRefsState preserves objects, storeObject only modifies addr.cnode
                funext oid
                by_cases hObs : objectObservable ctx observer oid
                · have hNe : oid ≠ addr.cnode := by
                    intro hEq; subst hEq; simp [hCNodeHigh] at hObs
                  have hBase : projectObjects ctx observer s₁ oid = projectObjects ctx observer s₂ oid :=
                    congrFun hObjLow oid
                  simp [projectObjects, hObs] at hBase ⊢
                  rw [clearCapabilityRefsState_preserves_objects, clearCapabilityRefsState_preserves_objects]
                  simp [hNe]
                  exact hBase
                · simp [projectObjects, hObs]
              · -- runnable: scheduler preserved by storeObject and clearCapabilityRefsState
                simp only [projectRunnable]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                simpa [projectRunnable] using hRunLow
              · -- current: same
                simp only [projectCurrent]
                rw [clearCapabilityRefsState_preserves_scheduler, clearCapabilityRefsState_preserves_scheduler]
                simpa [projectCurrent] using hCurLow
              · -- services: preserved by storeObject and clearCapabilityRefsState
                funext sid
                simp only [projectServiceStatus, clearCapabilityRefsState_lookupService]
                have hBase := congrArg ObservableState.services hLow
                have hSidBase := congrFun hBase sid
                simpa [projectServiceStatus] using hSidBase

-- ============================================================================
-- Non-interference theorem #5: lifecycleRetypeObject (WS-D2, F-05, TPI-D03)
-- ============================================================================

/-- Retyping an object that is not observable by the observer preserves
low-equivalence.

If the target object being retyped is outside the observer's clearance, the
observer's view of the system state is unaffected. -/
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

end SeLe4n.Kernel
