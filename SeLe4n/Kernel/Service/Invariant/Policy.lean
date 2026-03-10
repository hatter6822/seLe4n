/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Capability.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Reusable policy predicate surface over a single service entry. -/
abbrev ServicePolicyPredicate := SystemState → ServiceGraphEntry → Prop

/-- Policy component: backing object identity remains lifecycle-typed. -/
def policyBackingObjectTyped : ServicePolicyPredicate :=
  fun st svc => ∃ ty, SystemState.lookupObjectTypeMeta st svc.identity.backingObject = some ty

/-- Policy component: lifecycle metadata records an owner-slot reference to the backing object. -/
def policyOwnerAuthorityRefRecorded : ServicePolicyPredicate :=
  fun st svc =>
    ∃ slot,
      SystemState.lookupCapabilityRefMeta st { cnode := svc.identity.owner, slot := slot } =
        some (.object svc.identity.backingObject)

/-- Policy component: owner CNode contains concrete authority to the backing object. -/
def policyOwnerAuthoritySlotPresent : ServicePolicyPredicate :=
  fun st svc =>
    ∃ slot cap,
      SystemState.lookupSlotCap st { cnode := svc.identity.owner, slot := slot } = some cap ∧
      cap.target = .object svc.identity.backingObject

/-- M5 policy bundle entrypoint (WS-M5-C): reusable, mutation-free policy assumptions. -/
def servicePolicySurfaceInvariant (st : SystemState) : Prop :=
  ∀ sid svc,
    lookupService st sid = some svc →
      policyBackingObjectTyped st svc ∧
      (policyOwnerAuthorityRefRecorded st svc → policyOwnerAuthoritySlotPresent st svc)

/-- Cross-subsystem M5 proof-package bundle over service policy + lifecycle + capability surfaces. -/
def serviceLifecycleCapabilityInvariantBundle (st : SystemState) : Prop :=
  servicePolicySurfaceInvariant st ∧ lifecycleInvariantBundle st ∧ capabilityInvariantBundle st

theorem serviceLifecycleCapabilityInvariantBundle_of_components
    (st : SystemState)
    (hPolicy : servicePolicySurfaceInvariant st)
    (hLifecycle : lifecycleInvariantBundle st)
    (hCap : capabilityInvariantBundle st) :
    serviceLifecycleCapabilityInvariantBundle st := by
  exact ⟨hPolicy, hLifecycle, hCap⟩

/-- Bridge lemma: lifecycle typing assumptions imply policy backing-object typing. -/
theorem policyBackingObjectTyped_of_lifecycleInvariant
    (st : SystemState)
    (svc : ServiceGraphEntry)
    (obj : KernelObject)
    (hLifecycle : lifecycleInvariantBundle st)
    (hObj : st.objects[svc.identity.backingObject]? = some obj) :
    policyBackingObjectTyped st svc := by
  rcases hLifecycle with ⟨hIdAlias, _⟩
  rcases hIdAlias with ⟨hTypeExact, _⟩
  refine ⟨obj.objectType, ?_⟩
  simpa [lifecycleIdentityTypeExact, SystemState.objectTypeMetadataConsistent,
    SystemState.lookupObjectTypeMeta, hObj] using hTypeExact svc.identity.backingObject

/-- Bridge lemma: lifecycle capability-reference backing implies concrete slot authority. -/
theorem policyOwnerAuthoritySlotPresent_of_lifecycleInvariant
    (st : SystemState)
    (svc : ServiceGraphEntry)
    (hLifecycle : lifecycleInvariantBundle st)
    (hRef : policyOwnerAuthorityRefRecorded st svc) :
    policyOwnerAuthoritySlotPresent st svc := by
  rcases hLifecycle with ⟨_, hCapRefBundle⟩
  rcases hCapRefBundle with ⟨_hExact, hBacked⟩
  rcases hRef with ⟨slot, hMeta⟩
  rcases hBacked { cnode := svc.identity.owner, slot := slot } svc.identity.backingObject hMeta with
    ⟨cap, hLookup, hTarget⟩
  exact ⟨slot, cap, hLookup, hTarget⟩

/-- Bridge lemma: capability lookup-soundness assumptions imply owner-slot witness facts. -/
theorem policyOwnerAuthoritySlotPresent_of_capabilityLookup
    (st : SystemState)
    (svc : ServiceGraphEntry)
    (slot : SeLe4n.Slot)
    (cap : Capability)
    (_hCap : capabilityInvariantBundle st)
    (hLookup : cspaceLookupSlot { cnode := svc.identity.owner, slot := slot } st = .ok (cap, st))
    (hTarget : cap.target = .object svc.identity.backingObject) :
    policyOwnerAuthoritySlotPresent st svc := by
  have hSlotCap : SystemState.lookupSlotCap st { cnode := svc.identity.owner, slot := slot } = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st { cnode := svc.identity.owner, slot := slot } cap).1 hLookup
  exact ⟨slot, cap, hSlotCap, hTarget⟩

/-- Composed bridge theorem from lifecycle contracts to the service policy surface.

The assumption `hBackingObjects` states that each registered service references an existing backing
object identity in the object store. Under this assumption, lifecycle metadata consistency provides
all policy-surface obligations. -/
theorem servicePolicySurfaceInvariant_of_lifecycleInvariant
    (st : SystemState)
    (hLifecycle : lifecycleInvariantBundle st)
    (hBackingObjects :
      ∀ sid svc, lookupService st sid = some svc →
        ∃ obj, st.objects[svc.identity.backingObject]? = some obj) :
    servicePolicySurfaceInvariant st := by
  intro sid svc hSvc
  rcases hBackingObjects sid svc hSvc with ⟨obj, hObj⟩
  refine ⟨policyBackingObjectTyped_of_lifecycleInvariant st svc obj hLifecycle hObj, ?_⟩
  intro hRef
  exact policyOwnerAuthoritySlotPresent_of_lifecycleInvariant st svc hLifecycle hRef

/-- Policy-denial branch remains a check-only outcome (no state mutation step). -/
theorem serviceStart_policyDenied_separates_check_from_mutation
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hStopped : svc.status = .stopped)
    (hBacking : st.objects[svc.identity.backingObject]? ≠ none)
    (hDenied : policyAllowsStart svc = false) :
    serviceStart sid policyAllowsStart st = .error .policyDenied := by
  exact serviceStart_error_policyDenied st sid policyAllowsStart svc hSvc hStopped hBacking hDenied

/-- Stop-policy denial branch remains a check-only outcome (no state mutation step). -/
theorem serviceStop_policyDenied_separates_check_from_mutation
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hRunning : svc.status = .running)
    (hBacking : st.objects[svc.identity.backingObject]? ≠ none)
    (hDenied : policyAllowsStop svc = false) :
    serviceStop sid policyAllowsStop st = .error .policyDenied := by
  exact serviceStop_error_policyDenied st sid policyAllowsStop svc hSvc hRunning hBacking hDenied

theorem storeServiceState_preserves_servicePolicySurfaceInvariant
    (st : SystemState)
    (sid : ServiceId)
    (svc : ServiceGraphEntry)
    (newStatus : ServiceStatus)
    (hSvc : lookupService st sid = some svc)
    (hPolicy : servicePolicySurfaceInvariant st) :
    servicePolicySurfaceInvariant (storeServiceState sid { svc with status := newStatus } st) := by
  intro sid' svc' hLookup
  by_cases hSid : sid' = sid
  · subst sid'
    have hLookupEq :
        lookupService (storeServiceState sid { svc with status := newStatus } st) sid =
          some { svc with status := newStatus } :=
      storeServiceState_lookup_eq st sid { svc with status := newStatus }
    rw [hLookupEq] at hLookup
    cases hLookup
    rcases hPolicy sid svc hSvc with ⟨hTyped, hBridge⟩
    refine ⟨?_, ?_⟩
    · simpa [policyBackingObjectTyped] using hTyped
    · intro hRef
      have hRefOld : policyOwnerAuthorityRefRecorded st svc := by
        simpa [policyOwnerAuthorityRefRecorded] using hRef
      have hPresentOld : policyOwnerAuthoritySlotPresent st svc := hBridge hRefOld
      simpa [policyOwnerAuthoritySlotPresent] using hPresentOld
  · have hLookupNe := storeServiceState_lookup_ne st sid sid' { svc with status := newStatus } hSid
    have hLookupOld : lookupService st sid' = some svc' := by simpa [hLookupNe] using hLookup
    exact hPolicy sid' svc' hLookupOld

theorem storeServiceState_preserves_lifecycleInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (svc : ServiceGraphEntry)
    (newStatus : ServiceStatus)
    (hLifecycle : lifecycleInvariantBundle st) :
    lifecycleInvariantBundle (storeServiceState sid { svc with status := newStatus } st) := by
  simpa [lifecycleInvariantBundle, lifecycleIdentityAliasingInvariant, lifecycleIdentityTypeExact,
    lifecycleIdentityNoTypeAliasConflict, lifecycleCapabilityReferenceInvariant,
    lifecycleCapabilityRefExact, lifecycleCapabilityRefObjectTargetBacked, storeServiceState,
    SystemState.objectTypeMetadataConsistent, SystemState.capabilityRefMetadataConsistent,
    SystemState.lookupObjectTypeMeta, SystemState.lookupCapabilityRefMeta,
    SystemState.lookupSlotCap, SystemState.lookupCNode] using hLifecycle

/-- `storeServiceState` preserves the capability invariant bundle compositionally.

`storeServiceState` only modifies the `services` field, leaving the object store
unchanged. Therefore CNode slot-index uniqueness transfers directly from the pre-state. -/
theorem storeServiceState_preserves_capabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (svc : ServiceGraphEntry)
    (newStatus : ServiceStatus)
    (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle (storeServiceState sid { svc with status := newStatus } st) := by
  rcases hInv with ⟨hUnique, hSound, hAttRule, _, hBounded, hComp, hAcyclic⟩
  refine ⟨?_, ?_, hAttRule, lifecycleAuthorityMonotonicity_holds _, hBounded, hComp, hAcyclic⟩
  · intro cnodeId cn hCn
    exact hUnique cnodeId cn hCn
  · intro cnodeId cn slot cap hCn hMem
    have hSlot := hSound cnodeId cn slot cap hCn hMem
    simp only [SystemState.lookupSlotCap, storeServiceState] at hSlot ⊢
    exact hSlot

theorem serviceStart_preserves_serviceLifecycleCapabilityInvariantBundle
    (st st' : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (hStep : serviceStart sid policyAllowsStart st = .ok ((), st')) :
    serviceLifecycleCapabilityInvariantBundle st' := by
  rcases hInv with ⟨hPolicy, hLifecycle, hCap⟩
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      have hSvc : lookupService st sid = some svc := hLookup
      by_cases hStopped : svc.status = .stopped
      · simp [hLookup, hStopped] at hStep
        split at hStep <;> try (simp at hStep)
        by_cases hAllow : policyAllowsStart svc
        · by_cases hDeps : dependenciesSatisfied st sid
          · unfold storeServiceEntry at hStep
            simp [hAllow, hDeps, storeServiceState] at hStep
            cases hStep
            exact ⟨
              storeServiceState_preserves_servicePolicySurfaceInvariant st sid svc .running hSvc hPolicy,
              storeServiceState_preserves_lifecycleInvariantBundle st sid svc .running hLifecycle,
              storeServiceState_preserves_capabilityInvariantBundle st sid svc .running hCap
            ⟩
          · simp [hAllow, hDeps] at hStep
        · simp [hAllow] at hStep
      · simp [hLookup, hStopped] at hStep

theorem serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle
    (st st' : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (hStep : serviceStop sid policyAllowsStop st = .ok ((), st')) :
    serviceLifecycleCapabilityInvariantBundle st' := by
  rcases hInv with ⟨hPolicy, hLifecycle, hCap⟩
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      have hSvc : lookupService st sid = some svc := hLookup
      by_cases hRunning : svc.status = .running
      · by_cases hBacking : st.objects[svc.identity.backingObject]? = none
        · simp [hLookup, hRunning, hBacking] at hStep
        · by_cases hAllow : policyAllowsStop svc
          · unfold storeServiceEntry at hStep
            simp [hLookup, hRunning, hBacking, hAllow, storeServiceState] at hStep
            cases hStep
            exact ⟨
              storeServiceState_preserves_servicePolicySurfaceInvariant st sid svc .stopped hSvc hPolicy,
              storeServiceState_preserves_lifecycleInvariantBundle st sid svc .stopped hLifecycle,
              storeServiceState_preserves_capabilityInvariantBundle st sid svc .stopped hCap
            ⟩
          · simp [hLookup, hRunning, hBacking, hAllow] at hStep
      · simp [hLookup, hRunning] at hStep

theorem serviceRestart_preserves_serviceLifecycleCapabilityInvariantBundle
    (st st' : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (hStep : serviceRestart sid policyAllowsStop policyAllowsStart st = .ok ((), st')) :
    serviceLifecycleCapabilityInvariantBundle st' := by
  rcases serviceRestart_ok_implies_staged_steps st st' sid policyAllowsStop policyAllowsStart hStep with
    ⟨stStopped, hStop, hStart⟩
  have hStoppedInv : serviceLifecycleCapabilityInvariantBundle stStopped :=
    serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle
      st stStopped sid policyAllowsStop hInv hStop
  exact serviceStart_preserves_serviceLifecycleCapabilityInvariantBundle
    stStopped st' sid policyAllowsStart hStoppedInv hStart

theorem serviceStart_failure_preserves_serviceLifecycleCapabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (_hStep : serviceStart sid policyAllowsStart st = .error e) :
    serviceLifecycleCapabilityInvariantBundle st := by
  exact hInv

theorem serviceStop_failure_preserves_serviceLifecycleCapabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (e : KernelError)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (_hStep : serviceStop sid policyAllowsStop st = .error e) :
    serviceLifecycleCapabilityInvariantBundle st := by
  exact hInv

theorem serviceRestart_stop_failure_preserves_serviceLifecycleCapabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (_hStep : serviceRestart sid policyAllowsStop policyAllowsStart st = .error e)
    (_hStop : serviceStop sid policyAllowsStop st = .error e) :
    serviceLifecycleCapabilityInvariantBundle st := by
  exact hInv

theorem serviceRestart_start_failure_preserves_serviceLifecycleCapabilityInvariantBundle
    (st stStopped : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (hInv : serviceLifecycleCapabilityInvariantBundle st)
    (hStop : serviceStop sid policyAllowsStop st = .ok ((), stStopped))
    (_hStart : serviceStart sid policyAllowsStart stStopped = .error e) :
    serviceLifecycleCapabilityInvariantBundle stStopped := by
  exact serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle
    st stStopped sid policyAllowsStop hInv hStop

-- ============================================================================
-- F-07: Service dependency acyclicity invariant (WS-D4, TPI-D07)
-- ============================================================================

/-!
## TPI-D07 proof infrastructure plan

### Definitions (Layer 0)
- `serviceEdge` — direct dependency edge relation
- `serviceReachable` — reflexive-transitive closure of serviceEdge
- `serviceHasNontrivialPath` — path of length ≥ 1
- `serviceDependencyAcyclicDecl` — declarative acyclicity (no non-trivial self-loops)

### Structural lemmas (Layer 1)
- `serviceEdge_iff_mem` — definitional unfolding
- `serviceReachable_trans` — path concatenation
- `serviceReachable_of_edge` — single-edge path
- `serviceReachable_step_right` — right-append edge
- `serviceHasNontrivialPath_of_edge` — edge implies nontrivial path
- `storeServiceState_objectIndex_eq` — objectIndex frame condition
- `serviceBfsFuel_storeServiceState_eq` — fuel frame condition
- `serviceEdge_storeServiceState_eq` — edge at updated service
- `serviceEdge_storeServiceState_ne` — edge at non-updated service
- `serviceEdge_post_insert` — edge characterization after insertion

### Graph traversal soundness (Layer 2)
- `serviceHasPathTo_true_implies_reachable` — traversal true → declarative path
- `serviceHasPathTo_go_invariant` — traversal loop invariant
- `serviceBfsFuel_sufficient` — fuel adequacy
- `serviceHasPathTo_false_implies_not_reachable` — traversal false → no path

### Edge insertion (Layer 3)
- `serviceEdge_post_cases` — post-state edge decomposition
- `serviceReachable_post_insert_cases` — post-state path decomposition
- `nontrivial_cycle_post_insert_implies_pre_reach` — cycle → pre-state reachability
- `serviceDependencyAcyclicDecl_preserved` — declarative acyclicity preserved

### Final closure (Layer 4)
- `serviceDependencyAcyclic_implies_acyclicDecl` — traversal → declarative equivalence
- `serviceDependencyAcyclicDecl_implies_acyclic` — declarative → traversal equivalence
-/
