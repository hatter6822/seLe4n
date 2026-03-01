import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Lifecycle.Invariant

/-!
# Service Invariant Preservation Proofs

This module contains policy-surface definitions and preservation theorems for the
service orchestration subsystem, including cross-subsystem composition with lifecycle
and capability invariants.

## Proof scope qualification (F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
- `serviceStart_preserves_serviceLifecycleCapabilityInvariantBundle`
- `serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle`
- `serviceRestart_preserves_serviceLifecycleCapabilityInvariantBundle`
- `storeServiceState_preserves_servicePolicySurfaceInvariant`
- `storeServiceState_preserves_lifecycleInvariantBundle`
- `storeServiceState_preserves_capabilityInvariantBundle`

**Structural / bridge theorems** (high assurance):
- `servicePolicySurfaceInvariant_of_lifecycleInvariant`
- `policyBackingObjectTyped_of_lifecycleInvariant`
- `policyOwnerAuthoritySlotPresent_of_lifecycleInvariant`
- `policyOwnerAuthoritySlotPresent_of_capabilityLookup`
- `serviceLifecycleCapabilityInvariantBundle_of_components`

**Check-vs-mutation separation theorems** (high assurance):
- `serviceStart_policyDenied_separates_check_from_mutation`
- `serviceStop_policyDenied_separates_check_from_mutation`

**Error-case preservation theorems** (trivially true — the error path returns
unchanged state):
- `serviceStart_failure_preserves_serviceLifecycleCapabilityInvariantBundle`
- `serviceStop_failure_preserves_serviceLifecycleCapabilityInvariantBundle`
- `serviceRestart_stop_failure_preserves_serviceLifecycleCapabilityInvariantBundle`
- `serviceRestart_start_failure_preserves_serviceLifecycleCapabilityInvariantBundle`

Error-case theorems are retained for proof-surface completeness and compositional
coverage, but they do not constitute meaningful security evidence.
-/

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
    (hDenied : policyAllowsStart svc = false) :
    serviceStart sid policyAllowsStart st = .error .policyDenied := by
  exact serviceStart_error_policyDenied st sid policyAllowsStart svc hSvc hStopped hDenied

/-- Stop-policy denial branch remains a check-only outcome (no state mutation step). -/
theorem serviceStop_policyDenied_separates_check_from_mutation
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hRunning : svc.status = .running)
    (hDenied : policyAllowsStop svc = false) :
    serviceStop sid policyAllowsStop st = .error .policyDenied := by
  exact serviceStop_error_policyDenied st sid policyAllowsStop svc hSvc hRunning hDenied

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
  rcases hInv with ⟨hUnique, hSound, hAttRule, _⟩
  refine ⟨?_, ?_, hAttRule, lifecycleAuthorityMonotonicity_holds _⟩
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
      · by_cases hAllow : policyAllowsStart svc
        · by_cases hDeps : dependenciesSatisfied st sid
          · unfold storeServiceEntry at hStep
            simp [hLookup, hStopped, hAllow, hDeps, storeServiceState] at hStep
            cases hStep
            exact ⟨
              storeServiceState_preserves_servicePolicySurfaceInvariant st sid svc .running hSvc hPolicy,
              storeServiceState_preserves_lifecycleInvariantBundle st sid svc .running hLifecycle,
              storeServiceState_preserves_capabilityInvariantBundle st sid svc .running hCap
            ⟩
          · simp [hLookup, hStopped, hAllow, hDeps] at hStep
        · simp [hLookup, hStopped, hAllow] at hStep
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
      · by_cases hAllow : policyAllowsStop svc
        · unfold storeServiceEntry at hStep
          simp [hLookup, hRunning, hAllow, storeServiceState] at hStep
          cases hStep
          exact ⟨
            storeServiceState_preserves_servicePolicySurfaceInvariant st sid svc .stopped hSvc hPolicy,
            storeServiceState_preserves_lifecycleInvariantBundle st sid svc .stopped hLifecycle,
            storeServiceState_preserves_capabilityInvariantBundle st sid svc .stopped hCap
          ⟩
        · simp [hLookup, hRunning, hAllow] at hStep
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

### BFS soundness (Layer 2)
- `serviceHasPathTo_true_implies_reachable` — BFS true → declarative path
- `serviceHasPathTo_go_invariant` — BFS loop invariant
- `serviceBfsFuel_sufficient` — fuel adequacy
- `serviceHasPathTo_false_implies_not_reachable` — BFS false → no path

### Edge insertion (Layer 3)
- `serviceEdge_post_cases` — post-state edge decomposition
- `serviceReachable_post_insert_cases` — post-state path decomposition
- `nontrivial_cycle_post_insert_implies_pre_reach` — cycle → pre-state reachability
- `serviceDependencyAcyclicDecl_preserved` — declarative acyclicity preserved

### Final closure (Layer 4)
- `serviceDependencyAcyclic_implies_acyclicDecl` — BFS → declarative equivalence
- `serviceDependencyAcyclicDecl_implies_acyclic` — declarative → BFS equivalence
-/

-- ============================================================================
-- Layer 0: Declarative graph definitions
-- ============================================================================

/-- Direct dependency edge: service `a` lists `b` as a dependency. -/
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies

/-- Reflexive-transitive closure of the service dependency edge relation. -/
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl : serviceReachable st a a
  | step : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c

/-- Non-trivial path in the service dependency graph (length ≥ 1).
    Declarative analogue of `serviceHasPathTo` for self-loop detection. -/
inductive serviceNontrivialPath (st : SystemState) : ServiceId → ServiceId → Prop where
  | single : serviceEdge st a b → serviceNontrivialPath st a b
  | cons   : serviceEdge st a b → serviceNontrivialPath st b c → serviceNontrivialPath st a c

/-- The service dependency graph is acyclic: no service has a dependency chain
leading back to itself.

Risk 0 fix (WS-D4/TPI-D07): The original BFS-based definition
`∀ sid, ¬ serviceHasPathTo st sid sid fuel = true` was vacuously unsatisfiable
because `serviceHasPathTo` returns `true` immediately when `src = target`.
This declarative definition correctly captures acyclicity as the absence
of non-trivial self-loops. -/
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceNontrivialPath st sid sid

-- ============================================================================
-- Layer 1: Structural lemmas
-- ============================================================================

theorem serviceReachable_trans {st : SystemState} {a b c : ServiceId}
    (hab : serviceReachable st a b) (hbc : serviceReachable st b c) :
    serviceReachable st a c := by
  induction hab with
  | refl => exact hbc
  | step hedge _ ih => exact .step hedge (ih hbc)

theorem serviceReachable_of_edge {st : SystemState} {a b : ServiceId}
    (h : serviceEdge st a b) : serviceReachable st a b :=
  .step h .refl

theorem serviceReachable_of_nontrivialPath {st : SystemState} {a b : ServiceId}
    (h : serviceNontrivialPath st a b) : serviceReachable st a b := by
  induction h with
  | single hedge => exact serviceReachable_of_edge hedge
  | cons hedge _ ih => exact .step hedge ih

/-- Extend a single edge by a reachable suffix to form a nontrivial path.
    Proved by structural recursion on the `serviceReachable` argument. -/
theorem serviceNontrivialPath_of_edge_reachable {st : SystemState} {a b c : ServiceId}
    (hedge : serviceEdge st a b) (hreach : serviceReachable st b c) :
    serviceNontrivialPath st a c :=
  match hreach with
  | .refl => .single hedge
  | .step hedge2 htail =>
    .cons hedge (serviceNontrivialPath_of_edge_reachable hedge2 htail)

/-- A reachable pair with distinct endpoints has a nontrivial path. -/
theorem serviceNontrivialPath_of_reachable_ne {st : SystemState} {a b : ServiceId}
    (h : serviceReachable st a b) (hne : a ≠ b) : serviceNontrivialPath st a b := by
  cases h with
  | refl => exact absurd rfl hne
  | step hedge htail => exact serviceNontrivialPath_of_edge_reachable hedge htail

theorem serviceNontrivialPath_trans {st : SystemState} {a b c : ServiceId}
    (hab : serviceNontrivialPath st a b) (hbc : serviceNontrivialPath st b c) :
    serviceNontrivialPath st a c := by
  induction hab with
  | single hedge => exact .cons hedge hbc
  | cons hedge _ ih => exact .cons hedge (ih hbc)

theorem serviceNontrivialPath_step_right {st : SystemState} {a b c : ServiceId}
    (hab : serviceNontrivialPath st a b) (hbc : serviceEdge st b c) :
    serviceNontrivialPath st a c := by
  induction hab with
  | single hedge => exact .cons hedge (.single hbc)
  | cons hedge _ ih => exact .cons hedge (ih hbc)

-- ============================================================================
-- Layer 1: Frame lemmas for storeServiceState
-- ============================================================================

/-- Edge at a non-updated service is unchanged after storeServiceState. -/
theorem serviceEdge_storeServiceState_ne {st : SystemState} {svcId : ServiceId}
    {entry : ServiceGraphEntry} {a b : ServiceId} (ha : a ≠ svcId) :
    serviceEdge (storeServiceState svcId entry st) a b ↔ serviceEdge st a b := by
  constructor
  · rintro ⟨svc', hLookup, hMem⟩
    rw [storeServiceState_lookup_ne st svcId a entry ha] at hLookup
    exact ⟨svc', hLookup, hMem⟩
  · rintro ⟨svc', hLookup, hMem⟩
    rw [← storeServiceState_lookup_ne st svcId a entry ha] at hLookup
    exact ⟨svc', hLookup, hMem⟩

/-- Edge from the updated service reflects the new entry's dependencies. -/
theorem serviceEdge_storeServiceState_updated {st : SystemState} {svcId : ServiceId}
    {entry : ServiceGraphEntry} {b : ServiceId} :
    serviceEdge (storeServiceState svcId entry st) svcId b ↔ b ∈ entry.dependencies := by
  constructor
  · rintro ⟨svc', hLookup, hMem⟩
    rw [storeServiceState_lookup_eq] at hLookup
    cases hLookup
    exact hMem
  · intro hMem
    exact ⟨entry, storeServiceState_lookup_eq st svcId entry, hMem⟩

/-- Edge characterization after inserting depId into svcId's dependency list. -/
theorem serviceEdge_post_insert {st : SystemState} {svcId depId : ServiceId}
    {svc : ServiceGraphEntry} (hSvc : lookupService st svcId = some svc)
    {a b : ServiceId} :
    serviceEdge (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st) a b ↔
    ((a = svcId ∧ (b ∈ svc.dependencies ∨ b = depId)) ∨ (a ≠ svcId ∧ serviceEdge st a b)) := by
  by_cases ha : a = svcId
  · subst ha
    rw [serviceEdge_storeServiceState_updated]
    simp [List.mem_append]
  · rw [serviceEdge_storeServiceState_ne ha]
    constructor
    · intro h; exact Or.inr ⟨ha, h⟩
    · rintro (⟨hEq, _⟩ | ⟨_, h⟩)
      · exact absurd hEq ha
      · exact h

-- ============================================================================
-- Layer 2: BFS completeness bridge (TPI-D07-BRIDGE)
-- ============================================================================

-- ---- M2A: Dependency-list helper and edge bridge ----

/-- Dependency list of a service node, defaulting to [] if unregistered. -/
private def lookupDeps (st : SystemState) (nd : ServiceId) : List ServiceId :=
  match lookupService st nd with | some svc => svc.dependencies | none => []

/-- serviceEdge ↔ membership in lookupDeps. -/
private theorem serviceEdge_iff_lookupDeps {st : SystemState} {a b : ServiceId} :
    serviceEdge st a b ↔ b ∈ lookupDeps st a := by
  unfold serviceEdge lookupDeps; constructor
  · rintro ⟨svc, hL, hM⟩; rw [hL]; exact hM
  · intro h
    cases hL : lookupService st a with
    | none => simp [hL] at h
    | some svc => simp only [hL] at h; exact ⟨svc, rfl, h⟩

-- ---- M2B: Graph traversal closure invariant (WS-G8: HashSet-based) ----

/-- Traversal closure: every visited node's successors are either visited or in the frontier.
WS-G8: Visited set is `Std.HashSet ServiceId` for O(1) membership. -/
private def bfsClosed (st : SystemState) (fr : List ServiceId) (vis : Std.HashSet ServiceId) : Prop :=
  ∀ v : ServiceId, vis.contains v = true → ∀ dep : ServiceId, serviceEdge st v dep → vis.contains dep = true ∨ dep ∈ fr

/-- CB2: Initial closure (empty visited set). -/
private theorem bfsClosed_init (st : SystemState) (fr : List ServiceId) :
    bfsClosed st fr {} := by
  intro v hv; rw [HashSet_contains_empty] at hv; exact absurd hv (by decide)

/-- CB3: Skip preserves closure. -/
private theorem bfsClosed_skip {st : SystemState} {nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId}
    (hCl : bfsClosed st (nd :: rest) vis) (hVis : vis.contains nd = true) :
    bfsClosed st rest vis := by
  intro v hv dep he
  rcases hCl v hv dep he with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with heq | hr
    · subst heq; exact Or.inl hVis
    · exact Or.inr hr

/-- CB4: Expansion preserves closure.
WS-G8: Frontier is now DFS-ordered (deps ++ rest) and visited uses HashSet.insert. -/
private theorem bfsClosed_expand {st : SystemState} {nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId}
    (hCl : bfsClosed st (nd :: rest) vis) (_hNV : vis.contains nd = false) :
    bfsClosed st ((lookupDeps st nd).filter (fun d => !(vis.contains d)) ++ rest) (vis.insert nd) := by
  intro v hv dep he
  rcases (HashSet_contains_insert_iff vis nd v).mp hv with rfl | hOV
  · -- v = nd: newly expanded node
    by_cases hDV : vis.contains dep = true
    · exact Or.inl ((HashSet_contains_insert_iff vis v dep).mpr (Or.inr hDV))
    · have hDVF : vis.contains dep = false := by
        cases h : vis.contains dep with
        | false => rfl
        | true => exact absurd h hDV
      exact Or.inr (List.mem_append.mpr (Or.inl
        (List.mem_filter.mpr ⟨serviceEdge_iff_lookupDeps.mp he, by simp [hDVF]⟩)))
  · -- v ∈ old visited: successors in old vis or old frontier
    rcases hCl v hOV dep he with h | h
    · exact Or.inl ((HashSet_contains_insert_iff vis nd dep).mpr (Or.inr h))
    · rcases List.mem_cons.mp h with heq | hr
      · subst heq; exact Or.inl (HashSet_contains_insert_self vis dep)
      · exact Or.inr (List.mem_append.mpr (Or.inr hr))

/-- CB1: Boundary lemma — if a visited node reaches the target (not visited),
    some frontier node also reaches the target.
WS-G8: Visited set is HashSet. -/
private theorem bfs_boundary_lemma {st : SystemState} {tgt : ServiceId}
    {fr : List ServiceId} {vis : Std.HashSet ServiceId} {v : ServiceId}
    (hR : serviceReachable st v tgt) :
    vis.contains v = true → vis.contains tgt = false → bfsClosed st fr vis →
    ∃ f ∈ fr, serviceReachable st f tgt := by
  induction hR with
  | refl =>
    intro hV hTNV _; rw [hV] at hTNV; exact absurd hTNV (by decide)
  | step he _hr ih =>
    intro hV hTNV hCl
    rcases hCl _ hV _ he with h | h
    · exact ih h hTNV hCl
    · exact ⟨_, h, _hr⟩

-- ---- Helpers: Universe, filter length, reachability ----

/-- A "BFS universe" is a Nodup node set that contains all registered services
    and is closed under dependencies. -/
private def bfsUniverse (st : SystemState) (ns : List ServiceId) : Prop :=
  ns.Nodup ∧
  (∀ sid, lookupService st sid ≠ none → sid ∈ ns) ∧
  (∀ sid ∈ ns, ∀ dep ∈ lookupDeps st sid, dep ∈ ns)

/-- Reachable nodes stay in the universe. -/
private theorem reach_in_universe {st : SystemState} {ns : List ServiceId}
    (hU : bfsUniverse st ns) {a b : ServiceId} (ha : a ∈ ns)
    (hR : serviceReachable st a b) : b ∈ ns := by
  induction hR with
  | refl => exact ha
  | step he _ ih => exact ih (hU.2.2 _ ha _ (serviceEdge_iff_lookupDeps.mp he))

/-- Monotone filter length: stricter predicate → shorter filtered list. -/
private theorem filter_mono {α : Type} (p1 p2 : α → Bool) (xs : List α)
    (h : ∀ x, p2 x = true → p1 x = true) :
    (xs.filter p2).length ≤ (xs.filter p1).length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.filter_cons]
    by_cases hp2 : p2 x = true
    · rw [if_pos hp2, if_pos (h x hp2)]; simp only [List.length_cons]; omega
    · rw [if_neg hp2]
      by_cases hp1 : p1 x = true
      · rw [if_pos hp1]; simp only [List.length_cons]; omega
      · rw [if_neg hp1]; exact ih

/-- Strict filter decrease: if some element passes p1 but not p2. -/
private theorem filter_strict {α : Type} [DecidableEq α]
    (p1 p2 : α → Bool) (xs : List α)
    (h_sub : ∀ x, p2 x = true → p1 x = true)
    (a : α) (ha : a ∈ xs) (hp1 : p1 a = true) (hp2 : p2 a = false)
    (hNod : xs.Nodup) :
    (xs.filter p2).length < (xs.filter p1).length := by
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
    have ⟨_, hNodR⟩ := List.nodup_cons.mp hNod
    simp only [List.filter_cons]
    rcases List.mem_cons.mp ha with heq | har
    · subst heq
      rw [if_pos hp1, if_neg (by simp [hp2])]
      simp only [List.length_cons]
      exact Nat.lt_succ_of_le (filter_mono p1 p2 rest h_sub)
    · have ih' := ih har hNodR
      by_cases hp2x : p2 x = true
      · rw [if_pos hp2x, if_pos (h_sub x hp2x)]; simp only [List.length_cons]; omega
      · rw [if_neg hp2x]
        by_cases hp1x : p1 x = true
        · rw [if_pos hp1x]; simp only [List.length_cons]; omega
        · rw [if_neg hp1x]; exact ih'

/-- Adding nd to visited strictly decreases the unvisited-universe count.
WS-G8: Updated for `Std.HashSet` visited set. -/
private theorem filter_vis_decrease (ns : List ServiceId) (nd : ServiceId)
    (vis : Std.HashSet ServiceId) (hMem : nd ∈ ns) (hNV : vis.contains nd = false) (hNod : ns.Nodup) :
    (ns.filter (fun x => !((vis.insert nd).contains x))).length <
    (ns.filter (fun x => !(vis.contains x))).length :=
  filter_strict (fun x => !(vis.contains x)) (fun x => !((vis.insert nd).contains x)) ns
    (by intro x hx
        simp only [Bool.not_eq_true'] at hx ⊢
        exact ((HashSet_not_contains_insert vis nd x).mp hx).2)
    nd hMem (by simp only [hNV]; decide)
    (by simp only [HashSet_contains_insert_self vis nd]; decide) hNod

/-- If a ≠ b and a reaches b, there exists an intermediate step. -/
private theorem step_of_reachable_ne {st : SystemState} {a b : ServiceId}
    (hR : serviceReachable st a b) (hne : a ≠ b) :
    ∃ mid, serviceEdge st a mid ∧ serviceReachable st mid b := by
  cases hR with
  | refl => exact absurd rfl hne
  | step hedge htail => exact ⟨_, hedge, htail⟩

-- ---- EQ lemmas: Equational unfolding of serviceHasPathTo.go ----
-- WS-G8: Updated for HashSet visited set and DFS frontier ordering.

private theorem go_tgt_eq {st : SystemState} {tgt : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId} {f : Nat} :
    serviceHasPathTo.go st tgt (tgt :: rest) vis (f + 1) = true := by
  simp [serviceHasPathTo.go]

private theorem go_skip_eq {st : SystemState} {tgt nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId} {f : Nat}
    (hNeq : nd ≠ tgt) (hVis : vis.contains nd = true) :
    serviceHasPathTo.go st tgt (nd :: rest) vis (f + 1) =
    serviceHasPathTo.go st tgt rest vis (f + 1) := by
  simp [serviceHasPathTo.go, hNeq, hVis]

private theorem go_expand_eq {st : SystemState} {tgt nd : ServiceId}
    {rest : List ServiceId} {vis : Std.HashSet ServiceId} {f : Nat}
    (hNeq : nd ≠ tgt) (hNV : vis.contains nd = false) :
    serviceHasPathTo.go st tgt (nd :: rest) vis (f + 1) =
    serviceHasPathTo.go st tgt
      ((lookupDeps st nd).filter (fun d => !(vis.contains d)) ++ rest)
      (vis.insert nd) f := by
  simp only [serviceHasPathTo.go, hNeq, ite_false]
  simp only [Bool.eq_false_iff] at hNV
  simp only [hNV]
  unfold lookupDeps; rfl

-- ---- CP1: Core graph traversal completeness ----
-- WS-G8: Updated for HashSet visited set and DFS frontier ordering.

set_option maxHeartbeats 800000 in
/-- Core completeness: if the frontier contains a node that can reach the target,
    and we have enough fuel, the traversal returns true.
WS-G8: Visited set is `Std.HashSet ServiceId`. Frontier is DFS-ordered. -/
private theorem go_complete
    (st : SystemState) (tgt : ServiceId)
    (fr : List ServiceId) (vis : Std.HashSet ServiceId) (fuel : Nat)
    (ns : List ServiceId)
    (hU : bfsUniverse st ns) (hTV : vis.contains tgt = false) (hCl : bfsClosed st fr vis)
    (hR : ∃ w ∈ fr, serviceReachable st w tgt)
    (hFB : ∀ x ∈ fr, x ∈ ns)
    (hFuel : (ns.filter (fun x => !(vis.contains x))).length ≤ fuel) :
    serviceHasPathTo.go st tgt fr vis fuel = true := by
  induction fuel using Nat.strongRecOn generalizing fr vis with
  | _ fuel ih_fuel =>
    induction fr generalizing vis with
    | nil => obtain ⟨w, hwM, _⟩ := hR; exact absurd hwM List.not_mem_nil
    | cons nd rest ih_fr =>
      obtain ⟨w, hwM, hwR⟩ := hR
      have htNs := reach_in_universe hU (hFB w hwM) hwR
      have htFilt : tgt ∈ ns.filter (fun x => !(vis.contains x)) := by
        rw [List.mem_filter]; exact ⟨htNs, by simp [hTV]⟩
      have hFP : 0 < (ns.filter (fun x => !(vis.contains x))).length := List.length_pos_of_mem htFilt
      obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      by_cases hEq : nd = tgt
      · subst hEq; exact go_tgt_eq
      · by_cases hVis : vis.contains nd = true
        · -- Skip case
          rw [go_skip_eq hEq hVis]
          have hClR := bfsClosed_skip hCl hVis
          have hRR : ∃ f ∈ rest, serviceReachable st f tgt := by
            rcases List.mem_cons.mp hwM with heq | hw
            · subst heq; exact bfs_boundary_lemma hwR hVis hTV hClR
            · exact ⟨w, hw, hwR⟩
          exact ih_fr vis hTV hClR hRR
            (fun x hx => hFB x (List.mem_cons_of_mem nd hx)) hFuel
        · -- Expand case
          have hVisBool : vis.contains nd = false := by
            cases h : vis.contains nd with
            | false => rfl
            | true => exact absurd h hVis
          rw [go_expand_eq hEq hVisBool]
          have hNdNs := hFB nd List.mem_cons_self
          have hFuelDec := filter_vis_decrease ns nd vis hNdNs hVisBool hU.1
          apply ih_fuel fuel' (by omega)
          · -- tgt ∉ vis.insert nd
            rw [Std.HashSet.contains_insert]
            simp only [Bool.or_eq_false_iff]
            exact ⟨by cases h : (nd == tgt) <;> simp_all, hTV⟩
          · exact bfsClosed_expand hCl hVisBool
          · rcases List.mem_cons.mp hwM with heq | hw
            · rw [heq] at hwR
              obtain ⟨mid, hedge, htail⟩ := step_of_reachable_ne hwR hEq
              have hMidDeps : mid ∈ lookupDeps st nd :=
                serviceEdge_iff_lookupDeps.mp hedge
              by_cases hMidVis : vis.contains mid = true
              · have hClE := bfsClosed_expand hCl hVisBool
                have hMidNewVis : (vis.insert nd).contains mid = true :=
                  (HashSet_contains_insert_iff vis nd mid).mpr (Or.inr hMidVis)
                have hTgtNewVis : (vis.insert nd).contains tgt = false := by
                  rw [Std.HashSet.contains_insert]
                  simp only [Bool.or_eq_false_iff]
                  exact ⟨by cases h : (nd == tgt) <;> simp_all, hTV⟩
                exact bfs_boundary_lemma htail hMidNewVis hTgtNewVis hClE
              · have hMidVisBool : vis.contains mid = false := by
                  cases h : vis.contains mid with
                  | false => rfl
                  | true => exact absurd h hMidVis
                exact ⟨mid,
                  List.mem_append.mpr (Or.inl
                    (List.mem_filter.mpr ⟨hMidDeps, by simp [hMidVisBool]⟩)),
                  htail⟩
            · exact ⟨w, List.mem_append.mpr (Or.inr hw), hwR⟩
          · intro x hx
            rcases List.mem_append.mp hx with hxd | hxr
            · exact hU.2.2 nd hNdNs x (List.mem_filter.mp hxd).1
            · exact hFB x (List.mem_cons_of_mem nd hxr)
          · omega

/-- State-level bound: a traversal universe exists within the fuel budget.
    This is a precondition for the completeness bridge. -/
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ ns : List ServiceId,
    bfsUniverse st ns ∧ ns.length ≤ serviceBfsFuel st

/-- The source of a nontrivial path is a registered service. -/
private theorem registered_of_nontrivialPath_src {st : SystemState} {a b : ServiceId}
    (h : serviceNontrivialPath st a b) : lookupService st a ≠ none := by
  cases h with
  | single hedge => obtain ⟨svc, hL, _⟩ := hedge; simp [hL]
  | cons hedge _ => obtain ⟨svc, hL, _⟩ := hedge; simp [hL]

/-- Graph traversal completeness bridge: a nontrivial path between distinct services
is detected by `serviceHasPathTo` with `serviceBfsFuel` fuel.

This connects the declarative path relation to the executable graph traversal check
used in `serviceRegisterDependency`. Completeness is established by a formal
loop-invariant argument (M2/TPI-D07-BRIDGE): the traversal maintains a closure
invariant on the visited set, and a decreasing measure on the unvisited universe
nodes ensures termination with the correct result.

WS-G8: Visited set is `Std.HashSet ServiceId` (O(1) membership). Traversal
order is DFS (prepend) instead of BFS (append). Cycle detection correctness is
order-independent.

The `serviceCountBounded` hypothesis ensures that the set of reachable service
nodes fits within the fuel budget. -/
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b)
    (hBound : serviceCountBounded st) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  obtain ⟨ns, hU, hLen⟩ := hBound
  have haSrc := registered_of_nontrivialPath_src hPath
  have haInNs := hU.2.1 a haSrc
  apply go_complete st b [a] {} (serviceBfsFuel st) ns hU
  · exact HashSet_contains_empty
  · exact bfsClosed_init st [a]
  · exact ⟨a, List.mem_cons_self, serviceReachable_of_nontrivialPath hPath⟩
  · intro x hx; rcases List.mem_cons.mp hx with heq | h
    · subst heq; exact haInNs
    · exact absurd h List.not_mem_nil
  · -- fuel: ns.filter (fun x => !(({} : HashSet).contains x)).length ≤ serviceBfsFuel st
    -- Since empty.contains is always false, filter keeps all elements
    have hFiltId : ns.filter (fun x => !(({} : Std.HashSet ServiceId).contains x)) = ns := by
      rw [List.filter_eq_self]
      intro x _
      simp only [HashSet_contains_empty, Bool.not_false]
    rw [hFiltId]; exact hLen

-- ============================================================================
-- Layer 3: Post-insertion nontrivial path decomposition
-- ============================================================================

/-- Any nontrivial path in the post-insertion state either:
(1) consists entirely of pre-state edges, or
(2) uses the new svcId → depId edge, yielding pre-state reachability
    from the source to svcId and from depId to the target. -/
theorem nontrivialPath_post_insert_cases
    {st : SystemState} {svcId depId : ServiceId}
    {svc : ServiceGraphEntry} (hSvc : lookupService st svcId = some svc)
    {a b : ServiceId}
    (hPath : serviceNontrivialPath
      (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st) a b) :
    serviceNontrivialPath st a b ∨
    (serviceReachable st a svcId ∧ serviceReachable st depId b) := by
  induction hPath with
  | single hedge =>
    rcases (serviceEdge_post_insert hSvc).mp hedge with ⟨rfl, hOr⟩ | ⟨hNe, hOld⟩
    · rcases hOr with hOld | rfl
      · -- Old edge from svcId
        exact Or.inl (.single ⟨svc, hSvc, hOld⟩)
      · -- New edge: svcId → depId
        exact Or.inr ⟨.refl, .refl⟩
    · exact Or.inl (.single hOld)
  | cons hedge _ ih =>
    rcases (serviceEdge_post_insert hSvc).mp hedge with ⟨rfl, hOr⟩ | ⟨hNe, hOld⟩
    · rcases hOr with hOld | rfl
      · -- Old edge from svcId → mid, then path mid →+ b
        rcases ih with hPre | ⟨hReach1, hReach2⟩
        · exact Or.inl (.cons ⟨svc, hSvc, hOld⟩ hPre)
        · exact Or.inr ⟨.refl, hReach2⟩
      · -- New edge: svcId → depId, then path depId →+ b
        rcases ih with hPre | ⟨_, hReach2⟩
        · exact Or.inr ⟨.refl, serviceReachable_of_nontrivialPath hPre⟩
        · exact Or.inr ⟨.refl, hReach2⟩
    · -- Old edge from a → mid (a ≠ svcId), then path mid →+ b
      rcases ih with hPre | ⟨hReach1, hReach2⟩
      · exact Or.inl (.cons hOld hPre)
      · exact Or.inr ⟨.step hOld hReach1, hReach2⟩

-- ============================================================================
-- Layer 4: Acyclicity preservation (TPI-D07 closure)
-- ============================================================================

/-- After a successful dependency registration, the dependency graph remains acyclic.

The `serviceRegisterDependency` function checks whether `depId` can reach
`svcId` through existing edges before adding `svcId → depId`. If the check
finds a path, it returns `cyclicDependency`. On success, no path existed,
so adding the edge preserves acyclicity.

Risk 0 resolution (WS-D4/TPI-D07): The vacuous BFS-based invariant has been
replaced with a declarative acyclicity definition. The preservation proof is
genuine — it proceeds by post-insertion path decomposition and derives a
contradiction from the BFS cycle-detection check. BFS completeness
(`bfs_complete_for_nontrivialPath`) is now formally proved (M2/TPI-D07-BRIDGE),
contingent on `serviceCountBounded`, which asserts that the set of reachable
service nodes fits within the BFS fuel budget. -/
theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st)
    (hBound : serviceCountBounded st) :
    serviceDependencyAcyclic st' := by
  unfold serviceRegisterDependency at hReg
  cases hSvc : lookupService st svcId with
  | none => simp [hSvc] at hReg
  | some svc =>
    simp only [hSvc] at hReg
    cases hDep : lookupService st depId with
    | none => simp [hDep] at hReg
    | some depSvc =>
      simp only [hDep] at hReg
      by_cases hSelf : svcId = depId
      · simp [hSelf] at hReg
      · simp only [hSelf, ite_false] at hReg
        by_cases hExists : depId ∈ svc.dependencies
        · -- Idempotent: st' = st
          simp [hExists] at hReg
          cases hReg
          exact hAcyc
        · simp only [hExists, ite_false] at hReg
          by_cases hCycle : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
          · simp [hCycle] at hReg
          · simp only [hCycle] at hReg
            unfold storeServiceEntry at hReg
            simp at hReg
            cases hReg
            -- Goal: serviceDependencyAcyclic (storeServiceState svcId {svc with ...} st)
            -- Strategy: suppose a post-state cycle, decompose, derive contradiction
            intro sid hCycleSid
            rcases nontrivialPath_post_insert_cases hSvc hCycleSid with hPre | ⟨hReach1, hReach2⟩
            · -- Case 1: cycle uses only old edges → pre-state cycle
              exact hAcyc sid hPre
            · -- Case 2: cycle uses new edge → pre-state path depId →* svcId
              -- Compose: depId →* sid →* svcId via serviceReachable_trans
              have hDepSvc : serviceReachable st depId svcId :=
                serviceReachable_trans hReach2 hReach1
              -- Since svcId ≠ depId, this reachability is nontrivial
              have hNontrivial : serviceNontrivialPath st depId svcId :=
                serviceNontrivialPath_of_reachable_ne hDepSvc (Ne.symm hSelf)
              -- BFS completeness: nontrivial path + bounded universe → BFS returns true
              have hBfsTrue : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true :=
                bfs_complete_for_nontrivialPath hNontrivial (Ne.symm hSelf) hBound
              -- Contradiction with the BFS check that returned false
              exact absurd hBfsTrue hCycle

-- ============================================================================
-- F-11: serviceRestart failure-semantics documentation and proof (WS-D4)
-- ============================================================================

/-- Failure-semantics guarantee: on error, the `Kernel` monad returns only the
error variant — no intermediate state is accessible to the caller, so the
pre-restart invariant is trivially preserved (the state is unchanged from the
caller's perspective). -/
theorem serviceRestart_error_discards_state
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (_hErr : serviceRestart sid policyAllowsStop policyAllowsStart st = .error e)
    (hInv : serviceLifecycleCapabilityInvariantBundle st) :
    serviceLifecycleCapabilityInvariantBundle st :=
  hInv

/-- Functional decomposition: when restart returns error despite successful stop,
the error originated from the start phase. -/
theorem serviceRestart_error_from_start_phase
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (hNotStopErr : ∃ stStopped, serviceStop sid policyAllowsStop st = .ok ((), stStopped))
    (hErr : serviceRestart sid policyAllowsStop policyAllowsStart st = .error e) :
    ∃ stStopped,
      serviceStop sid policyAllowsStop st = .ok ((), stStopped) ∧
      serviceStart sid policyAllowsStart stStopped = .error e := by
  unfold serviceRestart at hErr
  rcases hNotStopErr with ⟨stStopped, hStop⟩
  simp only [hStop] at hErr
  exact ⟨stStopped, hStop, hErr⟩

-- ============================================================================
-- H-08/WS-E3: BFS soundness in Service/Invariant context
-- ============================================================================

/-- H-08/WS-E3: BFS conservatively reports a path when fuel is exhausted.
Under the zero-fuel base case the BFS returns `true`, preventing any
dependency registration when the fuel budget is insufficient. -/
theorem serviceHasPathTo_fuel_zero (st : SystemState) (src target : ServiceId) :
    serviceHasPathTo st src target 0 = true := by
  simp [serviceHasPathTo, serviceHasPathTo.go]

/-- H-08/WS-E3 adequacy: when BFS returns `false`, there genuinely is no
nontrivial path from `a` to `b`. This is the soundness direction —
the contrapositive of `bfs_complete_for_nontrivialPath`. -/
theorem bfs_false_implies_no_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hBfs : serviceHasPathTo st a b (serviceBfsFuel st) = false)
    (hNe : a ≠ b)
    (hBound : serviceCountBounded st) :
    ¬ serviceNontrivialPath st a b := by
  intro hPath
  have hTrue := bfs_complete_for_nontrivialPath hPath hNe hBound
  rw [hTrue] at hBfs
  cases hBfs

-- ============================================================================
-- WS-F3: Service operation frame lemmas for information-flow proofs
-- ============================================================================

/-- WS-F3: serviceStart preserves the object store. -/
theorem serviceStart_preserves_objects
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStart preserves the scheduler. -/
theorem serviceStart_preserves_scheduler
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStart preserves IRQ handler mappings. -/
theorem serviceStart_preserves_irqHandlers
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStart preserves the object index. -/
theorem serviceStart_preserves_objectIndex
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStart preserves lookup for other services. -/
theorem serviceStart_preserves_lookupService_ne
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (s : ServiceId) (hNe : s ≠ sid)
    (hStep : serviceStart sid policy st = .ok ((), st')) :
    lookupService st' s = lookupService st s := by
  unfold serviceStart at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep
      simp [lookupService, hNe]

/-- WS-F3: serviceStop preserves the object store. -/
theorem serviceStop_preserves_objects
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStop preserves the scheduler. -/
theorem serviceStop_preserves_scheduler
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStop preserves IRQ handler mappings. -/
theorem serviceStop_preserves_irqHandlers
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStop preserves the object index. -/
theorem serviceStop_preserves_objectIndex
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep; rfl

/-- WS-F3: serviceStop preserves lookup for other services. -/
theorem serviceStop_preserves_lookupService_ne
    (st st' : SystemState) (sid : ServiceId) (policy : ServicePolicy)
    (s : ServiceId) (hNe : s ≠ sid)
    (hStep : serviceStop sid policy st = .ok ((), st')) :
    lookupService st' s = lookupService st s := by
  unfold serviceStop at hStep
  cases hLookup : lookupService st sid with
  | none => simp [hLookup] at hStep
  | some svc =>
      simp [hLookup] at hStep
      split at hStep <;> try (simp at hStep)
      split at hStep <;> try (simp at hStep)
      unfold storeServiceEntry storeServiceState at hStep; simp at hStep; cases hStep
      simp [lookupService, hNe]

/-- WS-F3: serviceRestart decomposes into stop + start. -/
theorem serviceRestart_decompose
    (st st' : SystemState) (sid : ServiceId)
    (policyStop policyStart : ServicePolicy)
    (hStep : serviceRestart sid policyStop policyStart st = .ok ((), st')) :
    ∃ mid, serviceStop sid policyStop st = .ok ((), mid) ∧
           serviceStart sid policyStart mid = .ok ((), st') := by
  unfold serviceRestart at hStep
  cases hStop : serviceStop sid policyStop st with
  | error e => simp [hStop] at hStep
  | ok pair =>
      simp only [hStop] at hStep
      refine ⟨pair.2, ?_, hStep⟩
      have : pair = ((), pair.2) := Prod.ext (Subsingleton.elim _ _) rfl
      rw [this] at hStop

end SeLe4n.Kernel
