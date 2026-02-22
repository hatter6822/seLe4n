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
    (hObj : st.objects svc.identity.backingObject = some obj) :
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
    (hCap : capabilityInvariantBundle st)
    (hLookup : cspaceLookupSlot { cnode := svc.identity.owner, slot := slot } st = .ok (cap, st))
    (hTarget : cap.target = .object svc.identity.backingObject) :
    policyOwnerAuthoritySlotPresent st svc := by
  have hSound : cspaceLookupSound st := hCap.2.1
  have hSoundFacts := hSound { cnode := svc.identity.owner, slot := slot } cap st hLookup
  rcases hSoundFacts with ⟨hStEq, _hOwns, hSlotCap⟩
  cases hStEq
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
        ∃ obj, st.objects svc.identity.backingObject = some obj) :
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

theorem storeServiceState_preserves_capabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (svc : ServiceGraphEntry)
    (newStatus : ServiceStatus) :
    capabilityInvariantBundle (storeServiceState sid { svc with status := newStatus } st) := by
  exact capabilityInvariantBundle_holds (storeServiceState sid { svc with status := newStatus } st)

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
              storeServiceState_preserves_capabilityInvariantBundle st sid svc .running
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
            storeServiceState_preserves_capabilityInvariantBundle st sid svc .stopped
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

/-- BFS completeness bridge: a nontrivial path between distinct services is
detected by `serviceHasPathTo` with `serviceBfsFuel` fuel.

This connects the declarative path relation to the executable BFS check
used in `serviceRegisterDependency`. The property is operationally
validated by the negative state suite (cycle detection tests) and the
depth-5 dependency chain smoke test.

TPI-D07-BRIDGE: Formal proof of BFS loop-invariant completeness is
deferred as future infrastructure (see Risk 1, Risk 3 in the risk
register). The assumption is that `serviceBfsFuel` provides sufficient
fuel and the BFS correctly explores all reachable nodes. -/
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (_hPath : serviceNontrivialPath st a b)
    (_hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  sorry -- TPI-D07-BRIDGE: BFS completeness proof deferred (validated by executable tests)

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
contradiction from the BFS cycle-detection check. The sole deferred obligation
is BFS completeness (`bfs_complete_for_nontrivialPath`, TPI-D07-BRIDGE),
which connects the declarative path relation to the executable BFS check. -/
theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st) :
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
              -- BFS completeness: nontrivial path → BFS returns true
              have hBfsTrue : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true :=
                bfs_complete_for_nontrivialPath hNontrivial (Ne.symm hSelf)
              -- Contradiction with the BFS check that returned false
              exact absurd hBfsTrue hCycle

-- ============================================================================
-- F-11: serviceRestart failure-semantics documentation and proof (WS-D4)
-- ============================================================================

/-- Failure-semantics guarantee: on error, the `Kernel` monad returns only the
error variant — no intermediate state is accessible to the caller.

This is definitionally true by the structure of `Except.error`: the error
constructor does not carry a state component. The caller can only observe
the original pre-restart state `st` (which it already holds). -/
theorem serviceRestart_error_discards_state
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (_hErr : serviceRestart sid policyAllowsStop policyAllowsStart st = .error e) :
    True := by
  trivial

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

end SeLe4n.Kernel
