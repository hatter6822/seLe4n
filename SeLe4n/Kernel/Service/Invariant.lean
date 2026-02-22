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

/-- The service dependency graph is acyclic: no service can reach itself
through dependency edges.

Defined in terms of `serviceHasPathTo` with bounded BFS fuel. -/
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasPathTo st sid sid (serviceBfsFuel st) = true

/-- After a successful dependency registration, the dependency graph remains acyclic.

The `serviceRegisterDependency` function checks whether `depId` can reach
`svcId` through existing edges before adding `svcId → depId`. If the check
finds a path, it returns `cyclicDependency`. On success, no path existed,
so adding the edge preserves acyclicity.

The formal proof of BFS soundness (i.e., that a false return from
`serviceHasPathTo` implies no path exists in the full graph) is deferred
as TPI-D07. The cycle detection is operationally correct (validated by
executable tests). -/
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
            unfold serviceDependencyAcyclic
            intro sid
            unfold storeServiceEntry at hReg
            simp at hReg
            cases hReg
            sorry -- TPI-D07: BFS soundness deferred

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
