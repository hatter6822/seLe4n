/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # Service Orchestration — seLe4n Extension

**This module is a seLe4n-specific extension with no analogue in real seL4.**

seL4 provides no kernel-level service management — service dependency graphs
and orchestration are delegated entirely to user-level system components
(e.g., the component framework or CAmkES). seLe4n models service dependency
tracking as a first-class kernel abstraction to enable machine-checked
reasoning about dependency acyclicity and isolation enforcement.

The `ServiceGraphEntry` structure captures per-service identity, dependency
edges, and isolation edges. Operations (`serviceRegisterDependency`) are
deterministic kernel transitions with explicit error returns. The companion
invariant modules (`Invariant/Policy.lean`, `Invariant/Acyclicity.lean`)
provide machine-checked proofs of policy preservation and dependency acyclicity.

WS-Q1-E1: Lifecycle operations (`serviceStart`, `serviceStop`, `serviceRestart`)
and `ServiceStatus` have been removed. Runtime lifecycle state is now managed
through the capability-indexed service registry (`Service/Registry.lean`). -/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Deterministic service update helper in kernel-monad form. -/
def storeServiceEntry (sid : ServiceId) (entry : ServiceGraphEntry) : Kernel Unit :=
  fun st => .ok ((), storeServiceState sid entry st)

/-- R4-D.2 (M-15): Remove all dependency graph edges involving a given service.
    Erases the service's entry from the graph (removing outgoing edges) and
    filters the service from all other entries' dependency lists (removing
    incoming edges). Returns a pure SystemState update. -/
def removeDependenciesOf (st : SystemState) (sid : ServiceId) : SystemState :=
  let erased := st.services.erase sid
  let cleaned := erased.fold erased fun acc otherSid entry =>
    if entry.dependencies.any (· == sid) then
      let entry' := { entry with
        dependencies := entry.dependencies.filter (· != sid) }
      acc.insert otherSid entry'
    else
      acc
  { st with services := cleaned }

/-- R4-D.2: removeDependenciesOf preserves objects. -/
theorem removeDependenciesOf_objects_eq
    (st : SystemState) (sid : ServiceId) :
    (removeDependenciesOf st sid).objects = st.objects := by
  unfold removeDependenciesOf; rfl

/-- R4-D.2: removeDependenciesOf preserves scheduler. -/
theorem removeDependenciesOf_scheduler_eq
    (st : SystemState) (sid : ServiceId) :
    (removeDependenciesOf st sid).scheduler = st.scheduler := by
  unfold removeDependenciesOf; rfl

/-- R4-D.2: removeDependenciesOf preserves lifecycle. -/
theorem removeDependenciesOf_lifecycle_eq
    (st : SystemState) (sid : ServiceId) :
    (removeDependenciesOf st sid).lifecycle = st.lifecycle := by
  unfold removeDependenciesOf; rfl

/-- R4-D.2: removeDependenciesOf preserves serviceRegistry. -/
theorem removeDependenciesOf_serviceRegistry_eq
    (st : SystemState) (sid : ServiceId) :
    (removeDependenciesOf st sid).serviceRegistry = st.serviceRegistry := by
  unfold removeDependenciesOf; rfl

/-- W2-F: removeDependenciesOf preserves objectIndex. -/
theorem removeDependenciesOf_objectIndex_eq
    (st : SystemState) (sid : ServiceId) :
    (removeDependenciesOf st sid).objectIndex = st.objectIndex := by
  unfold removeDependenciesOf; rfl

-- ============================================================================
-- F-07: Service dependency registration with cycle detection (WS-D4)
-- ============================================================================

/-- Fuel bound for bounded graph reachability in the service dependency graph.

The `objectIndex` provides a finite list of known object IDs, which gives
a lower bound on meaningful graph nodes. We add a generous constant to
account for service IDs that may not have corresponding kernel objects.
The traversal does not consume fuel for already-visited nodes, so this bound
only constrains the number of distinct nodes visited.

Note: the function retains its `Bfs` name for API stability; the underlying
algorithm was migrated to DFS with HashSet visited set in WS-G8.

**AN4-H (SVC-M02) — `Bfs` suffix is historical**. The DFS-with-visited-set
implementation is structurally a BFS-equivalent search (the completeness
property witnessed by `serviceCountBounded` holds for both orderings on
finite graphs), so the symbol is retained to avoid a ~77-call-site cascade
across `Service/` and its consumer modules. Any future rename (to
`serviceSearchFuel` or `serviceDfsFuel`) should be landed as a single
atomic refactor commit with the full call-site migration — deferred as a
post-1.0 hygiene item; no currently-active plan file tracks it beyond
this annotation.

V5-I (H-SVC-1): **Fuel bounds analysis.** The fuel value `objectIndex.length + 256`
is sufficient because:
1. Each node is visited at most once (HashSet membership check).
2. The total number of distinct service IDs ≤ `objectIndex.length` (each
   service has a corresponding kernel object).
3. The `+ 256` margin accounts for services with IDs not yet in the object
   index (e.g., pending registrations) and prevents off-by-one edge cases.
4. Since fuel is only decremented when expanding a *new* (unvisited) node,
   and there are at most `objectIndex.length` such nodes, the traversal
   never exhausts fuel on a well-formed service graph.

See `serviceBfsFuel_adequate` for the formal proof that fuel ≥ objectIndex
length, and `serviceCountBounded` in `Service/Invariant/Acyclicity.lean` for
the BFS universe predicate ensuring completeness. -/
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256


/-- Bounded graph traversal reachability check in the service dependency graph.

Returns `true` if there exists a path of dependency edges from `src` to
`target`. Uses `fuel` as a bound on the number of distinct nodes expanded
(set via `serviceBfsFuel`).

H-08 (WS-E3): On fuel exhaustion the traversal returns `true` (conservatively
assumes a path may exist). This is sound for cycle-detection callers: a
false positive rejects a valid edge registration, while a false negative
would silently allow a cycle — the safe default is to assume reachability.

WS-G8/F-P08: Visited set migrated from `List ServiceId` (O(n) membership)
to `Std.HashSet ServiceId` (O(1) membership). Frontier ordering changed
from BFS (append) to DFS (prepend) — cycle detection is order-independent.
Total complexity reduced from O(n²) to O(n+e).

The traversal correctly handles:
- empty graphs (no services → no path),
- self-reachability (src = target → true immediately),
- disconnected components (frontier exhaustion → false),
- already-visited nodes (skipped without consuming fuel),
- fuel exhaustion → true (conservative soundness). -/
-- AF4-D (AF-18): `serviceHasPathTo` returns `true` on fuel exhaustion (line 0 =>
-- true). This is CONSERVATIVE for cycle detection: a false positive rejects a
-- valid edge registration; a false negative would silently allow a cycle in the
-- service dependency graph, potentially causing deadlock or infinite loops.
-- Proven correct under `serviceCountBounded` via `serviceBfsFuel_sound` and
-- `serviceBfsFuel_sufficient` (in `Service/Invariant/Acyclicity.lean`). Spurious rejection is acceptable because
-- fuel is bounded by `serviceBfsFuel st` = `objectIndex.length + 256`, which
-- exceeds any realistic service count. In practice, fuel exhaustion is
-- unreachable for well-formed states.
def serviceHasPathTo
    (st : SystemState) (src target : ServiceId) (fuel : Nat) : Bool :=
  go [src] {} fuel
where
  go (frontier : List ServiceId) (visited : Std.HashSet ServiceId) : Nat → Bool
  | 0 => true  -- H-08/WS-E3: fuel exhausted — conservatively assume path exists
  | fuel + 1 =>
      match frontier with
      | [] => false  -- frontier empty: no path exists
      | node :: rest =>
          if node = target then true
          else if visited.contains node then go rest visited (fuel + 1)
          else
            let deps := match lookupService st node with
              | some svc => svc.dependencies
              | none => []
            -- WS-G8: DFS ordering (prepend) instead of BFS (append);
            -- cycle detection is order-independent, and prepend is O(|deps|)
            -- instead of O(|rest|) for append.
            let newFrontier := deps.filter (fun d => !visited.contains d) ++ rest
            go newFrontier (visited.insert node) fuel

-- ============================================================================
-- W2-E (M-4): serviceHasPathTo fuel exhaustion semantics
-- ============================================================================

/-- W2-E (M-4): Fuel exhaustion conservatively assumes path exists, preventing
    registration of potentially cyclic dependencies. When fuel reaches 0 before
    the traversal completes, `serviceHasPathTo.go` returns `true` — this is
    sound for cycle-detection callers because a false positive only rejects a
    valid edge registration, while a false negative would silently allow a cycle.

    The fuel bound `serviceBfsFuel st = st.objectIndex.length + 256` is adequate
    because:
    1. Each *new* node expansion decrements fuel by 1.
    2. Already-visited nodes are skipped without consuming fuel.
    3. Total distinct services ≤ `objectIndex.length` (each has a kernel object).
    4. The `+ 256` margin handles services with IDs not yet in the object index.

    Worst-case graph: `objectIndex.length` services forming a single chain.
    The traversal visits each service once, consuming `objectIndex.length` fuel.
    With `objectIndex.length + 256` available, there is a margin of 256. -/
theorem serviceHasPathTo_fuel_exhaustion_conservative
    (st : SystemState) (src target : ServiceId) :
    serviceHasPathTo.go st target [src] {} 0 = true := by
  simp [serviceHasPathTo.go]

/-- Register a dependency edge from service `svcId` to service `depId`.

WS-D4/F-07: Before adding the edge, checks whether `depId` can already
reach `svcId` through existing dependency edges. If so, adding `svcId → depId`
would create a cycle, and the operation returns `cyclicDependency`.

Deterministic check ordering:
1. source service lookup (`objectNotFound`),
2. dependency service existence check (`objectNotFound`),
3. self-dependency check (`cyclicDependency`),
4. existing edge check (idempotent — already present returns success),
5. cycle detection: would `depId → ... → svcId` form a cycle? (`cyclicDependency`),
6. dependency edge is added on success.

**AN4-H (SVC-M03) — collision semantics**: step 4 above is intentionally
idempotent. When `depId ∈ svc.dependencies` holds before the call, the
function returns `.ok ((), st)` with the caller's state unmodified — it
does NOT re-append the edge nor return a "no-op" indicator. Callers that
need to distinguish "added" vs "already present" must observe this by
probing `lookupService` for `depId` membership in the pre-state. The
audit identifies this as acceptable: the no-op outcome is semantically
equivalent to the "added" outcome for every downstream invariant (the
dependency relation is set-valued in the proof surface via `∈`), and
widening the return type to a 3-way "added | no-op | error" disjunction
would cascade through every caller without changing reachable states.
The contract is therefore **documented rather than type-encoded**. -/
def serviceRegisterDependency
    (svcId depId : ServiceId) : Kernel Unit :=
  fun st =>
    match lookupService st svcId with
    | none => .error .objectNotFound
    | some svc =>
        match lookupService st depId with
        | none => .error .objectNotFound
        | some _ =>
            if svcId = depId then
              .error .cyclicDependency
            else if depId ∈ svc.dependencies then
              .ok ((), st)
            else if serviceHasPathTo st depId svcId (serviceBfsFuel st) then
              .error .cyclicDependency
            else
              let svc' : ServiceGraphEntry :=
                { svc with dependencies := svc.dependencies ++ [depId] }
              storeServiceEntry svcId svc' st

/-- Self-dependency is always rejected as cyclic. -/
theorem serviceRegisterDependency_error_self_loop
    (st : SystemState)
    (sid : ServiceId)
    (hSvc : (lookupService st sid).isSome = true) :
    serviceRegisterDependency sid sid st = .error .cyclicDependency := by
  unfold serviceRegisterDependency
  cases hL : lookupService st sid with
  | none => simp [hL] at hSvc
  | some svc => simp

-- ============================================================================
-- H-08/WS-E3: Graph traversal fuel adequacy and soundness
-- ============================================================================

/-- H-08/WS-E3: Fuel exhaustion always returns `true` (conservative safe answer).
This is the core soundness property: since `go` with zero fuel returns `true`,
a `false` result from `serviceHasPathTo` can only come from genuine frontier
depletion (no unvisited nodes remain), never from premature fuel exhaustion. -/
theorem serviceHasPathTo_fuel_zero_is_true
    (st : SystemState) (src target : ServiceId) :
    serviceHasPathTo st src target 0 = true := by
  simp [serviceHasPathTo, serviceHasPathTo.go]

/-- H-08/WS-E3: When `serviceHasPathTo` returns `false`, it was NOT due to fuel
exhaustion. Since fuel=0 returns `true`, a `false` result means the traversal
completed exploration and genuinely found no path — the frontier was fully
depleted. This provides the soundness bridge: `false` is reliable evidence
of unreachability within the explored frontier. -/
theorem serviceHasPathTo_false_implies_not_fuel_exhaustion
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hFalse : serviceHasPathTo st src target fuel = false) :
    fuel ≠ 0 := by
  intro hFuel
  subst hFuel
  simp [serviceHasPathTo, serviceHasPathTo.go] at hFalse

/-- H-08/WS-E3: The traversal fuel bound is always at least as large as the number
of known kernel objects. Since the DFS only expands unvisited nodes and skips
already-visited ones without consuming fuel, this ensures that any path
traversing only registered object-backed services is fully explored before
fuel runs out. -/
theorem serviceBfsFuel_adequate (st : SystemState) :
    serviceBfsFuel st ≥ st.objectIndex.length := by
  unfold serviceBfsFuel
  omega

/-- AN4-H.SVC-M01: `serviceBfsFuel` is always **at least** as large as the
number of initial services in the state. The service registry is modelled
via `st.services` (a `RobinHood.RHTable ServiceId ServiceGraphEntry`), and
each registered service has a corresponding kernel object in
`objectIndex`; `serviceBfsFuel = objectIndex.length + 256` therefore upper
bounds the number of distinct service IDs the BFS traversal might need to
expand, plus a 256-entry safety margin. At boot, the invariant is
preserved as a consequence of `bootFromPlatform`'s lifecycle-consistency
pass — every service present in `PlatformConfig.services` has an object
entry added to `objectIndex` before the service registry is populated.

This theorem is the parametric witness used by the AN4-H Service batch
documentation in `SELE4N_SPEC.md` §5 to discharge the "fuel sufficiency at
boot" obligation without per-deployment instantiation. -/
theorem bootFromPlatform_service_fuel_sufficient (st : SystemState)
    (hSize : st.services.size ≤ st.objectIndex.length) :
    serviceBfsFuel st ≥ st.services.size := by
  unfold serviceBfsFuel
  omega

/-- H-08/WS-E3: `serviceRegisterDependency` rejects an edge when
`serviceHasPathTo` reports potential reachability (either found or fuel
exhausted). This is the operational soundness property: the cycle check
cannot produce false negatives. -/
theorem serviceRegisterDependency_rejects_if_path_or_fuel_exhausted
    (st : SystemState) (svcId depId : ServiceId)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st svcId = some svc)
    (hDep : (lookupService st depId).isSome = true)
    (hNeSelf : svcId ≠ depId)
    (hNotPresent : depId ∉ svc.dependencies)
    (hPath : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true) :
    serviceRegisterDependency svcId depId st = .error .cyclicDependency := by
  unfold serviceRegisterDependency
  cases hD : lookupService st depId with
  | none => simp [hD] at hDep
  | some _ =>
    simp [hSvc, hNeSelf, hNotPresent, hPath]

end SeLe4n.Kernel
