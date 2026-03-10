import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- External policy gate used by M5 orchestration helpers. -/
abbrev ServicePolicy := ServiceGraphEntry → Bool

/-- Deterministic service update helper in kernel-monad form. -/
def storeServiceEntry (sid : ServiceId) (entry : ServiceGraphEntry) : Kernel Unit :=
  fun st => .ok ((), storeServiceState sid entry st)

/-- Start a stopped service when policy allows and dependencies are running.

Deterministic check ordering:
1. service lookup (`objectNotFound`),
2. backing-object existence (`objectNotFound`) — WS-H13/A-29,
3. service must be `stopped` (`illegalState`),
4. policy predicate must allow start (`policyDenied`),
5. dependencies must be running (`dependencyViolation`),
6. status changes to `running` on success. -/
def serviceStart
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    match lookupService st sid with
    | none => .error .objectNotFound
    | some svc =>
        -- WS-H13/A-29: Verify backing object exists before any state mutation
        match st.objects[svc.identity.backingObject]? with
        | none => .error .objectNotFound
        | some _ =>
          if svc.status = .stopped then
            if policyAllowsStart svc then
              if dependenciesSatisfied st sid then
                storeServiceEntry sid { svc with status := .running } st
              else
                .error .dependencyViolation
            else
              .error .policyDenied
          else
            .error .illegalState

/-- Stop a running service when policy allows.

Deterministic check ordering:
1. service lookup (`objectNotFound`),
2. backing-object existence (`objectNotFound`) — WS-H13/A-29,
3. service must be `running` (`illegalState`),
4. policy predicate must allow stop (`policyDenied`),
5. status changes to `stopped` on success. -/
def serviceStop
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy) : Kernel Unit :=
  fun st =>
    match lookupService st sid with
    | none => .error .objectNotFound
    | some svc =>
        -- WS-H13/A-29: Verify backing object exists before any state mutation
        match st.objects[svc.identity.backingObject]? with
        | none => .error .objectNotFound
        | some _ =>
          if svc.status = .running then
            if policyAllowsStop svc then
              storeServiceEntry sid { svc with status := .stopped } st
            else
              .error .policyDenied
          else
            .error .illegalState

/-- Restart composes stop-then-start with atomic rollback semantics.

WS-H13/A-30: If stop succeeds but start fails, the service is rolled back
to its pre-restart state (running). This ensures restart is atomic: either
both stop and start succeed, or the state is unchanged. The rollback is
achieved by restoring the original service entry from the pre-stop state.

Failure ordering:
1. any `serviceStop` failure is returned directly (state unchanged),
2. if stop succeeds then `serviceStart` runs over the post-stop state,
3. if start fails, the original service entry is restored (rollback),
4. success requires both stages to succeed. -/
def serviceRestart
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    match serviceStop sid policyAllowsStop st with
    | .error e => .error e
    | .ok (_, stStopped) =>
        match serviceStart sid policyAllowsStart stStopped with
        | .ok result => .ok result
        | .error e =>
            -- WS-H13/A-30: Rollback — restore service to pre-stop state
            match lookupService st sid with
            | some origSvc =>
                match storeServiceEntry sid origSvc stStopped with
                | .ok _ => .error e
                | .error _ => .error e  -- rollback failed; return original error
            | none => .error e  -- should not happen since stop succeeded

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
algorithm was migrated to DFS with HashSet visited set in WS-G8. -/
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
6. dependency edge is added on success. -/
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

theorem serviceStart_error_policyDenied
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (svc : ServiceGraphEntry)
    (obj : KernelObject)
    (hSvc : lookupService st sid = some svc)
    (hBacking : st.objects[svc.identity.backingObject]? = some obj)
    (hStopped : svc.status = .stopped)
    (hPolicy : policyAllowsStart svc = false) :
    serviceStart sid policyAllowsStart st = .error .policyDenied := by
  unfold serviceStart
  simp [hSvc, hBacking, hStopped, hPolicy]

/-- WS-H13/A-29: serviceStart fails when backing object is missing. -/
theorem serviceStart_error_backingObjectMissing
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hNoBacking : st.objects[svc.identity.backingObject]? = none) :
    serviceStart sid policyAllowsStart st = .error .objectNotFound := by
  unfold serviceStart
  simp [hSvc, hNoBacking]

theorem serviceStart_error_dependencyViolation
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (svc : ServiceGraphEntry)
    (obj : KernelObject)
    (hSvc : lookupService st sid = some svc)
    (hBacking : st.objects[svc.identity.backingObject]? = some obj)
    (hStopped : svc.status = .stopped)
    (hPolicy : policyAllowsStart svc = true)
    (hDeps : dependenciesSatisfied st sid = false) :
    serviceStart sid policyAllowsStart st = .error .dependencyViolation := by
  unfold serviceStart
  simp [hSvc, hBacking, hStopped, hPolicy, hDeps]

theorem serviceStop_error_policyDenied
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (obj : KernelObject)
    (hSvc : lookupService st sid = some svc)
    (hBacking : st.objects[svc.identity.backingObject]? = some obj)
    (hRunning : svc.status = .running)
    (hPolicy : policyAllowsStop svc = false) :
    serviceStop sid policyAllowsStop st = .error .policyDenied := by
  unfold serviceStop
  simp [hSvc, hBacking, hRunning, hPolicy]

/-- WS-H13/A-29: serviceStop fails when backing object is missing. -/
theorem serviceStop_error_backingObjectMissing
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hNoBacking : st.objects[svc.identity.backingObject]? = none) :
    serviceStop sid policyAllowsStop st = .error .objectNotFound := by
  unfold serviceStop
  simp [hSvc, hNoBacking]

theorem serviceStop_error_illegalState
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (obj : KernelObject)
    (hSvc : lookupService st sid = some svc)
    (hBacking : st.objects[svc.identity.backingObject]? = some obj)
    (hNotRunning : svc.status ≠ .running) :
    serviceStop sid policyAllowsStop st = .error .illegalState := by
  unfold serviceStop
  simp [hSvc, hBacking, hNotRunning]

theorem serviceRestart_error_of_stop_error
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (hStop : serviceStop sid policyAllowsStop st = .error e) :
    serviceRestart sid policyAllowsStop policyAllowsStart st = .error e := by
  unfold serviceRestart
  simp [hStop]

/-- WS-H13/A-30: Restart returns the start error when start fails, with rollback. -/
theorem serviceRestart_error_of_start_error
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (stStopped : SystemState)
    (e : KernelError)
    (hStop : serviceStop sid policyAllowsStop st = .ok ((), stStopped))
    (hStart : serviceStart sid policyAllowsStart stStopped = .error e) :
    serviceRestart sid policyAllowsStop policyAllowsStart st = .error e := by
  unfold serviceRestart
  simp only [hStop, hStart]
  split <;> simp_all [storeServiceEntry]

theorem serviceRestart_ok_implies_staged_steps
    (st st' : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (hStep : serviceRestart sid policyAllowsStop policyAllowsStart st = .ok ((), st')) :
    ∃ stStopped,
      serviceStop sid policyAllowsStop st = .ok ((), stStopped) ∧
      serviceStart sid policyAllowsStart stStopped = .ok ((), st') := by
  unfold serviceRestart at hStep
  cases hStop : serviceStop sid policyAllowsStop st with
  | error e => simp [hStop] at hStep
  | ok pair =>
      rcases pair with ⟨u, stStopped⟩
      cases u
      simp only [hStop] at hStep
      refine ⟨stStopped, rfl, ?_⟩
      -- hStep now has the match on serviceStart with rollback
      cases hStart : serviceStart sid policyAllowsStart stStopped with
      | ok pair₂ =>
        rcases pair₂ with ⟨_, stStarted⟩
        simp [hStart] at hStep
        rw [hStep]
      | error e =>
        -- Start failed: rollback produces .error, contradicts .ok in hStep
        simp only [hStart] at hStep
        split at hStep <;> simp_all [storeServiceEntry]

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
