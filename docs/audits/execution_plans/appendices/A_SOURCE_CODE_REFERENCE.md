# Appendix A — Annotated Source Code Reference

This appendix contains the key source code excerpts relevant to TPI-D07, annotated with proof-relevant observations.

---

## A.1 `serviceRegisterDependency` (Operations.lean:142–160)

```lean
def serviceRegisterDependency
    (svcId depId : ServiceId) : Kernel Unit :=
  fun st =>
    match lookupService st svcId with            -- Step 1: source exists?
    | none => .error .objectNotFound
    | some svc =>
        match lookupService st depId with        -- Step 2: target exists?
        | none => .error .objectNotFound
        | some _ =>
            if svcId = depId then                -- Step 3: self-loop guard
              .error .cyclicDependency
            else if depId ∈ svc.dependencies then -- Step 4: idempotent check
              .ok ((), st)
            else if serviceHasPathTo st depId svcId (serviceBfsFuel st) then
              .error .cyclicDependency            -- Step 5: cycle detection
            else
              let svc' : ServiceGraphEntry :=     -- Step 6: edge insertion
                { svc with dependencies := svc.dependencies ++ [depId] }
              storeServiceEntry svcId svc' st
```

**Proof-relevant annotations:**

- **Step 5 BFS call:** `serviceHasPathTo st depId svcId ...` — checks if `depId` can reach `svcId`. Note: `depId` is the **source**, `svcId` is the **target**. This is because adding edge `svcId → depId` would create a cycle if `depId → ... → svcId` already exists.
- **Step 6 state update:** Uses `storeServiceEntry` which wraps `storeServiceState` in the kernel monad. The only state change is to the `services` function at `svcId`.
- **`some _` at step 2:** The dependency target's entry (`depSvc`) is not bound to a variable in the `some _` pattern. In the proof, this is recovered via `cases hDep : lookupService st depId` which binds `depSvc`.

---

## A.2 `serviceHasPathTo` and `go` (Operations.lean:110–127)

```lean
def serviceHasPathTo
    (st : SystemState) (src target : ServiceId) (fuel : Nat) : Bool :=
  go [src] [] fuel
where
  go (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false                                    -- FUEL EXHAUSTED
  | fuel + 1 =>
      match frontier with
      | [] => false                                -- FRONTIER EMPTY: no path
      | node :: rest =>
          if node = target then true               -- FOUND TARGET
          else if node ∈ visited then              -- SKIP VISITED (recycle fuel)
            go rest visited (fuel + 1)             -- ← Note: fuel + 1 = original input
          else                                     -- EXPAND NEW NODE (consume fuel)
            let deps := match lookupService st node with
              | some svc => svc.dependencies
              | none => []
            let newFrontier := rest ++ deps.filter (· ∉ visited)
            go newFrontier (node :: visited) fuel   -- ← Note: fuel = original input - 1
```

**Proof-relevant annotations:**

- **Fuel recycling (line 121):** When `node ∈ visited`, the recursive call passes `fuel + 1`, which equals the original input (since we destructured `fuel + 1` into `fuel` and `1`). This means the Nat argument does **not** decrease in this branch. Termination relies on `frontier.length` decreasing (removing `node` from the front).
- **Fuel consumption (line 127):** When expanding a new node, `fuel` is passed (one less than input). The frontier may grow (`rest ++ deps.filter ...`), but the visited set grows (`node :: visited`), and fuel decreases.
- **Initial state:** `go [src] [] fuel` — frontier contains only `src`, visited is empty.
- **Self-reachability:** If `src = target`, the BFS immediately returns `true` on the first step (node = src = target). This is critical for the [Risk 0](../05_RISK_REGISTER.md#risk-0) analysis.

---

## A.3 `serviceBfsFuel` (Operations.lean:96–97)

```lean
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256
```

**Proof-relevant annotations:**

- `objectIndex` is a `List ObjId` tracking kernel objects — not directly related to `ServiceId`.
- `serviceBfsFuel` is always ≥ 256, so fuel ≥ 1 is guaranteed.
- After `storeServiceState`, the `objectIndex` is unchanged (frame condition S1).

---

## A.4 `serviceDependencyAcyclic` (Invariant.lean:349–350)

```lean
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasPathTo st sid sid (serviceBfsFuel st) = true
```

**Proof-relevant annotations:**

- This checks `serviceHasPathTo st sid sid ...` with `src = target = sid`.
- As analyzed in [Risk 0](../05_RISK_REGISTER.md#risk-0), the BFS returns `true` immediately when `src = target` and `fuel ≥ 1`. If confirmed, this makes the invariant always `False`.

---

## A.5 Data model types

### ServiceId (Prelude.lean:112–114)

```lean
structure ServiceId where
  val : Nat
deriving DecidableEq, Repr, Inhabited
```

- `DecidableEq` is critical: enables `if node = target` in the BFS and `if sid' = sid` in `storeServiceState`.
- The `Nat` wrapper means the domain is infinite, but only finitely many services have entries in any given state.

### ServiceGraphEntry (Object.lean:21–26)

```lean
structure ServiceGraphEntry where
  identity : ServiceIdentity
  status : ServiceStatus
  dependencies : List ServiceId
  isolatedFrom : List ServiceId
  deriving Repr, DecidableEq
```

- `dependencies` is the adjacency list for the dependency graph.
- `isolatedFrom` is unrelated to cycle detection.
- `DecidableEq` enables equality comparisons between entries.

### SystemState (State.lean:45–52)

```lean
structure SystemState where
  machine : SeLe4n.MachineState
  objects : SeLe4n.ObjId → Option KernelObject
  objectIndex : List SeLe4n.ObjId
  services : ServiceId → Option ServiceGraphEntry
  scheduler : SchedulerState
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  lifecycle : LifecycleMetadata
```

- `services` is a function, not a finite map. Any `ServiceId` can be queried.
- `objectIndex` is the finite list of tracked kernel objects (used for fuel computation).
- `storeServiceState` only modifies the `services` field.

---

## A.6 Store lemmas (State.lean:180–193)

```lean
theorem storeServiceState_lookup_eq
    (st : SystemState) (sid : ServiceId) (entry : ServiceGraphEntry) :
    lookupService (storeServiceState sid entry st) sid = some entry := by
  simp [lookupService, storeServiceState]

theorem storeServiceState_lookup_ne
    (st : SystemState) (sid sid' : ServiceId) (entry : ServiceGraphEntry)
    (hNe : sid' ≠ sid) :
    lookupService (storeServiceState sid entry st) sid' = lookupService st sid' := by
  simp [lookupService, storeServiceState, hNe]
```

**Proof-relevant annotations:**

- These two lemmas provide the **frame condition** for reasoning about edges after `storeServiceState`. They are the foundation for the `serviceEdge_storeServiceState_eq/ne` lemmas in M1.
- Note the argument order in `_ne`: the first `sid` is the **stored** ID, `sid'` is the **queried** ID, and `hNe : sid' ≠ sid`.

---

## A.7 `storeServiceEntry` (Operations.lean:11–12)

```lean
def storeServiceEntry (sid : ServiceId) (entry : ServiceGraphEntry) : Kernel Unit :=
  fun st => .ok ((), storeServiceState sid entry st)
```

**Proof-relevant annotations:**

- This is a thin wrapper around `storeServiceState` that injects into the kernel monad.
- In the proof at `Invariant.lean:391`, `unfold storeServiceEntry at hReg` followed by `simp at hReg; cases hReg` extracts the post-state equality `st' = storeServiceState svcId svc' st`.

---

## A.8 `lookupService` (State.lean:142–143)

```lean
def lookupService (st : SystemState) (sid : ServiceId) : Option ServiceGraphEntry :=
  st.services sid
```

- Definitionally equal to `st.services sid`. The `lookupService` name provides abstraction for documentation and proof readability.

---

## A.9 Preservation theorem structure (Invariant.lean:363–394)

```lean
theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st) :
    serviceDependencyAcyclic st' := by
  unfold serviceRegisterDependency at hReg
  cases hSvc : lookupService st svcId with        -- Branch 1: source not found
  | none => simp [hSvc] at hReg
  | some svc =>
    simp only [hSvc] at hReg
    cases hDep : lookupService st depId with       -- Branch 2: dep not found
    | none => simp [hDep] at hReg
    | some depSvc =>
      simp only [hDep] at hReg
      by_cases hSelf : svcId = depId               -- Branch 3: self-loop
      · simp [hSelf] at hReg
      · simp only [hSelf, ite_false] at hReg
        by_cases hExists : depId ∈ svc.dependencies -- Branch 4: idempotent
        · simp [hExists] at hReg
          cases hReg
          exact hAcyc
        · simp only [hExists, ite_false] at hReg
          by_cases hCycle : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
          · simp [hCycle] at hReg                   -- Branch 5: cycle found
          · simp only [hCycle] at hReg
            unfold serviceDependencyAcyclic
            intro sid
            unfold storeServiceEntry at hReg
            simp at hReg
            cases hReg
            sorry -- TPI-D07: BFS soundness deferred ← THIS IS THE TARGET
```

**Line-by-line proof-state analysis:** See [03_ROOT_CAUSE_ANALYSIS.md §5](../03_ROOT_CAUSE_ANALYSIS.md#5-proof-state-evolution-through-the-insertion-branch) for the exact goal state at the `sorry`.
