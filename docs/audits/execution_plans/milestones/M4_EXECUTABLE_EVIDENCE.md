# Milestone M4 — Executable Evidence Expansion

**Goal:** Strengthen the runtime test suite to exercise deeper dependency chains, ensuring the BFS handles realistic graph topologies and that the proof closure does not inadvertently mask a behavioral regression.

**Dependency:** M3 (proof closure complete — ensures no operational behavior changed)

**Estimated changes:** 3–5 new test cases in `NegativeStateSuite.lean`

---

## 1. Motivation

The current test suite (`NegativeStateSuite.lean:319–367`) exercises only **two-node** dependency graphs. While sufficient for basic cycle detection validation, deeper topologies exercise:

- **Multi-hop BFS traversal** — validates the BFS explores beyond direct dependencies
- **Visited-set correctness** — validates the BFS doesn't revisit nodes (diamond shape)
- **Fuel consumption** — validates the BFS has enough fuel for deeper chains
- **Non-over-restriction** — validates the BFS doesn't reject valid (acyclic) registrations

---

## 2. Test cases

### 2.1 Chain-length ≥ 3 cycle rejection (T1)

**Setup:** Three services A (100), B (101), C (102). Register A→B, B→C. Attempt C→A.

**Expected:** `.error .cyclicDependency` — the BFS should find the path C→(nothing, but wait — A→B→C exists, so the back-edge C→A would create A→B→C→A). Actually, the BFS checks `serviceHasPathTo st depId svcId ...` where `depId = A` and `svcId = C`. So it checks: does A reach C? Yes: A→B→C. So the registration is rejected.

```lean
let svcIdC : ServiceId := ⟨102⟩
let svcEntryC : ServiceGraphEntry := {
  identity := { sid := svcIdC, backingObject := 202, owner := 302 }
  status := .stopped
  dependencies := []
  isolatedFrom := []
}
-- Build state with three services
let svcState3 : SystemState :=
  (BootstrapBuilder.empty
    |>.withService svcIdA svcEntryA
    |>.withService svcIdB svcEntryB
    |>.withService svcIdC svcEntryC
    |>.build)
-- Register A→B
let regAB := SeLe4n.Kernel.serviceRegisterDependency svcIdA svcIdB svcState3
match regAB with
| .ok (_, stAB) =>
  -- Register B→C
  let regBC := SeLe4n.Kernel.serviceRegisterDependency svcIdB svcIdC stAB
  match regBC with
  | .ok (_, stABC) =>
    -- Attempt C→A (should detect cycle: A→B→C→A)
    expectError "service dependency chain-3 cycle detection C→A"
      (SeLe4n.Kernel.serviceRegisterDependency svcIdC svcIdA stABC)
      .cyclicDependency
  | .error err =>
    throw <| IO.userError s!"B→C registration failed: {reprStr err}"
| .error err =>
  throw <| IO.userError s!"A→B registration failed: {reprStr err}"
```

### 2.2 Diamond-shaped DAG (T2)

**Setup:** Four services A (100), B (101), C (102), D (103). Register A→B, A→C, B→D, C→D. Then attempt D→A.

**Expected:** All four initial registrations succeed (`.ok`). D→A is rejected (`.error .cyclicDependency`) because A reaches D via two paths (A→B→D and A→C→D).

**Validates:** BFS with multiple paths to the same node, visited-set correctness, fan-in at node D.

```lean
let svcIdD : ServiceId := ⟨103⟩
-- ... (setup with 4 services, register edges, then)
expectError "service dependency diamond cycle detection D→A"
  (SeLe4n.Kernel.serviceRegisterDependency svcIdD svcIdA stDiamond)
  .cyclicDependency
```

### 2.3 Positive non-cycle insertion in deep chain (T3)

**Setup:** After establishing A→B→C (from T1), register D→A where D is a new service with no inbound edges from A/B/C.

**Expected:** `.ok` — D→A is valid because A has no path to D.

**Validates:** BFS is not over-restrictive. The BFS checks if A reaches D, which it cannot (A→B→C, none pointing to D).

```lean
-- After stABC from T1:
let regDA := SeLe4n.Kernel.serviceRegisterDependency svcIdD svcIdA stABC_with_D
match regDA with
| .ok _ =>
  IO.println "positive check passed [service dependency D→A in chain is valid]"
| .error err =>
  throw <| IO.userError s!"D→A registration should succeed but failed: {reprStr err}"
```

### 2.4 Reverse chain registration order (T4)

**Setup:** Three services. Register C→B, then B→A. Then attempt A→C.

**Expected:** Both initial registrations succeed. A→C is rejected because C→B→A→C would be a cycle. The BFS checks if C reaches A: C→B→A. Yes.

**Validates:** BFS works regardless of registration order.

### 2.5 Fan-out stress (T5, optional)

**Setup:** One service S with 5+ dependency registrations to distinct services D1...D5. Then attempt Di→S for each.

**Expected:** All initial registrations succeed. All back-edge attempts are rejected.

**Validates:** BFS handles wide fan-out, fuel is sufficient for the expanded frontier.

---

## 3. Preserving existing test contracts

All existing test cases must continue to pass unchanged:

| Existing test | Expected result | Must not change |
|---|---|---|
| Self-loop rejection (A→A) | `.error .cyclicDependency` | Preserved |
| Missing target (A→999) | `.error .objectNotFound` | Preserved |
| Successful registration (A→B) | `.ok` | Preserved |
| Cycle detection (B→A after A→B) | `.error .cyclicDependency` | Preserved |
| Idempotent re-registration (A→B) | `.ok` | Preserved |

---

## 4. Implementation guidance

### 4.1 Service fixture construction

Use the existing `BootstrapBuilder` pattern from the current test fixture. Each new service needs:
- A unique `ServiceId` (e.g., 100, 101, 102, 103)
- A `ServiceGraphEntry` with unique `backingObject` and `owner` IDs
- Registration via `.withService`

### 4.2 State threading

Each registration produces a new state that must be threaded into the next registration. Use `match` or `do` notation to thread states:

```lean
let regAB := SeLe4n.Kernel.serviceRegisterDependency svcIdA svcIdB initialState
match regAB with
| .ok (_, stAB) =>
  let regBC := SeLe4n.Kernel.serviceRegisterDependency svcIdB svcIdC stAB
  match regBC with
  | .ok (_, stABC) =>
    -- ... continue
  | .error err => throw ...
| .error err => throw ...
```

### 4.3 Test location

New test cases should be added to `tests/NegativeStateSuite.lean` in the existing WS-D4 F-07 section (after line 367), within the `runNegativeChecks` function.

---

## 5. Exit criteria

> **Partial status:** A depth-5 dependency chain smoke test exists in `MainTraceHarness.lean` (lines 254-309) exercising multi-hop BFS traversal. Dedicated `NegativeStateSuite` expansion for chain-3, diamond DAG, and positive deep insertion tests remains pending.

- [ ] T1 chain-3 rejection test in NegativeStateSuite (pending)
- [ ] T2 diamond DAG test in NegativeStateSuite (pending)
- [ ] T3 positive deep insertion test in NegativeStateSuite (pending)
- [x] All existing test expectations unchanged
- [x] `lake build` succeeds
- [x] Depth-5 chain smoke test in MainTraceHarness validates multi-hop BFS traversal

## Artifacts modified

- `tests/NegativeStateSuite.lean` (new test cases in the WS-D4 F-07 section)

## Validation

```bash
./scripts/test_tier2_negative.sh
```
