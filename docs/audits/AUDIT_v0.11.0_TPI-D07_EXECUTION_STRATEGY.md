# TPI-D07 Execution Strategy — Service Dependency Acyclicity Invariant

## 1) Purpose and scope

This document provides an implementation-grade strategy to close tracked issue **TPI-D07** from [`AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md).

### 1.1 Objectives

1. **Replace the deferred `sorry`** at `Service/Invariant.lean:394` in `serviceRegisterDependency_preserves_acyclicity` with a complete formal proof.
2. **Preserve runtime behavior exactly** — same deterministic check ordering, same error semantics, same BFS fuel computation. This is a proof-only closure; no operational code changes.
3. **Land closure evidence** across the proof surface, executable test suite, and documentation artifacts to satisfy the integration requirements defined in [`AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md#integration-requirements-before-closure).

### 1.2 Non-goals

- Changing the BFS algorithm or fuel computation in `serviceHasPathTo`.
- Refactoring `ServiceGraphEntry`, `ServiceId`, or `storeServiceState` data structures.
- Addressing findings outside F-07 (F-11 and F-12 are already closed under WS-D4).
- Introducing completeness proofs for BFS (only soundness — the false-implies-no-path direction — is required).

### 1.3 Methodology

This strategy is derived from direct code inspection of the following source artifacts, not documentation-only assumptions:

| Artifact | Path | Role |
|---|---|---|
| BFS + registration logic | `SeLe4n/Kernel/Service/Operations.lean` | Operational definitions under proof |
| Acyclicity invariant + `sorry` | `SeLe4n/Kernel/Service/Invariant.lean:349–394` | Proof target |
| Service graph data model | `SeLe4n/Model/Object.lean:6–26` | `ServiceGraphEntry`, `ServiceStatus`, dependency lists |
| Service ID type | `SeLe4n/Prelude.lean:112–114` | `structure ServiceId` (typed `Nat` wrapper) |
| System state + store lemmas | `SeLe4n/Model/State.lean:45–193` | `storeServiceState`, `lookupService`, `_eq`/`_ne` lemmas |
| Negative test suite | `tests/NegativeStateSuite.lean:319–367` | Runtime validation of cycle detection |
| Tracked proof issues | `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md:214–236` | TPI-D07 status and closure contract |
| Workstream plan | `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md:281–357` | WS-D4 completion evidence |
| Claim-evidence index | `docs/CLAIM_EVIDENCE_INDEX.md:37` | TPI-D07 listed as IN PROGRESS |
| Proof and invariant map | `docs/gitbook/12-proof-and-invariant-map.md:195–204` | F-07 theorem catalog |

---

## 2) Deep audit snapshot (code-first)

### 2.1 Repository and development-state baseline

The seLe4n project is a Lean 4 microkernel verification model. The architecture is structured as:

- **Kernel subsystems** split into paired `Operations.lean` / `Invariant.lean` modules across six subsystems: `Architecture`, `Capability`, `IPC`, `Lifecycle`, `Scheduler`, `Service`, and `InformationFlow`.
- **Data model** defined in `SeLe4n/Model/` (`State.lean`, `Object.lean`) with typed wrapper IDs in `SeLe4n/Prelude.lean`.
- **Testing** is tiered across five levels:
  - Tier 0: Hygiene and metadata checks (`test_tier0_hygiene.sh`)
  - Tier 1: Build gate via `lake build` (`test_tier1_build.sh`)
  - Tier 2: Runtime checks — `NegativeStateSuite.lean` and `InformationFlowSuite.lean` (`test_tier2_negative.sh`)
  - Tier 3: Invariant surface anchors and documentation checks (`test_tier3_invariant_surface.sh`)
  - Tier 4: Nightly candidates (`test_tier4_nightly_candidates.sh`)
- **Portfolio status:** WS-D1 through WS-D4 are completed. WS-D4 marks TPI-D07 as the sole remaining proof debt (all other tracked issues TPI-D01 through TPI-D06 are CLOSED).

### 2.2 TPI-D07 implementation reality (what code does today)

#### 2.2.1 Cycle-prevention operational logic

The cycle-prevention logic is fully implemented and reachable in the production code path. `serviceRegisterDependency` (`Operations.lean:142–160`) enforces a strict deterministic check ordering:

| Step | Check | Failure result |
|---|---|---|
| 1 | `lookupService st svcId` — source service exists | `.error .objectNotFound` |
| 2 | `lookupService st depId` — dependency target exists | `.error .objectNotFound` |
| 3 | `svcId = depId` — self-dependency guard | `.error .cyclicDependency` |
| 4 | `depId ∈ svc.dependencies` — idempotent re-registration | `.ok ((), st)` (no-op) |
| 5 | `serviceHasPathTo st depId svcId (serviceBfsFuel st)` — cycle detection | `.error .cyclicDependency` |
| 6 | Edge insertion: append `depId` to `svc.dependencies` | `.ok ((), st')` |

On success, the post-state `st'` is produced by `storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st`, which updates only the service entry for `svcId` in the `services` function of `SystemState`.

#### 2.2.2 Bounded BFS reachability (`serviceHasPathTo`)

The reachability check (`Operations.lean:110–127`) implements a standard BFS with fuel-bounded termination:

```
serviceHasPathTo st src target fuel :=
  go [src] [] fuel
where
  go frontier visited
  | 0          => false                           -- fuel exhausted
  | fuel + 1   =>
      match frontier with
      | []          => false                      -- frontier empty: unreachable
      | node :: rest =>
          if node = target then true              -- found target
          else if node ∈ visited then             -- skip visited (no fuel cost)
            go rest visited (fuel + 1)
          else                                    -- expand new node (consumes fuel)
            let deps := (lookupService st node).map (·.dependencies) |>.getD []
            go (rest ++ deps.filter (· ∉ visited)) (node :: visited) fuel
```

Key behavioral properties:

- **Fuel is consumed only on distinct-node expansion** — revisiting an already-visited node recycles fuel via `go rest visited (fuel + 1)`.
- **Fuel bound:** `serviceBfsFuel st = st.objectIndex.length + 256` (`Operations.lean:96–97`).
- **Conservative on exhaustion:** returns `false` when fuel runs out, meaning it may fail to find an existing path (false negative) but never reports a spurious path (no false positives).
- **Completeness is not guaranteed:** the BFS is sound-by-construction for `true` returns (any reported path is real), but a `false` return under insufficient fuel does not logically imply unreachability. This is the exact gap TPI-D07 must close.

#### 2.2.3 Invariant definition and proof state

The acyclicity invariant (`Invariant.lean:349–350`):

```lean
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasPathTo st sid sid (serviceBfsFuel st) = true
```

The preservation theorem (`Invariant.lean:363–394`) has the following branch structure:

| Branch | Hypothesis | Discharge status |
|---|---|---|
| `lookupService st svcId = none` | Source not found → error | Discharged (no success) |
| `lookupService st depId = none` | Dep not found → error | Discharged (no success) |
| `svcId = depId` | Self-loop → error | Discharged (no success) |
| `depId ∈ svc.dependencies` | Idempotent → `st' = st` | Discharged (`exact hAcyc`) |
| `serviceHasPathTo st depId svcId ... = true` | Cycle found → error | Discharged (no success) |
| `serviceHasPathTo st depId svcId ... = false` | No cycle → edge inserted | **`sorry` at line 394** |

The `sorry` appears after the proof has reduced to a goal requiring: given `hCycle : serviceHasPathTo st depId svcId (serviceBfsFuel st) = false` and `hAcyc : serviceDependencyAcyclic st`, prove `serviceDependencyAcyclic st'` where `st'` has the new edge `svcId → depId`.

#### 2.2.4 Executable evidence

`tests/NegativeStateSuite.lean:319–367` validates cycle detection with five cases:

| Test case | Services | Expected result |
|---|---|---|
| Self-loop rejection | A → A | `.error .cyclicDependency` |
| Missing target rejection | A → nonexistent(999) | `.error .objectNotFound` |
| Successful registration | A → B | `.ok` (state `svcStateAB`) |
| Cycle detection | B → A (after A→B) | `.error .cyclicDependency` |
| Idempotent re-registration | A → B (already present) | `.ok` |

Test fixture: two services with IDs 100 and 101, both stopped, empty dependency lists, constructed via `BootstrapBuilder`.

### 2.3 Documentation-to-code consistency audit

| Document | TPI-D07 status | Accuracy |
|---|---|---|
| `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md:214` | IN PROGRESS | Correct — identifies BFS soundness as the remaining obligation |
| `AUDIT_v0.11.0_WORKSTREAM_PLAN.md:337` | WS-D4 completed, TPI-D07 sorry tracked | Correct — notes sorry is tracked, not silently ignored |
| `CLAIM_EVIDENCE_INDEX.md:37` | IN PROGRESS | Correct — reflects open proof obligation |
| `gitbook/12-proof-and-invariant-map.md:204` | Uses sorry; tracked as TPI-D07 | Correct |
| `test_tier0_hygiene.sh` | Excludes `TPI-D*` tagged sorry markers | Correct — accepted technical debt, not hygiene violation |

**Conclusion:** The gap is narrow and precise — **not an algorithm absence, but proof infrastructure insufficiency for bounded-BFS soundness relative to graph reachability semantics.** The runtime behavior is correct and tested. Only the formal bridge between `serviceHasPathTo ... = false` and "no path exists in the graph" is missing.

---

## 3) Root-cause analysis of the proof gap

### 3.1 Current proof skeleton

The existing proof in `serviceRegisterDependency_preserves_acyclicity` is structurally complete through all non-insertion branches. After case-splitting and simplification, the insertion branch reduces to:

```
Goal state at sorry (line 394):
  svcId depId : ServiceId
  st : SystemState
  svc : ServiceGraphEntry
  depSvc : ServiceGraphEntry
  hSvc : lookupService st svcId = some svc
  hDep : lookupService st depId = some depSvc
  hSelf : ¬ svcId = depId
  hExists : ¬ depId ∈ svc.dependencies
  hCycle : ¬ serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
  hAcyc : serviceDependencyAcyclic st
  sid : ServiceId
  ⊢ ¬ serviceHasPathTo
      (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
      sid sid (serviceBfsFuel ...) = true
```

### 3.2 Why the proof stalls

Three specific infrastructure gaps prevent closing this goal:

**Gap 1 — No relational graph semantics.** `serviceHasPathTo` is an executable `Bool`-valued BFS function. Reasoning about graph paths requires an inductive `Prop`-valued relation that supports structural induction. Currently, no such relation exists. Without it, proving "no path exists" requires unfolding the BFS recursion at every step — intractable for arbitrary graph shapes.

**Gap 2 — No BFS soundness bridge.** Even with a declarative path relation, we need a bridge lemma connecting the executable BFS to the relational semantics:

> `serviceHasPathTo st src target fuel = false → ¬ serviceReachable st src target`

This requires proving that the BFS explores all reachable nodes before returning false — a loop invariant argument over the `go` function's `frontier`, `visited`, and `fuel` state. The fuel adequacy question (does `serviceBfsFuel` provide enough fuel?) is embedded in this bridge.

**Gap 3 — No edge-insertion decomposition.** To prove acyclicity preservation after inserting edge `svcId → depId`, we need:

> Any cycle in the post-state graph that uses the new edge must correspond to a pre-state path from `depId` to `svcId`.

This is the classic single-edge-insertion cycle lemma. Without it, we cannot reduce the post-state acyclicity goal to the pre-state BFS hypothesis.

### 3.3 Dependency chain

The three gaps form a strict dependency chain:

```
Gap 1 (declarative path relation)
  └── Gap 2 (BFS soundness bridge)    ← requires Gap 1's definitions
        └── Gap 3 (insertion acyclicity) ← requires Gap 2's bridge lemma
              └── sorry elimination     ← requires Gap 3's composition
```

This ordering determines the milestone sequence in Section 4.

---

## 4) Milestone plan

Six milestones, ordered by strict dependency. Each milestone is designed to be independently testable and to produce reusable proof infrastructure.

### Milestone M0 — Baseline lock and proof-target map

**Goal:** Freeze operational behavior and enumerate the exact proof obligations without changing any executable code.

#### Tasks

1. **Branch shape audit.** Verify that `serviceRegisterDependency` has exactly six branches (as documented in Section 2.2.1) and record the post-simplification goal state at line 394 in strategy PR notes.
2. **Semantics freeze.** Confirm the closure is proof-only: no changes to `Operations.lean` definitions, no new error variants, no fuel computation changes.
3. **Theorem TODO map.** Add a structured comment block in `Service/Invariant.lean` (above line 341) listing the planned intermediate lemmas with their intended signatures. This serves as a verifiable implementation checklist.
4. **Store lemma inventory.** Confirm that `storeServiceState_lookup_eq` and `storeServiceState_lookup_ne` (in `State.lean:180–193`) are sufficient for reasoning about post-state service lookups, or identify any additional lemmas needed.

#### Exit criteria

- No changes to executable definitions in `Operations.lean`.
- Target theorem and all branch obligations documented.
- Required store-level lemmas inventoried and confirmed available.

#### Artifacts modified

- `SeLe4n/Kernel/Service/Invariant.lean` (comment block only)

---

### Milestone M1 — Declarative graph-path semantics

**Goal:** Introduce a proof-friendly inductive path relation over the service dependency graph, independent of the BFS implementation.

#### Tasks

##### M1.1 — Define edge relation

Define `serviceEdge` as a `Prop` capturing direct dependency membership:

```lean
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies
```

This grounds the edge relation in `lookupService`, which is the same accessor used by `serviceHasPathTo` (via `lookupService st node` at `Operations.lean:123`).

##### M1.2 — Define reachable relation

Define `serviceReachable` as the reflexive-transitive closure of `serviceEdge`:

```lean
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl  : serviceReachable st a a
  | step  : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c
```

Alternative: use `Relation.ReflTransGen` from Mathlib/Std if available in the project's dependency set. The inductive definition is preferred if the project avoids external dependencies.

##### M1.3 — Prove structural lemmas

| Lemma | Statement | Purpose |
|---|---|---|
| `serviceEdge_iff_mem` | `serviceEdge st a b ↔ ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies` | Definitional unfolding |
| `serviceReachable_trans` | `serviceReachable st a b → serviceReachable st b c → serviceReachable st a c` | Path concatenation |
| `serviceReachable_step_right` | `serviceReachable st a b → serviceEdge st b c → serviceReachable st a c` | Right-append edge |
| `serviceReachable_of_edge` | `serviceEdge st a b → serviceReachable st a b` | Single-edge path |

##### M1.4 — Prove edge behavior under store operations

| Lemma | Statement | Purpose |
|---|---|---|
| `serviceEdge_storeServiceState_eq` | Edge relation for the updated service entry (relates to new dependency list) | Post-state edge reasoning at `svcId` |
| `serviceEdge_storeServiceState_ne` | `sid ≠ svcId → serviceEdge (storeServiceState ...) sid b ↔ serviceEdge st sid b` | Post-state edge reasoning at other services |

These lemmas wrap `storeServiceState_lookup_eq` and `storeServiceState_lookup_ne` from `State.lean` to lift store-level facts to edge-level facts.

#### Exit criteria

- `serviceReachable` supports induction and composition proofs without unfolding BFS internals.
- Edge-store lemmas cover the single-service-update pattern used by `serviceRegisterDependency`.
- All lemmas compile without `sorry`.

#### Artifacts modified

- `SeLe4n/Kernel/Service/Invariant.lean` (new definitions and lemmas, placed between line 340 and the acyclicity section)

---

### Milestone M2 — BFS soundness bridge

**Goal:** Prove that a `false` return from `serviceHasPathTo` under sufficient fuel implies no declarative path exists.

#### Tasks

##### M2.1 — BFS loop invariant

Define and prove a loop invariant for the inner `go` function of `serviceHasPathTo`. The invariant relates the BFS state (`frontier`, `visited`, `fuel`) to declarative reachability:

> **Invariant:** If `serviceReachable st src target` holds, then either:
> - `target ∈ visited`, or
> - there exists some `mid ∈ frontier` such that `serviceReachable st mid target`, or
> - the function returns `true`.

This invariant is preserved across each iteration of `go` and, when `go` returns `false` (frontier empty, no target found), contradicts the existence of a declarative path.

##### M2.2 — Fuel adequacy

Establish that `serviceBfsFuel st` provides sufficient fuel for the BFS to explore all distinct reachable nodes:

**Approach A (preferred) — Model-level boundedness invariant:**

Prove that the number of distinct `ServiceId` values `sid` for which `lookupService st sid ≠ none` is bounded by `st.objectIndex.length + 256`. Since BFS consumes fuel only on distinct-node expansion and only nodes with `lookupService` entries contribute fan-out, this bound ensures the BFS never runs out of fuel before exploring all reachable nodes.

**Approach B (fallback) — Preconditioned theorem:**

If Approach A requires infrastructure beyond TPI-D07's scope (e.g., a global invariant linking service registration to `objectIndex`), introduce the fuel-adequacy assumption as an explicit precondition:

```lean
-- Precondition: registered services are bounded by available fuel
(hFuel : ∀ sid, lookupService st sid ≠ none →
           sid ∈ reachableSet → ... ≤ serviceBfsFuel st)
```

Document this precondition explicitly and track its discharge as a follow-up obligation.

##### M2.3 — Soundness theorem

Prove the key bridge lemma:

```lean
theorem serviceHasPathTo_false_implies_not_reachable
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hFuel : <fuel adequacy condition>)
    (hBfs : serviceHasPathTo st src target fuel = false) :
    ¬ serviceReachable st src target
```

The proof proceeds by contradiction: assume `serviceReachable st src target`, apply the BFS loop invariant (M2.1) to show the BFS must eventually expand a node on the path to `target`, then use fuel adequacy (M2.2) to show this expansion completes before fuel exhaustion, contradicting `hBfs`.

#### Exit criteria

- A soundness theorem is available that can directly discharge the `sorry` branch premise.
- Fuel adequacy approach is chosen and documented (Approach A or B).
- All lemmas compile without `sorry`.

#### Artifacts modified

- `SeLe4n/Kernel/Service/Invariant.lean` (BFS soundness infrastructure)

---

### Milestone M3 — Edge-insertion acyclicity preservation

**Goal:** Prove that inserting edge `svcId → depId` into an acyclic graph preserves acyclicity when `depId` cannot reach `svcId` in the pre-state.

#### Tasks

##### M3.1 — Post-state reachability decomposition

Prove that any path in the post-state graph either exists entirely in the pre-state graph, or uses the newly inserted edge exactly once:

```lean
theorem reachable_after_insert_cases
    (st : SystemState) (svcId depId : ServiceId)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st svcId = some svc)
    (hNotMem : depId ∉ svc.dependencies)
    (sid1 sid2 : ServiceId)
    (hReach : serviceReachable
      (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
      sid1 sid2) :
    serviceReachable st sid1 sid2 ∨
    (serviceReachable st sid1 svcId ∧ serviceReachable st depId sid2) ∨
    -- (more complex: paths using the new edge multiple times reduce
    --  to the above by pre-state acyclicity)
```

The proof uses induction on `serviceReachable` in the post-state, case-splitting each edge step on whether it originates from the updated service entry at `svcId`. The `serviceEdge_storeServiceState_eq` and `serviceEdge_storeServiceState_ne` lemmas from M1 provide the case analysis at each step.

##### M3.2 — Cycle implies pre-state reachability

Specialize M3.1 to self-reachability (cycles):

```lean
theorem cycle_after_insert_implies_pre_reach
    (st : SystemState) (svcId depId sid : ServiceId)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st svcId = some svc)
    (hNotMem : depId ∉ svc.dependencies)
    (hAcyc : serviceDependencyAcyclic st)
    (hCycle : serviceReachable
      (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
      sid sid) :
    serviceReachable st depId svcId
```

Argument: if `sid` reaches itself in the post-state, the path must use the new edge (otherwise `sid` reaches itself in the pre-state, contradicting `hAcyc`). Using the new edge means passing through `svcId → depId`, so `depId` reaches `svcId` via the remaining path segments — all of which exist in the pre-state.

##### M3.3 — Final theorem closure

Combine M3.2 with the M2 soundness bridge to discharge the `sorry`:

```lean
-- At the sorry site (line 394):
-- Given: hCycle : ¬ serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
-- Given: hAcyc : serviceDependencyAcyclic st
-- Goal:  ∀ sid, ¬ serviceHasPathTo st' sid sid (serviceBfsFuel st') = true

-- Step 1: Assume for contradiction that some sid reaches itself in st'.
-- Step 2: By cycle_after_insert_implies_pre_reach, depId reaches svcId in pre-state.
-- Step 3: By serviceHasPathTo_false_implies_not_reachable (M2), depId does NOT reach svcId.
-- Step 4: Contradiction.
```

Note: The final goal is stated in terms of `serviceHasPathTo` (the executable BFS), not `serviceReachable` (the declarative relation). The proof must bridge between them. Two sub-strategies:

- **Option 1:** Prove both BFS soundness (`false → ¬reachable`) and BFS semi-completeness (`reachable → true` under sufficient fuel), then reason entirely in the declarative domain and translate back.
- **Option 2:** Redefine `serviceDependencyAcyclic` in terms of `serviceReachable` and prove equivalence with the current BFS-based definition. This is cleaner but requires changing the invariant definition (proof-only change, no runtime impact).

**Recommended: Option 2** — it produces a cleaner final proof and makes the invariant definition independent of BFS implementation details. The equivalence theorem serves as a one-time bridge.

#### Exit criteria

- `serviceRegisterDependency_preserves_acyclicity` compiles with **no `sorry`**.
- All intermediate lemmas compile without `sorry`.

#### Artifacts modified

- `SeLe4n/Kernel/Service/Invariant.lean` (insertion lemmas + final theorem)

---

### Milestone M4 — Executable evidence expansion

**Goal:** Strengthen the runtime test suite to exercise deeper dependency chains, ensuring the BFS handles realistic graph topologies and that the proof closure does not inadvertently mask a behavioral regression.

#### Tasks

##### M4.1 — Deeper chain cycle rejection (length ≥ 3)

Add a test constructing a chain A → B → C and verifying that the back-edge C → A is rejected:

```
let svcIdC : ServiceId := ⟨102⟩
-- Register A → B (already tested), B → C (new)
-- Attempt C → A → should return .error .cyclicDependency
```

This exercises the BFS's multi-hop traversal, confirming it correctly detects transitive reachability — the exact property the formal proof targets.

##### M4.2 — Diamond-shaped DAG (non-cycle)

Add a test constructing A → B, A → C, B → D, C → D (diamond shape) and verifying that all four edges are accepted and D → A is rejected. This tests:

- BFS with multiple paths to the same node (visited-list correctness).
- Fan-in at node D.
- Cycle detection through the longest path.

##### M4.3 — Positive non-cycle insertion in deep chain

After establishing A → B → C, verify that registering D → A succeeds (D has no inbound edges from A/B/C, so no cycle). This ensures the BFS is not over-restrictive.

##### M4.4 — Preserve existing test contracts

All existing negative test cases (self-loop, missing target, A→B success, B→A rejection, idempotent re-registration) must continue to pass unchanged.

#### Exit criteria

- `tests/NegativeStateSuite.lean` includes at least three new test cases (chain-3 rejection, diamond DAG, positive deep insertion).
- `./scripts/test_tier2_negative.sh` passes with expanded coverage.
- No changes to existing test expectations.

#### Artifacts modified

- `tests/NegativeStateSuite.lean` (new test cases in the WS-D4 F-07 section)

---

### Milestone M5 — Closure synchronization and documentation hygiene

**Goal:** Satisfy the tracked-issue closure contract across all documentation surfaces and CI gates.

#### Tasks

##### M5.1 — Update tracked proof issue status

File: `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`

- Change TPI-D07 status from `IN PROGRESS` to `CLOSED`.
- Replace the "Partially closed theorem obligation (uses `sorry`)" section with the final theorem signature (no `sorry`).
- Add resolution summary documenting the proof approach (declarative path relation + BFS soundness bridge + edge-insertion decomposition).

##### M5.2 — Update workstream plan completion evidence

File: `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`

- Remove "TPI-D07 partially closed (BFS soundness sorry tracked)" qualifier from WS-D4 completion evidence (line 337).
- Update the F-07 completion evidence paragraph to state the preservation theorem is proved without `sorry`.

##### M5.3 — Update claim-evidence index

File: `docs/CLAIM_EVIDENCE_INDEX.md`

- Change TPI-D07 row status from `IN PROGRESS` to `CLOSED`.

##### M5.4 — Update proof and invariant map

File: `docs/gitbook/12-proof-and-invariant-map.md`

- Remove "(uses `sorry` for BFS soundness; tracked as TPI-D07)" from the `serviceRegisterDependency_preserves_acyclicity` entry.
- Add entries for the new intermediate lemmas introduced in M1–M3.
- Add "(no `sorry`)" qualifier to the preservation theorem entry.

##### M5.5 — Run validation gate sequence

Execute the full tiered validation:

```bash
./scripts/test_fast.sh            # Tier 0–1: hygiene + build
./scripts/test_tier2_negative.sh  # Tier 2: runtime negative suite
./scripts/test_tier3_invariant_surface.sh  # Tier 3: invariant anchors + doc checks
./scripts/test_full.sh            # Tier 0–3: full gate
```

Confirm that Tier-0 hygiene no longer needs a TPI-D07 sorry exclusion (if the exclusion pattern in `test_tier0_hygiene.sh` was specific to this sorry, it can be tightened).

#### Exit criteria

- No residual mention of deferred `sorry` for TPI-D07 in any documentation artifact.
- All four documentation files updated consistently.
- Tiered checks pass (`test_full.sh` exit 0).
- All changes land in a single PR to prevent documentation drift.

#### Artifacts modified

- `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`
- `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`
- `docs/CLAIM_EVIDENCE_INDEX.md`
- `docs/gitbook/12-proof-and-invariant-map.md`

---

## 5) Theorem inventory (implementation checklist)

The following theorems constitute the complete proof infrastructure required for TPI-D07 closure. They are ordered by dependency — each theorem depends only on those above it.

### Layer 0 — Definitions

| # | Name | Signature sketch | File location |
|---|---|---|---|
| D1 | `serviceEdge` | `SystemState → ServiceId → ServiceId → Prop` | `Service/Invariant.lean` |
| D2 | `serviceReachable` | `SystemState → ServiceId → ServiceId → Prop` (inductive) | `Service/Invariant.lean` |

### Layer 1 — Structural lemmas (M1)

| # | Name | Statement | Depends on |
|---|---|---|---|
| L1 | `serviceEdge_iff_mem` | `serviceEdge st a b ↔ ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies` | D1 |
| L2 | `serviceReachable_trans` | `serviceReachable st a b → serviceReachable st b c → serviceReachable st a c` | D2 |
| L3 | `serviceReachable_of_edge` | `serviceEdge st a b → serviceReachable st a b` | D1, D2 |
| L4 | `serviceEdge_storeServiceState_eq` | Edge relation at updated service reflects new dependency list | D1, `storeServiceState_lookup_eq` |
| L5 | `serviceEdge_storeServiceState_ne` | Edge relation at non-updated services is unchanged | D1, `storeServiceState_lookup_ne` |

### Layer 2 — BFS soundness (M2)

| # | Name | Statement | Depends on |
|---|---|---|---|
| B1 | `serviceHasPathTo_go_invariant` | Loop invariant for `go` relating frontier/visited to reachability | D2, L1 |
| B2 | `serviceBfsFuel_sufficient` | Fuel bound dominates distinct reachable nodes (or precondition) | — |
| B3 | `serviceHasPathTo_false_implies_not_reachable` | `false` return under sufficient fuel → no declarative path | B1, B2, D2 |

### Layer 3 — Edge insertion (M3)

| # | Name | Statement | Depends on |
|---|---|---|---|
| E1 | `serviceReachable_post_insert_cases` | Post-state path decomposes into pre-state paths ± new edge | L4, L5, D2 |
| E2 | `cycle_after_insert_implies_pre_reach` | Post-state cycle → pre-state `depId` reaches `svcId` | E1 |
| E3 | `serviceDependencyAcyclic_iff_reachable` | BFS-based invariant ↔ declarative invariant (if Option 2 chosen) | B3, D2 |

### Layer 4 — Final closure

| # | Name | Statement | Depends on |
|---|---|---|---|
| F1 | `serviceRegisterDependency_preserves_acyclicity` | Preservation theorem, no `sorry` | E2, B3, E3 |

**Total new theorem count:** 12–13 (depending on Option 1 vs Option 2 for the invariant bridge).

---

## 6) Risks, mitigations, and decision points

### Risk 1 — Fuel adequacy proof (HIGHEST priority)

**Risk:** `serviceBfsFuel st = st.objectIndex.length + 256` may not provably bound the number of distinct services in the graph. Service IDs are `Nat`-wrapped structs (`ServiceId` from `Prelude.lean:112`) and the `services` field of `SystemState` is a function `ServiceId → Option ServiceGraphEntry` — an infinite domain. The `objectIndex` tracks kernel objects, not services; a service's `backingObject` is in the object index, but `ServiceId` itself need not be.

**Mitigations:**

| Strategy | Approach | Trade-off |
|---|---|---|
| **A: Model-level invariant** | Prove that for all `sid` where `lookupService st sid ≠ none`, the `sid` is bounded by some finite set derivable from state. Link service registration to object-index discipline. | Best outcome: unconditional soundness. Risk: may require cross-subsystem invariant work beyond TPI-D07 scope. |
| **B: Preconditioned theorem** | Add an explicit fuel-adequacy hypothesis to the preservation theorem. Document the assumption. Track its discharge as a follow-up. | Pragmatic: closes the sorry cleanly. The precondition is dischargeable in any concrete (finite) model state. |
| **C: Strengthen BFS to track visited count** | Modify `serviceHasPathTo` to use visited-set size as fuel, making soundness trivially provable. | Violates the "no operational changes" constraint. Only if Approaches A and B fail. |

**Decision point:** Choose between A, B, or C during M2 implementation. Document the decision in the PR description.

### Risk 2 — List-based proof complexity (MEDIUM priority)

**Risk:** The dependency graph uses `List ServiceId` for `dependencies` and `List.filter`/`List.append` in the BFS. Lean 4 list lemmas can create rewriting-heavy proofs, especially for membership reasoning through `storeServiceState` (which uses function update, not list mutation).

**Mitigations:**

- Introduce small canonical membership lemmas (L4, L5) early in M1 before attempting the complex BFS invariant proof in M2.
- Use `simp` lemmas with `@[simp]` attribute for edge-relation unfolding to reduce manual rewriting.
- If list reasoning becomes intractable, consider introducing a `Finset`-based abstraction layer over the dependency lists (proof-only, no runtime impact).

### Risk 3 — BFS loop invariant complexity (MEDIUM priority)

**Risk:** The `go` function uses structural recursion on `fuel` with a `fuel + 1` pattern in the visited-skip branch (recycling fuel). This non-standard recursion pattern may complicate well-founded induction arguments.

**Mitigations:**

- Use `fuel` as the primary induction measure, with the visited-set size as a secondary measure for the fuel-recycling branch.
- Alternatively, prove the invariant by strong induction on `fuel`, handling the recycling case by noting that `|visited|` strictly increases or `|frontier|` strictly decreases on each non-recycling step.

### Risk 4 — Documentation drift (LOW priority)

**Risk:** Four documentation files reference TPI-D07 status. If proof closure and doc updates land in separate PRs, interim states may be inconsistent.

**Mitigation:** Perform all documentation updates (M5) in the same PR as the proof closure (M3). The milestone ordering ensures M5 is the final step.

---

## 7) Validation plan

### 7.1 Per-milestone validation

| Milestone | Validation command | What it checks |
|---|---|---|
| M0 | `./scripts/test_tier1_build.sh` | Build still passes with comment-only changes |
| M1 | `./scripts/test_tier1_build.sh` | New definitions and lemmas compile |
| M2 | `./scripts/test_tier1_build.sh` | BFS soundness lemmas compile |
| M3 | `./scripts/test_tier1_build.sh` + manual `sorry` search | Final theorem compiles without `sorry` |
| M4 | `./scripts/test_tier2_negative.sh` | New test cases pass |
| M5 | `./scripts/test_full.sh` | Full tier 0–3 gate passes |

### 7.2 Final closure validation sequence

```bash
# 1. Fast gate (Tier 0–1): hygiene + build
./scripts/test_fast.sh

# 2. Smoke gate (Tier 0–1 with extended checks)
./scripts/test_smoke.sh

# 3. Negative suite (Tier 2): runtime cycle-detection validation
./scripts/test_tier2_negative.sh

# 4. Invariant surface (Tier 3): symbol anchors + doc consistency
./scripts/test_tier3_invariant_surface.sh

# 5. Full gate (Tier 0–3): complete validation
./scripts/test_full.sh
```

### 7.3 Optional extended validation

```bash
# Nightly gate (Tier 0–4): includes experimental/candidate tests
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

### 7.4 Manual verification checklist

- [ ] `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` returns zero matches.
- [ ] `rg 'TPI-D07.*IN PROGRESS' docs/` returns zero matches.
- [ ] `rg 'sorry.*TPI-D07\|TPI-D07.*sorry' docs/` returns zero matches.
- [ ] All new lemma names appear in `docs/gitbook/12-proof-and-invariant-map.md`.
- [ ] `CLAIM_EVIDENCE_INDEX.md` shows TPI-D07 as CLOSED.

---

## 8) Definition of done for TPI-D07

TPI-D07 is closed when **all** of the following conditions hold:

### 8.1 Proof surface

| Condition | Verification |
|---|---|
| `serviceRegisterDependency_preserves_acyclicity` contains no `sorry` | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` returns 0 |
| All intermediate lemmas (L1–L5, B1–B3, E1–E3) compile without `sorry` | `lake build` succeeds |
| BFS soundness bridge connects executable BFS to declarative reachability | Theorem `serviceHasPathTo_false_implies_not_reachable` exists |
| Edge-insertion decomposition lemma exists | Theorem `cycle_after_insert_implies_pre_reach` exists |

### 8.2 Executable evidence

| Condition | Verification |
|---|---|
| Negative tests include chain-length ≥ 3 cycle rejection | Test case in `NegativeStateSuite.lean` |
| Negative tests include diamond-DAG topology | Test case in `NegativeStateSuite.lean` |
| All existing test expectations unchanged | `./scripts/test_tier2_negative.sh` passes |

### 8.3 Documentation

| Condition | Verification |
|---|---|
| `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`: TPI-D07 status = CLOSED | Manual inspection |
| `AUDIT_v0.11.0_WORKSTREAM_PLAN.md`: no "sorry deferred" qualifier | `rg 'sorry.*TPI-D07' docs/audits/` returns 0 |
| `CLAIM_EVIDENCE_INDEX.md`: TPI-D07 status = CLOSED | Manual inspection |
| `gitbook/12-proof-and-invariant-map.md`: preservation theorem marked "(no `sorry`)" | Manual inspection |

### 8.4 CI gates

| Condition | Verification |
|---|---|
| Tier 0–3 pass | `./scripts/test_full.sh` exits 0 |
| No new `sorry` introduced anywhere in proof surface | `rg 'sorry' SeLe4n/Kernel/` returns only pre-existing accepted debt (if any) |

---

## Appendix A — Key source code reference

### A.1 `serviceRegisterDependency` (Operations.lean:142–160)

```lean
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
```

### A.2 `serviceHasPathTo` (Operations.lean:110–127)

```lean
def serviceHasPathTo
    (st : SystemState) (src target : ServiceId) (fuel : Nat) : Bool :=
  go [src] [] fuel
where
  go (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      match frontier with
      | [] => false
      | node :: rest =>
          if node = target then true
          else if node ∈ visited then go rest visited (fuel + 1)
          else
            let deps := match lookupService st node with
              | some svc => svc.dependencies
              | none => []
            let newFrontier := rest ++ deps.filter (· ∉ visited)
            go newFrontier (node :: visited) fuel
```

### A.3 Data model

```lean
-- SeLe4n/Prelude.lean:112
structure ServiceId where
  val : Nat

-- SeLe4n/Model/Object.lean:21–26
structure ServiceGraphEntry where
  identity : ServiceIdentity
  status : ServiceStatus
  dependencies : List ServiceId
  isolatedFrom : List ServiceId

-- SeLe4n/Model/State.lean:45–52
structure SystemState where
  machine : MachineState
  objects : ObjId → Option KernelObject
  objectIndex : List ObjId
  services : ServiceId → Option ServiceGraphEntry
  scheduler : SchedulerState
  irqHandlers : Irq → Option ObjId
  lifecycle : LifecycleMetadata
```

### A.4 Store lemmas (State.lean:180–193)

```lean
theorem storeServiceState_lookup_eq (st : SystemState)
    (sid : ServiceId) (entry : ServiceGraphEntry) :
    lookupService (storeServiceState sid entry st) sid = some entry

theorem storeServiceState_lookup_ne (st : SystemState)
    (sid sid' : ServiceId) (entry : ServiceGraphEntry) (hNe : sid' ≠ sid) :
    lookupService (storeServiceState sid entry st) sid' = lookupService st sid'
```

---

## Appendix B — Cross-reference map

| This document section | Related artifact | Relationship |
|---|---|---|
| Section 2.2 | `Operations.lean:142–160` | Direct code audit |
| Section 2.2.2 | `Operations.lean:96–127` | BFS algorithm audit |
| Section 2.2.3 | `Invariant.lean:349–394` | Proof state audit |
| Section 2.2.4 | `NegativeStateSuite.lean:319–367` | Test coverage audit |
| Section 3 | `Invariant.lean:394` | Root cause of `sorry` |
| Section 4, M1 | `State.lean:180–193` | Store lemma dependencies |
| Section 4, M5.1 | `TRACKED_PROOF_ISSUES.md:214–236` | Status update target |
| Section 4, M5.2 | `WORKSTREAM_PLAN.md:331–338` | Completion evidence target |
| Section 4, M5.3 | `CLAIM_EVIDENCE_INDEX.md:37` | Status update target |
| Section 4, M5.4 | `12-proof-and-invariant-map.md:195–204` | Theorem catalog target |
