# TPI-D07 Execution Plan — Master Index

## Service Dependency Acyclicity Invariant: `sorry` Elimination

**Target:** Replace the deferred `sorry` at `SeLe4n/Kernel/Service/Invariant.lean:394` with a complete formal proof of `serviceRegisterDependency_preserves_acyclicity`.

**Tracked issue:** TPI-D07 from [`AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](../AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md#issue-tpi-d07-in-progress--service-dependency-acyclicity-invariant)

**Classification:** Proof-only closure — no operational code changes permitted.

---

## Document map

| # | Document | Purpose |
|---|---|---|
| **00** | **`00_INDEX.md`** (this file) | Master index, navigation, status dashboard |
| **01** | [`01_PURPOSE_AND_SCOPE.md`](./01_PURPOSE_AND_SCOPE.md) | Objectives, non-goals, methodology, source-artifact inventory |
| **02** | [`02_CODEBASE_AUDIT.md`](./02_CODEBASE_AUDIT.md) | Deep code-first audit of BFS, registration, invariant state |
| **03** | [`03_ROOT_CAUSE_ANALYSIS.md`](./03_ROOT_CAUSE_ANALYSIS.md) | Three infrastructure gaps, dependency chain, proof stall diagnosis |
| **04** | [`04_THEOREM_DEPENDENCY_GRAPH.md`](./04_THEOREM_DEPENDENCY_GRAPH.md) | Complete theorem inventory with layers, signatures, and dependency ordering |
| **05** | [`05_RISK_REGISTER.md`](./05_RISK_REGISTER.md) | Risk matrix, mitigations, decision points, contingency plans |
| **06** | [`06_VALIDATION_PLAN.md`](./06_VALIDATION_PLAN.md) | Per-milestone validation, final closure sequence, manual checklist |
| **07** | [`07_DEFINITION_OF_DONE.md`](./07_DEFINITION_OF_DONE.md) | Closure criteria across proof, tests, documentation, and CI gates |

### Milestone plans

| Milestone | Document | Goal |
|---|---|---|
| **M0** | [`milestones/M0_BASELINE_LOCK.md`](./milestones/M0_BASELINE_LOCK.md) | Freeze operational behavior, enumerate proof obligations |
| **M1** | [`milestones/M1_DECLARATIVE_SEMANTICS.md`](./milestones/M1_DECLARATIVE_SEMANTICS.md) | Introduce inductive path relation over service dependency graph |
| **M2** | [`milestones/M2_BFS_SOUNDNESS.md`](./milestones/M2_BFS_SOUNDNESS.md) | Prove BFS soundness bridge (false → no declarative path) |
| **M3** | [`milestones/M3_EDGE_INSERTION.md`](./milestones/M3_EDGE_INSERTION.md) | Prove edge-insertion preserves acyclicity, eliminate `sorry` |
| **M4** | [`milestones/M4_EXECUTABLE_EVIDENCE.md`](./milestones/M4_EXECUTABLE_EVIDENCE.md) | Expand runtime test suite with deeper graph topologies |
| **M5** | [`milestones/M5_CLOSURE_SYNC.md`](./milestones/M5_CLOSURE_SYNC.md) | Synchronize documentation, run full validation gates |

### Appendices

| Appendix | Document | Purpose |
|---|---|---|
| **A** | [`appendices/A_SOURCE_CODE_REFERENCE.md`](./appendices/A_SOURCE_CODE_REFERENCE.md) | Annotated source excerpts for all proof-relevant definitions |
| **B** | [`appendices/B_CROSS_REFERENCE_MAP.md`](./appendices/B_CROSS_REFERENCE_MAP.md) | Bidirectional mapping between execution plan and repository artifacts |

---

## Status dashboard

| Milestone | Status | Key deliverable | Blocking risk |
|---|---|---|---|
| M0 | `PENDING` | Proof-target map, store lemma inventory | None |
| M1 | `PENDING` | `serviceEdge`, `serviceReachable`, 5 structural lemmas | None |
| M2 | `PENDING` | `serviceHasPathTo_false_implies_not_reachable` | R1: Fuel adequacy |
| M3 | `PENDING` | `sorry` elimination in preservation theorem | R3: BFS loop invariant |
| M4 | `PENDING` | 3+ new test cases in `NegativeStateSuite.lean` | None |
| M5 | `PENDING` | All 4 doc files updated, `test_full.sh` passes | R4: Documentation drift |

## Milestone dependency graph

```
M0 ──→ M1 ──→ M2 ──→ M3 ──→ M4 ──→ M5
                              │
                              └── sorry eliminated here
```

All milestones are strictly sequential — each depends on the prior milestone's definitions and lemmas. M4 and M5 are logically independent of each other but both depend on M3 for the proof closure.

## Quick-start reading order

1. **Understand the problem:** [`03_ROOT_CAUSE_ANALYSIS.md`](./03_ROOT_CAUSE_ANALYSIS.md)
2. **See the proof plan:** [`04_THEOREM_DEPENDENCY_GRAPH.md`](./04_THEOREM_DEPENDENCY_GRAPH.md)
3. **Assess risk:** [`05_RISK_REGISTER.md`](./05_RISK_REGISTER.md)
4. **Implement sequentially:** M0 → M1 → M2 → M3 → M4 → M5

## Relationship to prior execution strategy

This multi-file execution plan expands and supersedes the former monolithic `AUDIT_v0.11.0_TPI-D07_EXECUTION_STRATEGY.md` (deleted as redundant). All substantive content has been preserved, refined, and extended with:

- More precise Lean 4 proof tactic suggestions for each lemma
- Expanded BFS loop invariant formalization with explicit well-founded recursion analysis
- Concrete `storeServiceState` frame-condition reasoning patterns
- Refined fuel adequacy analysis grounded in the actual `services : ServiceId → Option ServiceGraphEntry` domain
- Additional edge cases and proof obligations identified through direct code inspection
- Explicit decision records for the invariant-definition strategy (Option 1 vs Option 2)
