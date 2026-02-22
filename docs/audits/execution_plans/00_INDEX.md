# TPI-D07 Execution Plan — Master Index

## Service Dependency Acyclicity Invariant: `sorry` Elimination

**Target:** Replace the deferred `sorry` on `serviceRegisterDependency_preserves_acyclicity` with a complete formal proof. **COMPLETE:** All `sorry` markers have been eliminated. The full B1-B7 BFS soundness bridge is proved, `bfs_complete_for_nontrivialPath` is closed, and `serviceRegisterDependency_preserves_acyclicity` requires only the `serviceCountBounded` fuel adequacy precondition. Zero `sorry` markers remain in the codebase.

**Tracked issue:** TPI-D07 from [`AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](../AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md#issue-tpi-d07-closed--risk-0-resolved--service-dependency-acyclicity-invariant)

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
| M0 | `COMPLETE` | Proof-target map, store lemma inventory, semantics freeze | None |
| M1 | `COMPLETE` | `serviceEdge`, `serviceReachable`, `serviceNontrivialPath`, revised `serviceDependencyAcyclic`, 7 structural + 3 frame lemmas | None |
| M2 | `COMPLETE` | Full B1-B7 BFS soundness bridge proved; `bfs_complete_for_nontrivialPath` closed (no `sorry`); `serviceCountBounded` precondition | None |
| M3 | `COMPLETE` | `serviceRegisterDependency_preserves_acyclicity` is sorry-free; `nontrivialPath_post_insert_cases` proved | None |
| M4 | `PARTIAL` | Depth-5 chain smoke test exists in `MainTraceHarness`; dedicated `NegativeStateSuite` expansion pending | None |
| M5 | `COMPLETE` | All documentation synchronized; execution plan status updated | None |

## Milestone dependency graph

```
M0 ──→ M1 ──→ M2 ──→ M3 ──→ M4 ──→ M5
  ✓       ✓      ✓      ✓    partial    ✓
```

M0 through M3 and M5 are complete. The full B1-B7 BFS soundness bridge is proved in M2, closing TPI-D07-BRIDGE with zero `sorry` markers. The `serviceCountBounded` precondition handles fuel adequacy (Approach A). M4 (executable evidence expansion) is partially complete — the depth-5 chain smoke test exists but dedicated `NegativeStateSuite` expansion is pending.

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
