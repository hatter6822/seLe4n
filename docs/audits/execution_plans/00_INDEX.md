# TPI-D07 Execution Plan — Master Index

## Service Dependency Acyclicity Invariant: `sorry` Elimination

**Target:** Replace the deferred `sorry` on `serviceRegisterDependency_preserves_acyclicity` with a complete formal proof. The main preservation theorem is now sorry-free (line 591). The sole remaining `sorry` is on `bfs_complete_for_nontrivialPath` (line 531, annotated TPI-D07-BRIDGE).

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
| **M2** | [`milestones/M2_BFS_SOUNDNESS.md`](./milestones/M2_BFS_SOUNDNESS.md) | BFS completeness bridge — overview, architecture, theorem inventory |
| M2-A | [`milestones/M2A_EQUATIONAL_THEORY.md`](./milestones/M2A_EQUATIONAL_THEORY.md) | BFS `go` equational lemmas (EQ1–EQ5) |
| M2-B | [`milestones/M2B_COMPLETENESS_INVARIANT.md`](./milestones/M2B_COMPLETENESS_INVARIANT.md) | Loop invariant, closure property, boundary lemma |
| M2-C | [`milestones/M2C_FUEL_ADEQUACY.md`](./milestones/M2C_FUEL_ADEQUACY.md) | Fuel adequacy analysis and precondition design |
| M2-D | [`milestones/M2D_COMPLETENESS_PROOF.md`](./milestones/M2D_COMPLETENESS_PROOF.md) | Complete proof walkthrough for CP1 and wrappers |
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
| M2 | `IN PREPARATION` | Documentation expanded into 4 sub-documents (M2A–M2D) with detailed proof path; 13 lemmas + 2 definitions planned to eliminate `sorry` on `bfs_complete_for_nontrivialPath` | R1: Fuel adequacy, R3: BFS loop invariant |
| M3 | `COMPLETE` | `serviceRegisterDependency_preserves_acyclicity` is sorry-free; `nontrivialPath_post_insert_cases` proved | None (uses M2 bridge with `sorry`) |
| M4 | `PARTIAL` | Depth-5 chain smoke test exists in `MainTraceHarness`; dedicated `NegativeStateSuite` expansion pending | None |
| M5 | `IN PROGRESS` | Canonical docs updated; execution plan status sync in progress | R4: Documentation drift |

## Milestone dependency graph

```
M0 ──→ M1 ──→ M2 ──────────→ M3 ──→ M4 ──→ M5
  ✓       ✓    in preparation    ✓    partial  in progress
               │                 │
               ├─ M2A (equational)
               ├─ M2B (invariant)  └── preservation theorem sorry-free
               ├─ M2C (fuel)           (BFS bridge sorry targeted at M2)
               └─ M2D (proof)
```

M1 and M3 are complete. M2 (BFS completeness) has been expanded from a single deferred document into four detailed sub-documents (M2A–M2D) providing a complete proof roadmap: 13 lemmas + 2 definitions targeting the `sorry` on `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE). The proof strategy uses a visited-set closure invariant with a preconditioned fuel adequacy hypothesis. M4 and M5 are logically independent of each other but both depend on M3 for the proof closure.

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
