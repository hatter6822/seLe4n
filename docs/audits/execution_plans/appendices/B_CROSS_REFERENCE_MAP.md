# Appendix B — Cross-Reference Map

This appendix provides bidirectional mappings between the execution plan documents and the repository artifacts they reference.

> **Note:** Line references in sections 1-3 reflect the **pre-implementation** state. After the full TPI-D07 proof infrastructure was implemented (including the complete B1-B7 BFS soundness bridge), code was added to `Invariant.lean` shifting line numbers significantly. Key current locations: `serviceEdge` at line 388, `serviceDependencyAcyclic` at line 410, `serviceCountBounded` at line 611, `go_complete` (B4) at line 670, `bfs_complete_for_nontrivialPath` (B6) at line 841, `nontrivialPath_post_insert_cases` at line 871, `serviceRegisterDependency_preserves_acyclicity` at line 922. Total file length: 1007 lines.

---

## 1. Execution plan → Repository artifact

| Plan section | Repository artifact | Relationship |
|---|---|---|
| [02_CODEBASE_AUDIT §2](../02_CODEBASE_AUDIT.md#2-cycle-prevention-operational-logic) | `Operations.lean:142–160` | Direct code audit of `serviceRegisterDependency` |
| [02_CODEBASE_AUDIT §3](../02_CODEBASE_AUDIT.md#3-bounded-bfs-reachability) | `Operations.lean:96–127` | BFS algorithm and fuel analysis |
| [02_CODEBASE_AUDIT §4](../02_CODEBASE_AUDIT.md#4-invariant-definition-and-proof-state) | `Invariant.lean:349–394` | Invariant definition and proof skeleton |
| [02_CODEBASE_AUDIT §5](../02_CODEBASE_AUDIT.md#5-executable-evidence-baseline) | `NegativeStateSuite.lean:319–367` | Test coverage audit |
| [03_ROOT_CAUSE_ANALYSIS §5](../03_ROOT_CAUSE_ANALYSIS.md#5-proof-state-evolution-through-the-insertion-branch) | `Invariant.lean:394` | Exact goal state at `sorry` |
| [M0 §M0.4](../milestones/M0_BASELINE_LOCK.md#m04--store-lemma-inventory) | `State.lean:180–193` | Store lemma dependency |
| [M1 §3](../milestones/M1_DECLARATIVE_SEMANTICS.md#3-store-interaction-lemmas) | `State.lean:180–193` | Store lemma wrapping |
| [M4 §2](../milestones/M4_EXECUTABLE_EVIDENCE.md#2-test-cases) | `NegativeStateSuite.lean:319–367` | Test expansion target |
| [M5 §1.1](../milestones/M5_CLOSURE_SYNC.md#11-update-tracked-proof-issue-status) | `TRACKED_PROOF_ISSUES.md:214–236` | Status update target |
| [M5 §1.2](../milestones/M5_CLOSURE_SYNC.md#12-update-workstream-plan) | `WORKSTREAM_PLAN.md:331–338` | Completion evidence target |
| [M5 §1.3](../milestones/M5_CLOSURE_SYNC.md#13-update-claim-evidence-index) | `CLAIM_EVIDENCE_INDEX.md:37` | Status update target |
| [M5 §1.4](../milestones/M5_CLOSURE_SYNC.md#14-update-proof-and-invariant-map) | `12-proof-and-invariant-map.md:195–204` | Theorem catalog target |

---

## 2. Repository artifact → Execution plan

| Repository artifact | Plan documents | How it's used |
|---|---|---|
| `SeLe4n/Kernel/Service/Operations.lean` | [02_CODEBASE_AUDIT](../02_CODEBASE_AUDIT.md), [Appendix A](./A_SOURCE_CODE_REFERENCE.md) | Audited (frozen — no changes) |
| `SeLe4n/Kernel/Service/Invariant.lean` | [02_CODEBASE_AUDIT](../02_CODEBASE_AUDIT.md), [03_ROOT_CAUSE](../03_ROOT_CAUSE_ANALYSIS.md), [M0](../milestones/M0_BASELINE_LOCK.md)–[M3](../milestones/M3_EDGE_INSERTION.md), [Appendix A](./A_SOURCE_CODE_REFERENCE.md) | **Primary modification target** |
| `SeLe4n/Model/State.lean` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [M0](../milestones/M0_BASELINE_LOCK.md), [M1](../milestones/M1_DECLARATIVE_SEMANTICS.md), [Appendix A](./A_SOURCE_CODE_REFERENCE.md) | Store lemma source (may add new lemmas) |
| `SeLe4n/Model/Object.lean` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [Appendix A](./A_SOURCE_CODE_REFERENCE.md) | Data model reference (frozen) |
| `SeLe4n/Prelude.lean` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [Appendix A](./A_SOURCE_CODE_REFERENCE.md) | Type definitions reference (frozen) |
| `tests/NegativeStateSuite.lean` | [02_CODEBASE_AUDIT](../02_CODEBASE_AUDIT.md), [M4](../milestones/M4_EXECUTABLE_EVIDENCE.md) | Test expansion target |
| `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [M5](../milestones/M5_CLOSURE_SYNC.md), [07_DOD](../07_DEFINITION_OF_DONE.md) | Documentation update target |
| `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [M5](../milestones/M5_CLOSURE_SYNC.md), [07_DOD](../07_DEFINITION_OF_DONE.md) | Documentation update target |
| `docs/CLAIM_EVIDENCE_INDEX.md` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [M5](../milestones/M5_CLOSURE_SYNC.md), [07_DOD](../07_DEFINITION_OF_DONE.md) | Documentation update target |
| `docs/gitbook/12-proof-and-invariant-map.md` | [01_PURPOSE](../01_PURPOSE_AND_SCOPE.md), [M5](../milestones/M5_CLOSURE_SYNC.md), [07_DOD](../07_DEFINITION_OF_DONE.md) | Documentation update target |
| `scripts/test_*.sh` | [06_VALIDATION](../06_VALIDATION_PLAN.md) | Validation commands |
| `docs/audits/AUDIT_v0.11.0_TPI-D07_EXECUTION_STRATEGY.md` | [00_INDEX](../00_INDEX.md) | Superseded and deleted — content absorbed into this execution plan |

---

## 3. Theorem → File location map

| Theorem / Definition | Planned file | Section |
|---|---|---|
| `serviceEdge` (D1) | `Service/Invariant.lean` | Between line 340 and 349 |
| `serviceReachable` (D2) | `Service/Invariant.lean` | Between line 340 and 349 |
| `serviceHasNontrivialPath` (D3) | `Service/Invariant.lean` | Between line 340 and 349 |
| `serviceDependencyAcyclicDecl` (D4) | `Service/Invariant.lean` | Between line 340 and 349 |
| `serviceEdge_iff_mem` (L1) | `Service/Invariant.lean` | After D1 |
| `serviceReachable_trans` (L2) | `Service/Invariant.lean` | After D2 |
| `serviceReachable_of_edge` (L3) | `Service/Invariant.lean` | After D2 |
| `serviceReachable_step_right` (L4) | `Service/Invariant.lean` | After L2, L3 |
| `serviceHasNontrivialPath_of_edge` (L5) | `Service/Invariant.lean` | After D3 |
| `storeServiceState_objectIndex_eq` (S1) | `Service/Invariant.lean` or `State.lean` | Frame conditions section |
| `serviceBfsFuel_storeServiceState_eq` (S2) | `Service/Invariant.lean` | After S1 |
| `serviceEdge_storeServiceState_eq` (S3) | `Service/Invariant.lean` | After D1 |
| `serviceEdge_storeServiceState_ne` (S4) | `Service/Invariant.lean` | After D1 |
| `serviceEdge_post_insert` (S5) | `Service/Invariant.lean` | After S3 |
| `serviceHasPathTo_go_true_implies_exists_reachable` (B1) | `Service/Invariant.lean` | BFS soundness section |
| `serviceHasPathTo_true_implies_reachable` (B2) | `Service/Invariant.lean` | After B1 |
| `serviceHasPathTo_true_implies_nontrivial` (B3) | `Service/Invariant.lean` | After B2 |
| `serviceHasPathTo_go_invariant` / `go_complete` (B4) | `Service/Invariant.lean` | BFS soundness section |
| `serviceBfsFuel_sufficient` (B5) | `Service/Invariant.lean` | After B4 |
| `serviceHasPathTo_false_implies_not_reachable` (B6) | `Service/Invariant.lean` | After B4, B5 |
| `serviceHasPathTo_false_implies_not_nontrivial` (B7) | `Service/Invariant.lean` | After B6 |
| `serviceEdge_post_cases` (E1) | `Service/Invariant.lean` | Edge insertion section |
| `serviceReachable_post_insert_of_pre` (E2) | `Service/Invariant.lean` | After E1 |
| `serviceReachable_post_insert_cases` (E3) | `Service/Invariant.lean` | After E1 |
| `nontrivial_cycle_post_insert_implies_pre_reach` (E4) | `Service/Invariant.lean` | After E3 |
| `serviceDependencyAcyclicDecl_preserved` (E5) | `Service/Invariant.lean` | After E4 |
| `serviceDependencyAcyclic_implies_acyclicDecl` (EQ1) | `Service/Invariant.lean` | Equivalence section |
| `serviceDependencyAcyclicDecl_implies_acyclic` (EQ2) | `Service/Invariant.lean` | Equivalence section |
| `serviceRegisterDependency_preserves_acyclicity` (F1) | `Service/Invariant.lean:363–394` | **Existing** — sorry replaced |

---

## 4. Risk → Mitigation location map

| Risk | Primary mitigation | Implementation location |
|---|---|---|
| R0 (vacuous invariant) | Verify BFS self-reachability behavior | M0 (baseline audit) |
| R1 (fuel adequacy) | Preconditioned or unconditional fuel bound | M2 (BFS soundness) |
| R2 (list complexity) | Canonical membership lemmas | M1 (structural lemmas) |
| R3 (BFS induction) | Lexicographic induction measure | M2 (loop invariant) |
| R4 (doc drift) | Same-PR landing | M5 (closure sync) |
| R5 (Lean version) | Toolchain lock | M0 (baseline lock) |

---

## 5. Validation gate → Script map

| Gate | Script | Tier |
|---|---|---|
| Hygiene | `scripts/test_tier0_hygiene.sh` | 0 |
| Build | `scripts/test_tier1_build.sh` | 1 |
| Negative suite | `scripts/test_tier2_negative.sh` | 2 |
| Trace probe | `scripts/test_tier2_trace.sh` | 2 |
| Invariant surface | `scripts/test_tier3_invariant_surface.sh` | 3 |
| Fast (Tier 0–1) | `scripts/test_fast.sh` | 0–1 |
| Smoke (Tier 0–2) | `scripts/test_smoke.sh` | 0–2 |
| Full (Tier 0–3) | `scripts/test_full.sh` | 0–3 |
| Nightly (Tier 0–4) | `scripts/test_nightly.sh` | 0–4 |
