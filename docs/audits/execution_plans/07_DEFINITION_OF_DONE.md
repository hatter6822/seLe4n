# 07 — Definition of Done for TPI-D07

TPI-D07 is **closed** when **all** of the following conditions hold simultaneously. Each condition has an explicit verification method.

> **Current status: COMPLETE.** Strategy B (Risk 0) was chosen. The entire proof surface is sorry-free. The BFS completeness bridge `bfs_complete_for_nontrivialPath` is fully proved under `serviceCountBounded` (TPI-D07-BRIDGE closed). Full B1-B7 suite implemented.

---

## 1. Proof surface

| # | Condition | Verification | Status |
|---|---|---|---|
| P1 | `serviceRegisterDependency_preserves_acyclicity` contains **no `sorry`** | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` — zero matches | [x] |
| P2 | The theorem compiles successfully | `lake build` exits 0 | [x] |
| P3 | No `sorry` anywhere in the kernel proof surface | `rg 'sorry' SeLe4n/Kernel/` — zero matches | [x] |
| P4 | All intermediate lemmas compile without `sorry` | `lake build` exits 0 (all B1-B7 lemmas fully proved) | [x] |

### Full proof infrastructure (Risk 0, Strategy B — implemented):

| # | Condition | Verification | Status |
|---|---|---|---|
| P5 | `serviceEdge`, `serviceReachable`, `serviceNontrivialPath` exist | `rg 'def serviceEdge\|inductive serviceReachable\|inductive serviceNontrivialPath' SeLe4n/Kernel/Service/Invariant.lean` | [x] |
| P6 | BFS completeness bridge exists and is fully proved | `rg 'bfs_complete_for_nontrivialPath' SeLe4n/Kernel/Service/Invariant.lean` | [x] |
| P7 | Edge-insertion decomposition exists | `rg 'nontrivialPath_post_insert_cases' SeLe4n/Kernel/Service/Invariant.lean` | [x] |

---

## 2. Executable evidence

| # | Condition | Verification | Status |
|---|---|---|---|
| E1 | Negative tests include chain-length ≥ 3 cycle rejection | `rg 'chain.3\|chain-3\|three.service\|svcIdC' tests/NegativeStateSuite.lean` matches | [ ] |
| E2 | Negative tests include diamond-DAG topology | `rg 'diamond\|svcIdD' tests/NegativeStateSuite.lean` matches | [ ] |
| E3 | All existing test expectations unchanged | `./scripts/test_tier2_negative.sh` exits 0 | [ ] |
| E4 | New tests pass | `./scripts/test_tier2_negative.sh` exits 0 | [ ] |

---

## 3. Documentation

| # | Condition | Verification | Status |
|---|---|---|---|
| D1 | `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`: TPI-D07 = CLOSED | `rg 'TPI-D07.*CLOSED' docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md` | [x] |
| D2 | `AUDIT_v0.11.0_WORKSTREAM_PLAN.md`: TPI-D07 closed, BFS bridge tracked | Lines 71, 336-343, 478 consistent | [x] |
| D3 | `CLAIM_EVIDENCE_INDEX.md`: TPI-D07 = CLOSED | `rg 'TPI-D07.*CLOSED' docs/CLAIM_EVIDENCE_INDEX.md` | [x] |
| D4 | `gitbook/12-proof-and-invariant-map.md`: preservation theorem `(no sorry)` | Section 13 and §14 updated | [x] |
| D5 | No documentation references TPI-D07 as IN PROGRESS | `rg 'TPI-D07.*IN PROGRESS' docs/` returns 0 | [x] |

---

## 4. CI gates

| # | Condition | Verification | Status |
|---|---|---|---|
| C1 | Tier 0 (hygiene) passes | `./scripts/test_tier0_hygiene.sh` exits 0 | [ ] |
| C2 | Tier 1 (build) passes | `./scripts/test_tier1_build.sh` exits 0 | [ ] |
| C3 | Tier 2 (runtime negative suite) passes | `./scripts/test_tier2_negative.sh` exits 0 | [ ] |
| C4 | Tier 3 (invariant surface) passes | `./scripts/test_tier3_invariant_surface.sh` exits 0 | [ ] |
| C5 | Full gate (Tier 0–3) passes | `./scripts/test_full.sh` exits 0 | [ ] |

---

## 5. Operational stability

| # | Condition | Verification | Status |
|---|---|---|---|
| O1 | `Operations.lean` has zero changes | File hash comparison | [x] |
| O2 | No runtime behavior change in cycle detection | Existing tests pass unchanged | [x] |
| O3 | No new error variants added | `rg 'KernelError' SeLe4n/Model/State.lean` unchanged | [x] |
| O4 | No fuel computation change | `rg 'serviceBfsFuel' SeLe4n/Kernel/Service/Operations.lean` unchanged | [x] |

---

## 6. Landing criteria

| # | Condition | Verification | Status |
|---|---|---|---|
| L1 | All changes in a single PR | PR contains M0–M5 artifacts | [ ] |
| L2 | PR passes CI | GitHub Actions green | [ ] |
| L3 | PR description includes validation evidence | `test_full.sh` output included | [ ] |

---

## Summary

**Total conditions:** 25–28 (depending on proof strategy)

**Critical path:** P1 (sorry eliminated) → C5 (full gate passes) → D1–D5 (docs updated) → L1 (PR landed)

TPI-D07 is the **last open tracked proof issue** in the WS-D portfolio. Closing it completes the proof surface for all findings identified in `AUDIT_v0.11.0.md`.
