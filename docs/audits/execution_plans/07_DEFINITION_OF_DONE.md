# 07 — Definition of Done for TPI-D07

TPI-D07 is **closed** when **all** of the following conditions hold simultaneously. Each condition has an explicit verification method.

---

## 1. Proof surface

| # | Condition | Verification | Status |
|---|---|---|---|
| P1 | `serviceRegisterDependency_preserves_acyclicity` contains **no `sorry`** | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` returns 0 matches | [ ] |
| P2 | The theorem compiles successfully | `lake build` exits 0 | [ ] |
| P3 | No new `sorry` introduced anywhere in the kernel proof surface | `rg 'sorry' SeLe4n/Kernel/` returns same or fewer matches than before | [ ] |
| P4 | All intermediate lemmas (if any) compile without `sorry` | `lake build` exits 0 | [ ] |

### If full proof infrastructure is built (Risk 0, Strategy B):

| # | Condition | Verification | Status |
|---|---|---|---|
| P5 | `serviceEdge` and `serviceReachable` definitions exist | `rg 'def serviceEdge\|inductive serviceReachable' SeLe4n/Kernel/Service/Invariant.lean` | [ ] |
| P6 | BFS soundness bridge exists | `rg 'serviceHasPathTo_false_implies_not_reachable\|serviceHasPathTo_true_implies_reachable' SeLe4n/Kernel/Service/Invariant.lean` | [ ] |
| P7 | Edge-insertion decomposition exists | `rg 'serviceReachable_post_insert_cases\|nontrivial_cycle_post_insert_implies_pre_reach' SeLe4n/Kernel/Service/Invariant.lean` | [ ] |

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
| D1 | `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`: TPI-D07 = CLOSED | `rg 'TPI-D07.*CLOSED' docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md` | [ ] |
| D2 | `AUDIT_v0.11.0_WORKSTREAM_PLAN.md`: no "sorry deferred" qualifier | `rg 'sorry.*TPI-D07\|TPI-D07.*sorry' docs/audits/` returns 0 | [ ] |
| D3 | `CLAIM_EVIDENCE_INDEX.md`: TPI-D07 = CLOSED | `rg 'TPI-D07.*CLOSED' docs/CLAIM_EVIDENCE_INDEX.md` | [ ] |
| D4 | `gitbook/12-proof-and-invariant-map.md`: theorem marked `(no sorry)` | Manual inspection of section 13 | [ ] |
| D5 | No documentation references TPI-D07 as IN PROGRESS | `rg 'TPI-D07.*IN PROGRESS' docs/` returns 0 | [ ] |

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
| O1 | `Operations.lean` has zero changes | File hash comparison | [ ] |
| O2 | No runtime behavior change in cycle detection | Existing tests pass unchanged | [ ] |
| O3 | No new error variants added | `rg 'KernelError' SeLe4n/Model/State.lean` unchanged | [ ] |
| O4 | No fuel computation change | `rg 'serviceBfsFuel' SeLe4n/Kernel/Service/Operations.lean` unchanged | [ ] |

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
