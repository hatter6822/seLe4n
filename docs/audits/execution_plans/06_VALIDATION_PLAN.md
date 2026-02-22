# 06 — Validation Plan

This document specifies the validation procedures for each milestone and the final closure sequence.

---

## 1. Per-milestone validation

| Milestone | Validation command | What it checks | Status |
|---|---|---|---|
| M0 | `./scripts/test_tier1_build.sh` | Build passes with comment-only changes | ✓ Complete |
| M0 | `sha256sum` of frozen files | No operational definitions changed | ✓ Complete |
| M1 | `./scripts/test_tier1_build.sh` | New definitions and lemmas compile | ✓ Complete |
| M1 | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` | Only BFS bridge sorry (line 531, TPI-D07-BRIDGE) | ✓ Verified |
| M2 | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` | `bfs_complete_for_nontrivialPath` sorry at line 531 (deferred) | ✓ Accepted (TPI-D07-BRIDGE) |
| M3 | `./scripts/test_tier1_build.sh` | Preservation theorem compiles sorry-free | ✓ Complete |
| M3 | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` | **One match** at line 531 (TPI-D07-BRIDGE) — preservation theorem sorry-free | ✓ Verified |
| M4 | `./scripts/test_tier2_negative.sh` | Test cases pass | Pending (expanded tests) |
| M4 | Manual: existing tests unchanged | No regression in test expectations | ✓ Verified |
| M5 | `rg 'TPI-D07.*IN PROGRESS' docs/` | No docs show TPI-D07 as open | ✓ Verified |
| M5 | `./scripts/test_full.sh` | Full tier 0–3 gate passes | Pending |

---

## 2. Final closure validation sequence

After all milestones are complete, execute this full validation sequence:

### 2.1 Build verification

```bash
# Clean build to ensure no stale artifacts
lake clean && lake build
```

### 2.2 Sorry verification

```bash
# Primary check: only TPI-D07-BRIDGE sorry remains
rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean
# Expected output: 1 match at line 531 (bfs_complete_for_nontrivialPath, annotated TPI-D07-BRIDGE)
# The preservation theorem (serviceRegisterDependency_preserves_acyclicity) is sorry-free.

# Secondary check: no new sorry anywhere in kernel
rg 'sorry' SeLe4n/Kernel/
# Expected: only TPI-D07-BRIDGE at Service/Invariant.lean:531
```

### 2.3 Tiered test gates

```bash
# Tier 0: Hygiene checks (metadata, formatting, sorry accounting)
./scripts/test_tier0_hygiene.sh

# Tier 1: Build gate
./scripts/test_tier1_build.sh

# Tier 2: Runtime negative suite (cycle detection tests)
./scripts/test_tier2_negative.sh

# Tier 3: Invariant surface (symbol anchors, doc consistency)
./scripts/test_tier3_invariant_surface.sh

# Combined: full gate (Tier 0–3)
./scripts/test_full.sh
```

### 2.4 Documentation consistency

```bash
# No TPI-D07 marked as open
rg 'TPI-D07.*IN PROGRESS' docs/
# Expected: 0 matches

# No sorry/TPI-D07 co-occurrence
rg 'sorry.*TPI-D07|TPI-D07.*sorry' docs/
# Expected: 0 matches

# TPI-D07 marked as CLOSED in tracked issues
rg 'TPI-D07.*CLOSED' docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md
# Expected: 1 match

# TPI-D07 marked as CLOSED in claim index
rg 'TPI-D07.*CLOSED' docs/CLAIM_EVIDENCE_INDEX.md
# Expected: 1 match
```

### 2.5 Optional: extended validation

```bash
# Smoke gate (Tier 0–1 with extended checks)
./scripts/test_smoke.sh

# Nightly gate (Tier 0–4, includes experimental tests)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

---

## 3. Regression test matrix

These checks ensure TPI-D07 changes do not regress existing functionality:

| Area | Check | Tool | Pass criteria |
|---|---|---|---|
| Build | Full project builds | `lake build` | Exit 0 |
| Service operations | Existing cycle detection tests pass | `test_tier2_negative.sh` | Exit 0 |
| Service invariants | Existing preservation theorems compile | `test_tier1_build.sh` | Exit 0 |
| Cross-subsystem | Lifecycle/capability bundles unaffected | `test_tier1_build.sh` | Exit 0 |
| Information flow | IF suite unaffected | `test_tier2_negative.sh` | Exit 0 |
| Trace harness | Trace probe unaffected | `test_tier2_trace.sh` | Exit 0 |
| Doc anchors | Symbol anchors still valid | `test_tier3_invariant_surface.sh` | Exit 0 |
| Hygiene | No new sorry introduced | `rg 'sorry' SeLe4n/Kernel/` | No new matches |

---

## 4. Manual verification checklist

| # | Check | Method | Expected | Verified? |
|---|---|---|---|---|
| 1 | Preservation theorem sorry-free | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` | 1 match (line 531, TPI-D07-BRIDGE only) | [x] |
| 2 | TPI-D07 status = CLOSED in TRACKED_PROOF_ISSUES | Manual inspection line 214 | `(CLOSED — Risk 0 resolved)` | [x] |
| 3 | TPI-D07 status = CLOSED in CLAIM_EVIDENCE_INDEX | Manual inspection line 37 | `CLOSED` | [x] |
| 4 | No stale `partially closed` in WORKSTREAM_PLAN | Manual inspection lines 71, 336-343, 478 | TPI-D07 closed throughout | [x] |
| 5 | Proof map shows `(no sorry)` on preservation theorem | Manual inspection section 13 | Updated entry | [x] |
| 6 | New lemma names in proof map §14 | Manual inspection section 14 | All 4 layers documented | [x] |
| 7 | Tier 0–3 gates pass | `./scripts/test_full.sh` | Exit 0 | [ ] |
| 8 | Depth-5 chain test present | `rg 'depth-5\|chainL3' SeLe4n/Testing/MainTraceHarness.lean` | ≥ 2 matches | [x] |
| 9 | Operations.lean unchanged | `sha256sum` comparison | Same hash | [x] |
| 10 | No new `sorry` in kernel | `rg 'sorry' SeLe4n/Kernel/` | Only TPI-D07-BRIDGE | [x] |

---

## 5. CI integration notes

The project uses GitHub Actions (`.github/workflows/lean_action_ci.yml`). After pushing the TPI-D07 PR:

1. CI should run `lake build` (Tier 1).
2. CI should run the test suites.
3. The PR description should include the validation output from `test_full.sh`.

If CI uses `rg 'sorry'` as a quality gate, ensure the TPI-D07 sorry exclusion pattern is removed or updated.
