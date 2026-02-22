# Milestone M5 — Closure Synchronization and Documentation Hygiene

**Goal:** Satisfy the tracked-issue closure contract across all documentation surfaces and CI gates. Ensure no residual mentions of deferred `sorry` for TPI-D07 exist.

**Dependency:** M3 (proof closure) and M4 (test expansion)

**Estimated changes:** 4 documentation files updated, full test gate run

---

## 1. Documentation updates

### 1.1 Update tracked proof issue status

**File:** `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`

**Current state (line 214):**
```markdown
## Issue TPI-D07 (IN PROGRESS) — Service dependency acyclicity invariant
```

**Required changes:**

1. Change header status from `IN PROGRESS` to `CLOSED`:
   ```markdown
   ## Issue TPI-D07 (CLOSED) — Service dependency acyclicity invariant
   ```

2. Update the "Current status" bullet to reflect completed proof.

3. Remove the "Remaining obligation" bullet.

4. Replace "Partially closed theorem obligation (uses `sorry`)" with the final theorem signature and resolution summary:

   ```markdown
   - **Resolution:** `sorry` eliminated from `serviceRegisterDependency_preserves_acyclicity`.
     [Describe the proof approach used — either vacuous closure or full proof infrastructure,
     depending on which path was taken in M3.]

   Closed theorem obligation:

   ```lean
   theorem serviceRegisterDependency_preserves_acyclicity
       (svcId depId : ServiceId) (st st' : SystemState)
       (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
       (hAcyc : serviceDependencyAcyclic st) :
       serviceDependencyAcyclic st' := by
     ... -- complete proof, no sorry
   ```
   ```

### 1.2 Update workstream plan completion evidence

**File:** `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`

**Current state (line 337):**
```
theorem uses `sorry` for BFS soundness (tracked as TPI-D07)
```

**Required changes:**

1. Remove the qualifier `TPI-D07 partially closed (BFS soundness sorry tracked)` from the WS-D4 completion evidence paragraph.

2. Update the F-07 completion evidence to state the preservation theorem is proved without `sorry`.

3. Update the status dashboard entry for WS-D4 to remove the `TPI-D07 partially closed` note.

**Specific lines to update:**

- Line 337: Remove `(BFS soundness uses sorry, tracked)` → replace with `(no sorry)`
- Line 473: Remove `TPI-D07 partially closed (BFS soundness sorry tracked)` → replace with `TPI-D07 closed`

### 1.3 Update claim-evidence index

**File:** `docs/CLAIM_EVIDENCE_INDEX.md`

**Current state (line 37):**
```
| TPI-D07 | Service dependency acyclicity invariant (BFS soundness `sorry` tracked) | WS-D4 | IN PROGRESS |
```

**Required change:**
```
| TPI-D07 | Service dependency acyclicity invariant | WS-D4 | CLOSED |
```

### 1.4 Update proof and invariant map

**File:** `docs/gitbook/12-proof-and-invariant-map.md`

**Current state (line 204):**
```
- `serviceRegisterDependency_preserves_acyclicity` — preservation theorem (uses `sorry` for BFS soundness; tracked as TPI-D07)
```

**Required changes:**

1. Remove `(uses sorry for BFS soundness; tracked as TPI-D07)` → replace with `(no sorry)`

2. If the full proof infrastructure was built (Path B from M3), add entries for new intermediate lemmas:
   - `serviceEdge` — direct dependency edge relation
   - `serviceReachable` — reflexive-transitive closure
   - `serviceHasNontrivialPath` — non-trivial path
   - `serviceDependencyAcyclicDecl` — declarative acyclicity
   - `serviceHasPathTo_true_implies_reachable` — BFS completeness
   - `serviceHasPathTo_false_implies_not_reachable` — BFS soundness
   - `serviceReachable_post_insert_cases` — edge-insertion path decomposition
   - `nontrivial_cycle_post_insert_implies_pre_reach` — cycle analysis

3. If vacuous closure (Path A from M3), add a note explaining the invariant's current semantics.

---

## 2. Hygiene verification

### 2.1 `sorry` audit

After all changes, verify no `sorry` remains in the service proof surface:

```bash
rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean
# Expected: 0 matches
```

### 2.2 TPI-D07 status audit

Verify no documentation still references TPI-D07 as IN PROGRESS:

```bash
rg 'TPI-D07.*IN PROGRESS' docs/
# Expected: 0 matches

rg 'sorry.*TPI-D07\|TPI-D07.*sorry' docs/
# Expected: 0 matches
```

### 2.3 Tier-0 hygiene exclusion

Check whether `test_tier0_hygiene.sh` has a specific sorry-exclusion pattern for TPI-D07. If so, determine whether it can be tightened now that the `sorry` is eliminated:

```bash
rg 'TPI-D07\|TPI-D' scripts/test_tier0_hygiene.sh
```

---

## 3. Full validation gate sequence

Execute the complete tiered validation to confirm all gates pass:

```bash
# 1. Fast gate (Tier 0–1): hygiene + build
./scripts/test_fast.sh

# 2. Smoke gate
./scripts/test_smoke.sh

# 3. Negative suite (Tier 2): runtime cycle-detection validation
./scripts/test_tier2_negative.sh

# 4. Invariant surface (Tier 3): symbol anchors + doc consistency
./scripts/test_tier3_invariant_surface.sh

# 5. Full gate (Tier 0–3): complete validation
./scripts/test_full.sh
```

### 3.1 Optional extended validation

```bash
# Nightly gate (Tier 0–4): includes experimental/candidate tests
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

---

## 4. Manual verification checklist

| # | Check | Command | Expected |
|---|---|---|---|
| 1 | No `sorry` in Service/Invariant.lean | `rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean` | 0 matches |
| 2 | No TPI-D07 IN PROGRESS in docs | `rg 'TPI-D07.*IN PROGRESS' docs/` | 0 matches |
| 3 | No sorry+TPI-D07 co-occurrence | `rg 'sorry.*TPI-D07\|TPI-D07.*sorry' docs/` | 0 matches |
| 4 | TRACKED_PROOF_ISSUES shows CLOSED | Manual inspection of line 214 | `(CLOSED)` |
| 5 | CLAIM_EVIDENCE_INDEX shows CLOSED | Manual inspection of line 37 | `CLOSED` |
| 6 | Proof map shows (no sorry) | Manual inspection of section 13 | `(no sorry)` |
| 7 | New lemma names in proof map | Manual inspection | All new lemmas listed |
| 8 | Tier 0–3 gates pass | `./scripts/test_full.sh` | Exit 0 |

---

## 5. Landing strategy

All documentation updates must land in the **same commit/PR** as the proof closure to prevent documentation drift. The recommended commit structure:

1. **Commit 1:** M0–M3 proof infrastructure and `sorry` elimination
2. **Commit 2:** M4 test expansion
3. **Commit 3:** M5 documentation updates
4. **Single PR** containing all three commits

Alternatively, a single atomic commit is acceptable if the changes are not too large to review.

---

## 6. Exit criteria

- [ ] `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`: TPI-D07 status = CLOSED
- [ ] `AUDIT_v0.11.0_WORKSTREAM_PLAN.md`: no `sorry` deferred qualifier for TPI-D07
- [ ] `CLAIM_EVIDENCE_INDEX.md`: TPI-D07 status = CLOSED
- [ ] `gitbook/12-proof-and-invariant-map.md`: preservation theorem marked `(no sorry)`
- [ ] No residual `sorry` mentions for TPI-D07 in any documentation
- [ ] `./scripts/test_full.sh` exits 0
- [ ] All changes land in a single PR

## Artifacts modified

- `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`
- `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`
- `docs/CLAIM_EVIDENCE_INDEX.md`
- `docs/gitbook/12-proof-and-invariant-map.md`
