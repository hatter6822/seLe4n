# Audit Report: PR #179 — M2 BFS Soundness Bridge

**Auditor:** Claude (Opus 4.6)
**Date:** 2026-02-23
**PR Branch:** `claude/bfs-soundness-bridge-UyV5X`
**Milestone:** M2 — BFS Soundness Bridge (`docs/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md`)
**Verdict:** PASS with noted concerns (see §5)

---

## 1. Executive summary

PR #179 eliminates the sole remaining `sorry` on `bfs_complete_for_nontrivialPath`
(TPI-D07-BRIDGE, formerly at `Invariant.lean:531`) by implementing a formal BFS
completeness proof. The proof establishes that if a declarative nontrivial path
exists between two service nodes, the executable BFS (`serviceHasPathTo`) returns
`true` under adequate fuel.

**Key result:** `lake build` produces zero `sorry` warnings. All smoke tests pass.
The acyclicity proof surface is now formally closed.

**Trade-off:** The proof introduces `serviceCountBounded st` as a new precondition
on both `bfs_complete_for_nontrivialPath` and `serviceRegisterDependency_preserves_acyclicity`.
This is the expected Approach A strategy from the M2C fuel adequacy spec.

---

## 2. Files changed (10 files, +353/−109 lines)

| File | Change type | Lines |
|------|------------|-------|
| `SeLe4n/Kernel/Service/Invariant.lean` | Core proof additions | +265 |
| `CLAUDE.md` | Write tool guidance cleanup (unrelated) | −33 |
| `docs/CLAIM_EVIDENCE_INDEX.md` | Status update | ±1 |
| `docs/DEVELOPMENT.md` | Status update | ±6 |
| `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md` | Status update | +17/−12 |
| `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` | Status update | ±5 |
| `docs/audits/execution_plans/00_INDEX.md` | M2 status → COMPLETE | ±10 |
| `docs/audits/execution_plans/milestones/M5_CLOSURE_SYNC.md` | Status update | +3 |
| `docs/gitbook/12-proof-and-invariant-map.md` | Status update | ±11 |
| `docs/spec/SELE4N_SPEC.md` | Status update | ±1 |

---

## 3. M2 exit criteria checklist

| # | Criterion | Status | Location | Notes |
|---|-----------|--------|----------|-------|
| 1 | `lookupDeps` helper defined | **PASS** | `Invariant.lean:517` | Private def, matches M2A spec |
| 2 | `serviceEdge_iff_lookupDeps` bridge proved | **PASS** | `Invariant.lean:521` | Iff proof, no sorry |
| 3 | BFS equational lemmas EQ1–EQ5 | **PARTIAL** | `Invariant.lean:661–677` | EQ3–EQ5 present; EQ1, EQ2 omitted (not needed; see §4.1) |
| 4 | `bfsClosed` definition | **PASS** | `Invariant.lean:533` | Matches M2B spec |
| 5 | CB2 (initial closure) | **PASS** | `Invariant.lean:537` (`bfsClosed_init`) | |
| 6 | CB3 (skip preserves closure) | **PASS** | `Invariant.lean:542` (`bfsClosed_skip`) | |
| 7 | CB4 (expansion preserves closure) | **PASS** | `Invariant.lean:554` (`bfsClosed_expand`) | `_hNV` unused; see §5.5 |
| 8 | CB1 (boundary lemma) | **PASS** | `Invariant.lean:573` (`bfs_boundary_lemma`) | Induction on `serviceReachable`; correct |
| 9 | `serviceCountBounded` defined | **PASS** | `Invariant.lean:752` | Stronger than M2C spec; see §4.2 |
| 10 | CP1 (core loop completeness) | **PASS** | `Invariant.lean:684` (`go_complete`) | Strong induction on fuel + structural on frontier |
| 11 | OW1 + OW2 wrappers | **PARTIAL** | `Invariant.lean:774` | OW1 folded into OW2; see §4.1 |
| 12 | `bfs_complete_for_nontrivialPath` sorry eliminated | **PASS** | `Invariant.lean:774` | No sorry |
| 13 | `lake build` zero sorry in `Service/Invariant.lean` | **PASS** | Verified | Zero warnings |
| 14 | `test_smoke.sh` passes | **PASS** | Verified | All tier 0–2 gates pass |

---

## 4. Deviations from the M2 plan

### 4.1 Omitted lemmas (justified)

Three planned artifacts were omitted, each for valid reasons:

- **EQ1 (`go_zero_eq_false`)**: The fuel-zero case is handled inline in `go_complete`
  by showing `fuel ≠ 0` from the unvisited filter length bound, then destructuring
  `fuel = fuel' + 1`. A separate lemma is unnecessary.

- **EQ2 (`go_nil_eq_false`)**: The empty-frontier case is handled by the structural
  induction base case in `go_complete`, which derives a contradiction from
  `∃ w ∈ [], ...`. No separate lemma needed.

- **OW1 (`serviceHasPathTo_complete_of_reachable`)**: The intermediate wrapper was
  folded directly into `bfs_complete_for_nontrivialPath` (OW2), which instantiates
  `go_complete` with the initial BFS state `frontier=[a], visited=[], fuel=serviceBfsFuel`.
  This is a clean simplification.

### 4.2 `serviceCountBounded` is stronger than the M2C spec

The M2C document specified:
```lean
∃ allSids, allSids.Nodup ∧ (∀ sid, lookupService st sid ≠ none → sid ∈ allSids)
  ∧ allSids.length ≤ serviceBfsFuel st
```

The PR implements:
```lean
∃ ns, bfsUniverse st ns ∧ ns.length ≤ serviceBfsFuel st
```

where `bfsUniverse` additionally requires **dependency closure**:
```
∀ sid ∈ ns, ∀ dep ∈ lookupDeps st sid, dep ∈ ns
```

This strengthening is **necessary and correct**. The original M2C spec was
insufficient: the BFS can reach nodes that are listed as dependencies but lack
their own service entries. Without dependency closure, `reach_in_universe` would
fail. The M2C spec was underspecified; the PR corrects it.

### 4.3 Additional helper artifacts (unplanned but needed)

The PR introduces 7 helper lemmas not in the original M2 plan:

| Name | Line | Purpose |
|------|------|---------|
| `bfsUniverse` | 589 | Bundles universe properties (Nodup + registration + dep closure) |
| `reach_in_universe` | 596 | Reachable nodes stay in universe (for fuel bound argument) |
| `filter_mono` | 604 | Monotone filter: stricter predicate → shorter list |
| `filter_strict` | 619 | Strict filter decrease under Nodup |
| `filter_vis_decrease` | 644 | Specializes `filter_strict` for visited set expansion |
| `step_of_reachable_ne` | 652 | If `a ≠ b` and `a` reaches `b`, an intermediate step exists |
| `registered_of_nontrivialPath_src` | 757 | Source of nontrivial path is a registered service |

All are well-motivated and necessary for the proof to go through.

### 4.4 Induction strategy

The M2D document specified `(fuel, frontier.length)` lexicographic induction.
The PR uses `Nat.strongRecOn` on `fuel` with inner structural induction on
`frontier`. These are equivalent: the skip case uses the inner frontier
induction (same fuel, shorter frontier), and the expand case uses strong fuel
induction (`fuel' < fuel' + 1`). The PR's approach is arguably simpler and
avoids the need for an explicit well-founded relation.

---

## 5. Technical concerns

### 5.1 RESOLVED — Breaking API change on preservation theorem

`serviceRegisterDependency_preserves_acyclicity` now requires
`hBound : serviceCountBounded st` as an additional parameter. This is the expected
Approach A trade-off from M2C.

**Resolution:** `serviceCountBounded_preserved_by_registerDependency` now proves
that the precondition is maintained across successful registrations, so callers
can chain multiple registrations without additional proof obligations.

### 5.2 RESOLVED — `serviceCountBounded` preservation proved

`serviceCountBounded_preserved_by_registerDependency` formally proves that
after a successful `serviceRegisterDependency`, the post-state satisfies
`serviceCountBounded`. The proof reuses the same BFS universe `ns` from the
pre-state, because:

- `storeServiceState` does not change `objectIndex`, so `serviceBfsFuel` is preserved
- The only dependency-list change is appending `depId` (which is registered) to `svcId`
- The `bfsUniverse` closure property is maintained since `depId ∈ ns`

### 5.3 RESOLVED — `hNe : a ≠ b` parameter removed

The vestigial `hNe` parameter has been removed from `bfs_complete_for_nontrivialPath`.
The theorem now has a cleaner signature:
```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hBound : serviceCountBounded st) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

### 5.4 MINOR — `maxHeartbeats 800000`

The `go_complete` theorem requires 4× the default heartbeat budget. The proof
compiles in ~2.6s, which is acceptable, but indicates room for optimization.
No correctness concern.

### 5.5 MINOR — `_hNV` unused in `bfsClosed_expand`

The `_hNV : nd ∉ vis` hypothesis in `bfsClosed_expand` (CB4) is declared but
unused. The closure property holds regardless of whether `nd` was already
visited. The parameter is over-specified but harmless — it matches the BFS
branch condition and aids readability.

### 5.6 MINOR — Unrelated `CLAUDE.md` changes

The PR includes modifications to `CLAUDE.md` (removing Write tool timeout
prevention rules) that are unrelated to the M2 BFS soundness bridge. This
is minor scope creep.

---

## 6. Proof correctness verification

### 6.1 `go_complete` (CP1) — case analysis

| Case | Condition | Proof strategy | Verified |
|------|-----------|---------------|----------|
| Base: `fr = []` | Contradiction with `∃ w ∈ [], ...` | `absurd hwM List.not_mem_nil` | ✓ |
| `nd = tgt` | Target found immediately | `go_tgt_eq` | ✓ |
| `nd ∈ vis` (skip) | Same fuel, shorter frontier | `ih_fr` + `bfsClosed_skip` + `bfs_boundary_lemma` | ✓ |
| `nd ∉ vis` (expand) | Strictly less fuel, new frontier | `ih_fuel` + `bfsClosed_expand` + `filter_vis_decrease` | ✓ |

### 6.2 Skip case — witness propagation

When the current frontier witness `w = nd` is the node being skipped (because
`nd ∈ vis`), the proof correctly invokes `bfs_boundary_lemma` with:
- `hwR : serviceReachable st nd tgt`
- `hVis : nd ∈ vis`
- `hTV : tgt ∉ vis`
- `hClR : bfsClosed st rest vis`

to produce `∃ f ∈ rest, serviceReachable st f tgt`. This is the crucial step
that transfers the reachability witness from the skipped node to a rest-frontier
element. **Correct.**

### 6.3 Expand case — fuel termination

When expanding `nd ∉ vis`:
1. `filter_vis_decrease` gives: `(ns.filter (· ∉ (nd :: vis))).length < (ns.filter (· ∉ vis)).length`
2. Combined with `hFuel`: `(ns.filter (· ∉ vis)).length ≤ fuel' + 1`
3. Therefore: `(ns.filter (· ∉ (nd :: vis))).length ≤ fuel'`
4. Strong induction: `fuel' < fuel' + 1 = fuel` triggers `ih_fuel`

**Correct.** The fuel decreasing argument is sound.

### 6.4 Expand case — reachability witness propagation

When the witness `w = nd` and `nd` is being expanded:
- `step_of_reachable_ne hwR hEq` produces `⟨mid, hedge, htail⟩`
- If `mid ∈ vis`: `bfs_boundary_lemma htail hMidNewVis hTgtNewVis hClE` finds a frontier witness
- If `mid ∉ vis`: `mid` is in `(lookupDeps st nd).filter (· ∉ vis)`, hence in the new frontier

Both sub-cases correctly establish `∃ w' ∈ newFrontier, serviceReachable st w' tgt`. **Correct.**

### 6.5 Equational lemmas

- `go_tgt_eq`: `simp [serviceHasPathTo.go]` on `tgt :: rest` with `fuel + 1` yields `true`. **Correct.**
- `go_skip_eq`: `simp [serviceHasPathTo.go, hNeq, hVis]` reduces skip. **Correct.**
- `go_expand_eq`: `simp + unfold lookupDeps; rfl` — the `let deps := match lookupService ...`
  in `go` is definitionally equal to `lookupDeps`. **Correct.**

### 6.6 `bfs_complete_for_nontrivialPath` assembly

The outer theorem correctly instantiates `go_complete` with initial state:
- `frontier = [a]`, `visited = []`, `fuel = serviceBfsFuel st`, universe `ns` from `serviceCountBounded`
- `tgt ∉ [] = true` (via `simp`)
- `bfsClosed st [a] [] = true` (via `bfsClosed_init`)
- Witness: `⟨a, List.mem_cons_self, serviceReachable_of_nontrivialPath hPath⟩`
- Universe membership: `a ∈ ns` via `registered_of_nontrivialPath_src` + universe registration
- Fuel bound: `ns.filter (· ∉ []) = ns` → `ns.length ≤ serviceBfsFuel st`

**Correct.**

---

## 7. Stretch goals status

| Goal | Status |
|------|--------|
| Fuel monotonicity (`go_fuel_mono`) | Not implemented |
| `serviceCountBounded` preservation across mutations | **Implemented** (`serviceCountBounded_preserved_by_registerDependency`) |
| Unconditional fuel adequacy (Approach B) | Not implemented |
| B1–B3 extraction direction (BFS `true` → declarative path) | Not implemented |
| Full bidirectional equivalence | Not implemented |

Most stretch goals remain deferred, as expected by the M2 plan. The preservation
theorem was implemented as part of audit remediation (§5.2).

---

## 8. Verdict

**PASS.** PR #179 achieves the core M2 objective: eliminating the `sorry` on
`bfs_complete_for_nontrivialPath` with a formally verified BFS completeness proof.
The proof is mathematically correct, builds cleanly, and passes all smoke tests.

The `serviceCountBounded` precondition (Approach A) is a legitimate trade-off
documented in the M2 spec. The API surface change to `serviceRegisterDependency_preserves_acyclicity`
is the expected consequence.

**Recommended follow-ups (all resolved):**
1. ~~Prove `serviceCountBounded` preservation across `serviceRegisterDependency`~~ — **DONE** (§5.2)
2. ~~Drop the vestigial `hNe` parameter~~ — **DONE** (§5.3)
3. ~~Extract `CLAUDE.md` changes into a separate PR~~ — **DONE** (excluded from audit branch)
