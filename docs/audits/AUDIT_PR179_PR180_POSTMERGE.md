# Post-Merge Audit: PR #179 and PR #180

**Auditor:** Claude (Opus 4.6)
**Date:** 2026-02-23
**Scope:** End-to-end audit of changes introduced by PR #179 (M2 BFS Soundness Bridge) and PR #180 (Audit of PR #179)
**Verdict:** CONDITIONAL PASS — genuine proof progress with critical documentation defects and an unresolved precondition gap

---

## 1. Executive summary

PR #179 added ~265 lines of formal BFS completeness proof infrastructure to
`SeLe4n/Kernel/Service/Invariant.lean`, replacing a `sorry` on
`bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE). PR #180 added an audit
report (`AUDIT_PR179_M2_BFS_SOUNDNESS.md`) and updated milestone documentation.

**The BFS loop-invariant proof is mathematically correct and represents genuine
progress.** However, this audit identifies three categories of defects:

| # | Category | Severity |
|---|----------|----------|
| D1 | `serviceCountBounded` is an unproved precondition — never established, never preserved | HIGH |
| D2 | Documentation claims a theorem exists (`serviceCountBounded_preserved_by_registerDependency`) that does not exist in any `.lean` file | CRITICAL |
| D3 | Documentation claims `hNe` parameter was removed (§5.3); it is still present at `Invariant.lean:777` | MEDIUM |

**Recommendation:** Do NOT revert. Continue from the current state, but correct
the documentation and track `serviceCountBounded` as an explicit proof obligation.

---

## 2. What PR #179 changed (code)

### 2.1 New proof infrastructure in `Service/Invariant.lean`

| Artifact | Line | Purpose | Correct? |
|----------|------|---------|----------|
| `lookupDeps` | 517 | Helper: dependency list with `[]` default | Yes |
| `serviceEdge_iff_lookupDeps` | 521 | Iff bridge between declarative edge and list membership | Yes |
| `bfsClosed` | 533 | BFS closure invariant definition | Yes |
| `bfsClosed_init` (CB2) | 537 | Empty visited set is trivially closed | Yes |
| `bfsClosed_skip` (CB3) | 542 | Skip preserves closure | Yes |
| `bfsClosed_expand` (CB4) | 554 | Expansion preserves closure | Yes (`_hNV` unused but harmless) |
| `bfs_boundary_lemma` (CB1) | 573 | Visited reachable node implies frontier reachable node | Yes |
| `bfsUniverse` | 590 | Nodup + registration + dependency-closure bundle | Yes |
| `reach_in_universe` | 596 | Reachable nodes stay in universe | Yes |
| `filter_mono` | 604 | Monotone filter length | Yes |
| `filter_strict` | 619 | Strict filter decrease under Nodup | Yes |
| `filter_vis_decrease` | 644 | Specialization for visited-set expansion | Yes |
| `step_of_reachable_ne` | 652 | Intermediate step from nontrivial reachability | Yes |
| `go_tgt_eq` (EQ3) | 661 | Target at head returns true | Yes |
| `go_skip_eq` (EQ4) | 666 | Skip equational unfolding | Yes |
| `go_expand_eq` (EQ5) | 672 | Expand equational unfolding | Yes |
| `go_complete` (CP1) | 684 | Core BFS completeness by strong fuel induction | Yes |
| `serviceCountBounded` | 752 | Fuel adequacy precondition | See §3 |
| `registered_of_nontrivialPath_src` | 757 | Source of nontrivial path is registered | Yes |

### 2.2 Modified theorem signatures

**`bfs_complete_for_nontrivialPath`** (line 774):
```lean
-- BEFORE (sorry):
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (_hPath : serviceNontrivialPath st a b)
    (_hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  sorry

-- AFTER (proved, with new precondition):
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b)
    (hBound : serviceCountBounded st) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  -- ~20 lines of genuine proof
```

**`serviceRegisterDependency_preserves_acyclicity`** (line 855):
```lean
-- BEFORE: (hAcyc : serviceDependencyAcyclic st) only
-- AFTER:  (hAcyc : ...) (hBound : serviceCountBounded st)
```

### 2.3 What PR #180 changed (documentation only)

PR #180 added `docs/audits/AUDIT_PR179_M2_BFS_SOUNDNESS.md` (283 lines) and
updated `M2_BFS_SOUNDNESS.md` and `12-proof-and-invariant-map.md`. No `.lean`
files were modified.

---

## 3. Critical finding: `serviceCountBounded` gap

### 3.1 The precondition

```lean
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ ns : List ServiceId,
    bfsUniverse st ns ∧ ns.length ≤ serviceBfsFuel st
```

This requires the existence of a finite list of ServiceIds that:
- Has no duplicates (`Nodup`)
- Contains every registered service (`lookupService st sid ≠ none → sid ∈ ns`)
- Is closed under dependencies (`∀ sid ∈ ns, ∀ dep ∈ lookupDeps st sid, dep ∈ ns`)
- Fits within the fuel budget (`ns.length ≤ serviceBfsFuel st`)

### 3.2 The gap: consumed but never produced

`serviceCountBounded` appears in exactly 5 lines of `.lean` code:

| Line | Role |
|------|------|
| 752 | Definition |
| 772 | Comment |
| 778 | **Consumed** as hypothesis of `bfs_complete_for_nontrivialPath` |
| 853 | Comment |
| 859 | **Consumed** as hypothesis of `serviceRegisterDependency_preserves_acyclicity` |

**Zero theorems produce `serviceCountBounded` as a conclusion.** It is never:
- Proved for any initial or constructed state
- Proved to be preserved by `serviceRegisterDependency` (or any other operation)
- Proved to be preserved by `serviceStart`, `serviceStop`, `serviceRestart`
- Included in any invariant bundle

### 3.3 Why this matters

Before PR #179, the preservation theorem had the natural specification:

```
successful_registration + pre_acyclicity  ⟹  post_acyclicity
```

After PR #179, it has a weaker specification:

```
successful_registration + pre_acyclicity + serviceCountBounded  ⟹  post_acyclicity
```

A caller who chains multiple `serviceRegisterDependency` calls must prove
`serviceCountBounded st` for every intermediate state — but no preservation
theorem exists, so this is impossible within the formalization.

### 3.4 Is `serviceCountBounded` plausible?

Yes. The property is plausible for states constructed through normal kernel
operations, because:

- `serviceRegisterDependency` checks `lookupService st depId ≠ none` before
  adding a dependency, so all edges point to registered services
- `storeServiceState` does not modify `objectIndex`, so `serviceBfsFuel` is
  stable across service mutations
- The `+256` headroom in `serviceBfsFuel` provides margin

But plausibility is not proof. In formal verification, unproved hypotheses must
be tracked with the same rigor as `sorry`.

### 3.5 Comparison: old sorry vs. new gap

| Dimension | Before (sorry) | After (serviceCountBounded) |
|-----------|---------------|---------------------------|
| Proof gap size | Entire BFS completeness argument | Fuel adequacy only (~20% of original) |
| Gap visibility | `sorry` keyword — caught by grep, CI, Lean warnings | Invisible — no compiler warning, no CI gate |
| Theorem strength | Unconditional (2 hypotheses) | Conditional (3 hypotheses) |
| Downstream usability | Callable (accepting sorry debt) | **Not callable** without proving precondition |
| Intellectual honesty | Explicit: "we haven't proved this" | Implicit: hypothesis that no one discharges |

**The proof gap was narrowed by ~80% but its visibility was reduced to zero.**

---

## 4. Documentation integrity defects

### 4.1 CRITICAL — Phantom theorem claim

`docs/audits/AUDIT_PR179_M2_BFS_SOUNDNESS.md` (PR #180) makes three false
claims about `serviceCountBounded_preserved_by_registerDependency`:

| Location | Claim | Reality |
|----------|-------|---------|
| Line 143 | "now proves that the precondition is maintained" | Theorem does not exist in any `.lean` file |
| Line 260 | Status: "**Implemented**" | Not implemented |
| Line 287 | "DONE (§5.2)" | Not done |

`docs/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md` line 441 marks
`[x]` (completed) for this theorem. It is not completed.

`docs/gitbook/12-proof-and-invariant-map.md` line 294 claims it "proves the
precondition is maintained." It does not.

### 4.2 MEDIUM — False `hNe` removal claim

`AUDIT_PR179_M2_BFS_SOUNDNESS.md` §5.3 states:
> **RESOLVED — `hNe : a ≠ b` parameter removed**

The actual code at `Invariant.lean:777` contains:
```lean
    (hNe : a ≠ b)
```

The parameter was NOT removed.

### 4.3 LOW — Overstated closure language

Multiple documents use language like "No `sorry` debt remains," "all sorry
obligations eliminated," and "fully closed." While technically true (there is
no literal `sorry` keyword), this language obscures the fact that a new
untracked proof obligation was introduced.

---

## 5. Proof correctness verification

### 5.1 `go_complete` (CP1) — verified correct

The core theorem uses `Nat.strongRecOn` on fuel with structural induction on
the frontier list. I verified all four cases:

| Case | Strategy | Verified |
|------|----------|----------|
| `fr = []` | Contradiction with `∃ w ∈ []` | Correct |
| `nd = tgt` | `go_tgt_eq` | Correct |
| `nd ∈ vis` (skip) | `ih_fr` + `bfsClosed_skip` + `bfs_boundary_lemma` | Correct |
| `nd ∉ vis` (expand) | `ih_fuel` + `bfsClosed_expand` + `filter_vis_decrease` | Correct |

The skip case correctly identifies that fuel is NOT consumed (the BFS
implementation passes `fuel + 1` through in the skip branch), so the structural
frontier IH applies. The expand case correctly shows strict fuel decrease via
`filter_vis_decrease`, enabling strong induction.

### 5.2 Equational bridge — verified correct

- `go_tgt_eq`: Target at head with `fuel + 1` returns `true`. Matches BFS line 120.
- `go_skip_eq`: Visited node skipped, same fuel. Matches BFS line 121.
- `go_expand_eq`: Unvisited node expanded, fuel decremented. Matches BFS line 123-127.
  The `lookupDeps` bridge to the BFS `let deps := match lookupService ...` is
  definitionally equal, confirmed by `rfl`.

### 5.3 Closure lemmas — verified correct

- `bfsClosed_init`: Empty visited set trivially closed.
- `bfsClosed_skip`: When `nd ∈ vis`, removing `nd` from frontier preserves closure
  because `nd` references are absorbed into `vis`.
- `bfsClosed_expand`: When `nd ∉ vis`, adding `nd` to visited and its deps to
  frontier preserves closure. `_hNV` is unused but matches the BFS branch condition.
- `bfs_boundary_lemma`: Key correctness argument. Proved by induction on
  `serviceReachable`. If `v ∈ vis` reaches `tgt ∉ vis`, the path must cross the
  vis/frontier boundary, producing a frontier witness.

### 5.4 `maxHeartbeats 800000`

`go_complete` requires 4x default heartbeat budget. This is a performance
concern, not a correctness concern. The proof compiles in ~2.6s.

### 5.5 No sorry/axiom in production surface

Confirmed: `grep -r 'sorry\|axiom' SeLe4n/ --include='*.lean'` returns zero
matches across all 28 `.lean` files and 271 theorems.

---

## 6. Test infrastructure assessment

### 6.1 What tests cover

| Tier | What it checks | Catches regression? |
|------|---------------|-------------------|
| T0 | No `sorry`/`axiom` keywords, TPI annotations | Yes for sorry reintroduction |
| T1 | `lake build` succeeds | Yes for type errors |
| T2 | Main trace output matches fixture (50 lines) | Yes for operation behavior changes |
| T2 | NegativeStateSuite (372 lines) — error paths | Partially — checks outputs, not invariants |
| T3 | Regex anchors for theorem/definition names | Yes for renamed/removed theorems |

### 6.2 What tests do NOT cover

- No test validates `serviceCountBounded` on any concrete state
- No test empirically validates BFS completeness on worst-case graphs
- No test runs invariant preservation checks on post-mutation states
- No test catches the addition of unproved hypotheses to existing theorems

---

## 7. Verdict and recommendation

### 7.1 Should the project revert?

**No.** The BFS loop-invariant proof infrastructure (~250 lines) is genuine,
correct, and valuable. It solves the hard algorithmic part of the problem.
Reverting would discard real work.

### 7.2 Should the project continue from the current state?

**Yes, with corrections.** The current state is strictly better than the pre-PR
state in proof content, but worse in documentation integrity. The following
corrections are needed:

### 7.3 Required corrections (immediate)

**C1. Track `serviceCountBounded` as an explicit proof obligation.**

Add a TPI annotation (e.g., `TPI-D07-FUEL`) to `serviceCountBounded` in
`Invariant.lean` and register it in the tracked proof issues document. This
restores the visibility that was lost when the `sorry` was removed.

**C2. Correct false documentation claims.**

In `AUDIT_PR179_M2_BFS_SOUNDNESS.md`:
- §5.1: Change "RESOLVED" to "OPEN — serviceCountBounded not preserved"
- §5.2: Change to "NOT IMPLEMENTED — theorem does not exist"
- §5.3: Change to "NOT RESOLVED — hNe still present at line 777"
- Table line 260: Change "Implemented" to "Not implemented"
- Line 287: Change "DONE" to "TODO"

In `M2_BFS_SOUNDNESS.md` line 441: Uncheck the `[x]` box.

In `12-proof-and-invariant-map.md` line 294: Remove the false claim.

**C3. Update closure language across all docs.**

Replace "no sorry debt remains" with "no sorry keyword remains; the
`serviceCountBounded` precondition is tracked as TPI-D07-FUEL."

### 7.4 Recommended follow-up work (next workstream)

**F1. Prove `serviceCountBounded` for initial states.**

```lean
theorem serviceCountBounded_initial :
    serviceCountBounded defaultSystemState
```

**F2. Prove `serviceCountBounded` preservation across all service mutations.**

```lean
theorem serviceCountBounded_preserved_storeServiceState
    (sid : ServiceId) (entry : ServiceGraphEntry) (st : SystemState)
    (hBound : serviceCountBounded st)
    (hDeps : ∀ dep ∈ entry.dependencies, dep ∈ ns)  -- or similar
    : serviceCountBounded (storeServiceState sid entry st)
```

This is the theorem that PR #180 claims exists but does not.

**F3. Consider Approach B (eliminate precondition entirely).**

Add a `serviceIndex : List ServiceId` field to `SystemState` that tracks all
registered ServiceIds, maintained by `storeServiceState`. Then
`serviceCountBounded` becomes provable from the model structure alone, and the
precondition can be removed from the theorem signatures. This restores the
unconditional theorem strength of the pre-PR state while keeping the proof.

**F4. Add CI gate for hypothesis tracking.**

Add a Tier 0 check that greps for `serviceCountBounded` usage and verifies
both consumption and production sites exist, similar to the existing
sorry/axiom scan.

---

## 8. Accounting summary

| Metric | Before PRs | After PRs | Assessment |
|--------|-----------|-----------|------------|
| Lines in Service/Invariant.lean | 675 | 940 | +265 lines of proof |
| `sorry` count | 1 | 0 | Improved (but see §3) |
| `axiom` count | 0 | 0 | Clean |
| Unproved hypotheses | 0 | 1 (`serviceCountBounded`) | New gap |
| Phantom theorem claims in docs | 0 | 1 | Defect |
| False factual claims in docs | 0 | 2 | Defect |
| BFS algorithmic proof | Absent | Complete | Genuine progress |
| Fuel adequacy proof | Absent | Absent | No change |
| Top-level theorem strength | 2 hypotheses | 3 hypotheses | Weaker |
| Proof gap visibility | Compiler-flagged | Invisible | Worse |

---

## 9. Conclusion

PR #179 completed approximately 80% of the work needed to close TPI-D07-BRIDGE.
The BFS closure invariant, termination argument, equational bridge, and core
completeness theorem are all correct and machine-checked. This is real,
valuable formal verification work.

The remaining 20% — fuel adequacy — was externalized as `serviceCountBounded`
rather than proved. This is a legitimate engineering choice (Approach A from
the M2C spec), but the documentation overstates the closure, and PR #180's
audit report contains multiple false claims about theorems and parameter
changes that do not match the actual code.

The project should continue from the current state with documentation
corrections and a tracked proof obligation for `serviceCountBounded`.
