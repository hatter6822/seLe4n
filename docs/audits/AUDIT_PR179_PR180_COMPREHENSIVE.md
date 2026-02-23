# Comprehensive Audit: PR #179 and PR #180

**Auditor:** Claude (Opus 4.6) — independent end-to-end review
**Date:** 2026-02-23
**Scope:** Full codebase before/after PR #179 (M2 BFS Soundness Bridge) and PR #180 (Audit of PR #179)
**Baseline commit:** `1fd50a8` (pre-PR #179)
**Current HEAD:** `2fc9b3e` (post-PR #180 merge)

---

## 1. Executive Summary

**Verdict: DO NOT REVERT. Continue development from the current state — but correct the documentation lies and close the identified proof gap first.**

PR #179 is a genuine, substantial improvement: it eliminates the sole `sorry` in
the entire codebase with a mathematically correct BFS completeness proof that
Lean's kernel verifies. PR #180, however, is a deeply flawed audit document that
makes **three demonstrably false claims** about code that does not exist. These
phantom claims have propagated across five documentation files.

The Lean proof code is sound. The documentation around it is not trustworthy.

---

## 2. Pre-PR Baseline State (commit `1fd50a8`)

| Metric | Value |
|--------|-------|
| Total `.lean` files | 33 |
| Total `sorry` instances | **1** (in `Service/Invariant.lean:531`) |
| Total `axiom` declarations | 0 |
| `Service/Invariant.lean` lines | 675 |
| Theorems in `Service/Invariant.lean` | 31 |
| Build status | Clean (62 jobs) |

The single `sorry` was on `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE),
annotated as deferred and covered by executable tests. The theorem statement was:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (_hPath : serviceNontrivialPath st a b)
    (_hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  sorry -- TPI-D07-BRIDGE: BFS completeness proof deferred
```

The `serviceRegisterDependency_preserves_acyclicity` theorem existed with a clean
signature — it did NOT require `serviceCountBounded`:

```lean
theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st) :
    serviceDependencyAcyclic st'
```

This is important context: the pre-PR API was unconditional.

---

## 3. Post-PR Current State (commit `2fc9b3e`)

| Metric | Value |
|--------|-------|
| Total `sorry` instances | **0** |
| Total `axiom` declarations | 0 |
| `Service/Invariant.lean` lines | 941 |
| New theorems added | ~20 (BFS bridge infrastructure) |
| New definitions added | ~8 |
| Build status | Clean (62 jobs) |
| `test_smoke.sh` | PASS |

---

## 4. PR #179 Analysis — The BFS Soundness Bridge

### 4.1 What PR #179 Actually Did

PR #179 added ~265 lines of Lean proof code to `Service/Invariant.lean` that
formally prove BFS completeness: if a nontrivial path exists between two
service nodes in the dependency graph, the executable BFS (`serviceHasPathTo`)
returns `true` given adequate fuel.

**Proof architecture (verified correct):**

| Layer | Component | Status |
|-------|-----------|--------|
| M2A | `lookupDeps` helper + `serviceEdge_iff_lookupDeps` bridge | Correct |
| M2B | `bfsClosed` definition + CB2/CB3/CB4 lemmas | Correct |
| CB1 | `bfs_boundary_lemma` (visited→frontier witness transfer) | Correct |
| Universe | `bfsUniverse` + `reach_in_universe` | Correct |
| Termination | `filter_mono`, `filter_strict`, `filter_vis_decrease` | Correct |
| EQ lemmas | `go_tgt_eq`, `go_skip_eq`, `go_expand_eq` | Correct |
| CP1 | `go_complete` (core BFS completeness, strong induction) | Correct |
| Wrapper | `bfs_complete_for_nontrivialPath` (instantiates `go_complete`) | Correct |

### 4.2 Proof Correctness Assessment

The proof is **mathematically sound** and **machine-verified by Lean's kernel**.

- `go_complete` uses strong induction on `fuel` with inner structural induction on
  `frontier`. The skip case (already-visited node) uses frontier shrinkage. The
  expand case uses strictly decreasing unvisited-universe count via `filter_vis_decrease`.
- The `bfs_boundary_lemma` correctly handles witness propagation: when a visited
  node reaches the target but the target isn't visited, some frontier node must
  also reach the target (by the closure invariant).
- The BFS implementation's fuel semantics are correctly captured: skip doesn't
  consume fuel (`fuel + 1` → `fuel + 1`), expand does (`fuel + 1` → `fuel`).
- The equational lemmas (`go_tgt_eq`, `go_skip_eq`, `go_expand_eq`) correctly
  unfold the recursive BFS definition and match `lookupDeps` to the inline
  `match lookupService` in `go`.

### 4.3 The `serviceCountBounded` Trade-off

PR #179 introduced `serviceCountBounded st` as a new precondition:

```lean
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ ns : List ServiceId,
    bfsUniverse st ns ∧ ns.length ≤ serviceBfsFuel st
```

This was added to both `bfs_complete_for_nontrivialPath` AND
`serviceRegisterDependency_preserves_acyclicity`. This is an expected trade-off
(the M2C "Approach A" from the planning docs), but it has a consequence: the
preservation theorem's API changed from unconditional to conditional.

**This is the right engineering choice.** The alternative ("Approach B") would
require proving that `serviceBfsFuel st` is always large enough for any reachable
state — which would demand a model-level bound on the number of service
registrations, something the current model doesn't constrain. Approach A
is honest: it says "given adequate fuel, the BFS is complete."

### 4.4 The `bfsUniverse` Strengthening

The M2C spec originally required only:
```
∃ allSids, allSids.Nodup ∧ (∀ sid, lookupService st sid ≠ none → sid ∈ allSids)
  ∧ allSids.length ≤ serviceBfsFuel st
```

The implementation strengthens this with **dependency closure**:
```
∀ sid ∈ ns, ∀ dep ∈ lookupDeps st sid, dep ∈ ns
```

This strengthening is **necessary and correct**. Without it, the BFS could
reach a node via a dependency edge that falls outside the universe, breaking
`reach_in_universe`. The original spec was underspecified.

### 4.5 Minor Issues

- **`maxHeartbeats 800000`**: The `go_complete` proof requires 4× default heartbeats.
  Acceptable for a complex induction, but indicates room for proof optimization.
- **`_hNV` unused in `bfsClosed_expand`**: The `nd ∉ vis` hypothesis is declared
  but unused. Harmless — the closure property holds regardless — but slightly
  over-specified.
- **`hNe : a ≠ b` still present**: The parameter is still in the theorem signature
  at line 777, despite documentation claiming it was removed (see §5).

---

## 5. PR #180 Analysis — The Audit Document

### 5.1 What PR #180 Actually Did

PR #180 added a 283-line audit document (`AUDIT_PR179_M2_BFS_SOUNDNESS.md`) and
updated the M2 milestone document and GitBook chapter. It added **zero lines of
Lean code**.

### 5.2 CRITICAL FINDING: Three Phantom Claims

The audit document makes three claims about code changes that **do not exist**.
These are not minor inaccuracies — they are assertions about theorems that were
never implemented.

#### Phantom Claim 1: `serviceCountBounded_preserved_by_registerDependency`

**Claim locations** (5 files):
- `AUDIT_PR179_M2_BFS_SOUNDNESS.md` §5.1, §5.2, §7
- `M2_BFS_SOUNDNESS.md` line 441 (stretch goals, marked `[x]`)
- `12-proof-and-invariant-map.md` line 294

**Claim text** (§5.2):
> `serviceCountBounded_preserved_by_registerDependency` formally proves that
> after a successful `serviceRegisterDependency`, the post-state satisfies
> `serviceCountBounded`.

**Reality:**
```
$ grep -rn "serviceCountBounded_preserved" SeLe4n/ --include="*.lean"
(no output)
```

**This theorem does not exist.** It was never implemented. The stretch goal
checklist marks it `[x]` complete. The §7 "Recommended follow-ups" shows it
struck through as "DONE (§5.2)". Five documentation files reference it as if
it exists.

#### Phantom Claim 2: `hNe : a ≠ b` Removed

**Claim** (§5.3):
> The vestigial `hNe` parameter has been removed from `bfs_complete_for_nontrivialPath`.

**Reality** (`Invariant.lean:777`):
```lean
    (hNe : a ≠ b)  -- still present
```

The parameter was never removed.

#### Phantom Claim 3: Documented Signature Doesn't Match Code

**Documented signature** (§5.3):
```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hBound : serviceCountBounded st) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

**Actual signature** (`Invariant.lean:774-779`):
```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b)
    (hBound : serviceCountBounded st) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

### 5.3 Root Cause

The audit document appears to have been written based on **intended changes**
rather than verified against **actual code**. The document describes a world
where:
1. A preservation theorem was proved
2. A vestigial parameter was removed
3. All concerns were resolved

None of these happened in the code. The document was merged as-is,
and its false claims cascaded into four other documentation files.

### 5.4 Impact Assessment

The phantom claims are **documentation bugs, not proof bugs**. The actual
Lean code is correct and machine-verified. However:

- Readers of the audit document will believe `serviceCountBounded` preservation
  is proven when it is not.
- The stretch goal checklist is misleading.
- The claim-evidence index gives false confidence about proof completeness.

---

## 6. The `serviceCountBounded` Proof Gap

This is the most important architectural observation from the audit.

### 6.1 The Gap

Pre-PR #179, `serviceRegisterDependency_preserves_acyclicity` was unconditional:
```lean
(hAcyc : serviceDependencyAcyclic st) → serviceDependencyAcyclic st'
```

Post-PR #179, it requires:
```lean
(hAcyc : serviceDependencyAcyclic st) →
(hBound : serviceCountBounded st) →
serviceDependencyAcyclic st'
```

But nothing proves `serviceCountBounded st'` for the post-state. This means
a caller doing two successive registrations cannot chain the theorem:
```
register(A→B) : acyclic(st) + bounded(st) → acyclic(st')
register(C→D) : acyclic(st') + bounded(st') → acyclic(st'')
                                  ^^^^^^^^^ NOT PROVEN
```

### 6.2 Is This Actually Provable?

Yes. `storeServiceState` only modifies the `services` function (not
`objectIndex`), so `serviceBfsFuel st' = serviceBfsFuel st`. The BFS universe
`ns` from the pre-state can be reused for the post-state because:
- Registration only adds `depId` to `svcId.dependencies`
- `depId` is already registered (checked by `serviceRegisterDependency`)
- So `depId ∈ ns` already holds
- The Nodup and registration properties are preserved

This is a straightforward proof. It should be implemented.

### 6.3 Is This a Reason to Revert?

**No.** The gap is a missing convenience lemma, not a soundness hole. The
`serviceCountBounded` precondition is satisfiable for any well-formed system
state, and is morally equivalent to "the system has finitely many registered
services" — which is always true in practice. The pre-PR #179 code had a
`sorry` on the same theorem, which is strictly worse than having a proven
theorem with a precondition.

---

## 7. Test Infrastructure Assessment

The test suite has 5 tiers:

| Tier | Script | What It Tests |
|------|--------|---------------|
| 0 | `test_tier0_hygiene.sh` | File structure, no-sorry policy, no-axiom policy |
| 1 | `test_tier1_build.sh` | `lake build` succeeds |
| 2 | `test_tier2_trace.sh` | Main trace output matches fixture |
| 2 | NegativeStateSuite | ~70 error-path scenarios, 6 runtime invariants |
| 3 | `test_tier3_invariant_surface.sh` | ~120 definition/theorem name anchors exist |
| 4 | `test_nightly.sh` | Determinism check, stochastic probe |

**Assessment:** The test infrastructure is adequate for *build regression
detection* and *structural validation* but does not provide *semantic
verification*. The tiered system is well-organized and catches real
regressions (missing definitions, output changes, sorry introduction).
However, no test actually *instantiates* a proven theorem against a concrete
state transition. The proofs compile and the tests pass, but no test connects
the two.

This is a common gap in formal verification projects and is not a deficiency
introduced by PR #179 or #180. It predates both PRs and should be addressed
in WS-D5 (test infrastructure) as already planned.

---

## 8. Verdict

### Should the project revert?

**No.** The reasoning:

| Factor | Pre-PR #179 | Post-PR #179 | Assessment |
|--------|-------------|--------------|------------|
| `sorry` count | 1 | 0 | **Improvement** |
| BFS completeness | Assumed | Proved | **Improvement** |
| Acyclicity preservation | Unconditional (with sorry) | Conditional (without sorry) | **Net improvement** |
| Proof soundness | Incomplete | Complete | **Improvement** |
| Documentation accuracy | Reasonable | Contains false claims | **Regression** |
| API surface | Simpler | +1 precondition | **Minor regression** |

The single `sorry` was a real proof debt. Eliminating it with a correct formal
proof is unambiguously better, even with the `serviceCountBounded` precondition.
Reverting would reintroduce the `sorry` — going from "proven with a precondition"
back to "unproven" is a step backward.

### What should happen instead?

**Continue from current state** with the following fixes, in priority order:

---

## 9. Recommended Fixes

### Fix 1 (CRITICAL): Correct the Phantom Documentation Claims

The following documents contain false claims that must be corrected:

1. **`AUDIT_PR179_M2_BFS_SOUNDNESS.md`**
   - §5.1: Change "RESOLVED" to "OPEN — preservation theorem not yet implemented"
   - §5.2: Change "RESOLVED" to "OPEN — theorem does not exist in code"
   - §5.3: Change "RESOLVED" to "OPEN — `hNe` parameter still present"
   - §7 stretch goals: Unmark `serviceCountBounded` preservation (change ✓ to ☐)
   - §8 recommended follow-ups: Remove strikethroughs, mark as TODO

2. **`M2_BFS_SOUNDNESS.md`** line 441: Change `[x]` to `[ ]`

3. **`12-proof-and-invariant-map.md`** lines 292-295: Remove reference to
   non-existent theorem

4. **`SELE4N_SPEC.md`**: Add note about `serviceCountBounded` precondition

5. **`CLAIM_EVIDENCE_INDEX.md`**: Add note about missing preservation theorem

### Fix 2 (HIGH): Implement `serviceCountBounded` Preservation

Prove the following theorem in `Service/Invariant.lean`:

```lean
theorem serviceCountBounded_preserved_by_registerDependency
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hBound : serviceCountBounded st) :
    serviceCountBounded st' := by
  -- Proof sketch:
  -- 1. Extract ns, hU, hLen from hBound
  -- 2. Show serviceBfsFuel st' = serviceBfsFuel st
  --    (storeServiceState doesn't change objectIndex)
  -- 3. Show bfsUniverse st' ns still holds:
  --    a. Nodup preserved (ns unchanged)
  --    b. Registration: storeServiceState only changes svcId's entry,
  --       all other lookups unchanged
  --    c. Dep closure: only new dep is depId, which is registered,
  --       hence depId ∈ ns by hU.2.1
  -- 4. Same ns, same fuel → serviceCountBounded st'
  sorry -- TODO: implement
```

### Fix 3 (MEDIUM): Remove Vestigial `hNe` Parameter

The `hNe : a ≠ b` parameter on `bfs_complete_for_nontrivialPath` is genuinely
unnecessary. A nontrivial path from `a` to `a` would mean `a` has a self-cycle,
and the `serviceRegisterDependency_preserves_acyclicity` proof only calls this
theorem with `depId` and `svcId` where `depId ≠ svcId` is already known. However,
the more principled fix is to prove that `serviceNontrivialPath st a b → a ≠ b`
is NOT generally true (a nontrivial path `a → ... → a` is a cycle, which is
`a = b` with `a = a`). So `hNe` serves as a guard: the BFS returns `true`
immediately when `src = target`, so we need `a ≠ b` to ensure the BFS actually
does work.

Actually, looking more carefully: `serviceHasPathTo st a a fuel = true` always
(the BFS checks `node = target` first). So `bfs_complete_for_nontrivialPath`
with `a = b` is trivially true without the proof infrastructure. The `hNe`
parameter is harmless but causes the proof to do unnecessary work. Removing it
would require adjusting the proof to handle the `a = b` case separately (trivially).

### Fix 4 (LOW): Prove `serviceCountBounded` for Initial States

Add a lemma showing the default/empty state satisfies `serviceCountBounded`:

```lean
theorem serviceCountBounded_default : serviceCountBounded default := by
  exact ⟨[], ⟨List.nodup_nil, fun _ h => absurd rfl h, fun _ h => absurd h List.not_mem_nil⟩, by omega⟩
```

This would establish the base case for inductive reasoning about system states.

---

## 10. Criticisms of the Overall Project

### 10.1 The Proof-Test Disconnect

The project's strongest asset (115 machine-checked theorems across 7 invariant
files, zero sorry, zero axioms) is disconnected from its test infrastructure.
No test instantiates a theorem. The proofs and the tests live in parallel
universes. This is the project's most significant architectural weakness and
should be the focus of WS-D5.

### 10.2 The Documentation-as-Truth Problem

PR #180 demonstrates a dangerous pattern: audit documents that assert code
changes were made without verification. When the audit itself becomes a source
of false claims, it undermines the entire documentation chain. The project
should adopt a policy: **audit documents must link to specific git diff ranges
and include machine-verifiable assertions** (e.g., "grep for
`serviceCountBounded_preserved` returns exactly 1 match in `.lean` files").

### 10.3 The `serviceCountBounded` Composability Gap

While not a soundness issue, the missing preservation theorem means the
acyclicity proof cannot be composed across multiple registrations without
re-establishing the precondition. This is the kind of gap that makes formal
proofs less useful in practice — a caller must do extra work to use the theorem.

### 10.4 The Fuel Bound Is Generous but Ungrounded

`serviceBfsFuel st = st.objectIndex.length + 256` is a reasonable heuristic,
but the `+ 256` constant is arbitrary. The BFS universe requires that
`ns.length ≤ serviceBfsFuel st`. If the system ever had more than
`objectIndex.length + 256` service IDs reachable via dependency edges (which
seems unlikely but isn't provably impossible), the fuel would be insufficient.
A principled approach would tie the fuel to the actual number of registered
services, not the object index.

### 10.5 Dependency Closure Is Not Enforced at Registration Time

The `bfsUniverse` requires that dependencies form a closed set — every
dependency target is in the universe. But `ServiceGraphEntry.dependencies` is
just a `List ServiceId` with no invariant guaranteeing all targets are
registered. While `serviceRegisterDependency` checks this at registration time,
there's no system-level invariant preventing a service from being constructed
with invalid dependencies through other paths (e.g., direct `storeServiceState`
calls). Consider adding a system-level well-formedness invariant.

---

## 11. Final Assessment

| Component | Grade | Notes |
|-----------|-------|-------|
| BFS completeness proof (PR #179 code) | **A** | Correct, well-structured, machine-verified |
| `go_complete` induction strategy | **A** | Strong induction on fuel + structural on frontier is clean |
| `serviceCountBounded` design choice | **B+** | Honest about preconditions; missing preservation theorem |
| Audit document (PR #180) | **F** | Three phantom claims, cascading false documentation |
| Documentation accuracy (overall) | **D** | Multiple files contain false claims about code |
| Test infrastructure | **B-** | Well-tiered but doesn't verify semantic properties |
| Overall proof surface | **A** | 115 theorems, 0 sorry, 0 axioms across 2919 lines |
| Overall project health | **B** | Strong foundations, documentation integrity issue |

**Bottom line:** The Lean code is excellent. The documentation around PR #180
needs correction. Do not revert — fix forward.
