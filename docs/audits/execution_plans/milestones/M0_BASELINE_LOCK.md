# Milestone M0 — Baseline Lock and Proof-Target Map

**Goal:** Freeze operational behavior, enumerate exact proof obligations, and verify all prerequisite infrastructure is available — without changing any executable code.

**Dependency:** None (entry milestone)

**Prerequisite resolved:** Risk 0 (vacuous invariant) — Strategy B adopted. The `serviceDependencyAcyclic` definition has been corrected from the vacuous BFS-based form to declarative non-trivial-path acyclicity. Layer 0 definitions (`serviceEdge`, `serviceReachable`, `serviceHasNontrivialPath`) are committed. This is a pre-M0 change that establishes the correct invariant foundation before the baseline is locked.

**Estimated theorems added:** 0 (audit and documentation only; Layer 0 definitions added as Risk 0 prerequisite)

---

## Tasks

### M0.1 — Branch shape audit

Verify that `serviceRegisterDependency` (`Operations.lean:142–160`) has exactly six branches as documented in [02_CODEBASE_AUDIT.md §2.1](../02_CODEBASE_AUDIT.md#21-serviceregisterdependency-check-ordering):

1. Source not found → `.error .objectNotFound`
2. Dep not found → `.error .objectNotFound`
3. Self-dependency → `.error .cyclicDependency`
4. Idempotent → `.ok ((), st)`
5. Cycle detected → `.error .cyclicDependency`
6. Edge inserted → `.ok ((), st')`

**Verification command:**
```bash
rg 'serviceRegisterDependency' SeLe4n/Kernel/Service/Operations.lean --context 20
```

Record the exact line numbers and branch structure. Confirm the post-simplification goal state at `Invariant.lean:394` matches the goal documented in [03_ROOT_CAUSE_ANALYSIS.md §5](../03_ROOT_CAUSE_ANALYSIS.md#5-proof-state-evolution-through-the-insertion-branch).

### M0.2 — Semantics freeze

Confirm the closure is **proof-only**:

- `Operations.lean` — zero definition changes. Record file hash.
- `State.lean` — definition signatures unchanged. New lemmas are permitted.
- `Object.lean`, `Prelude.lean` — zero changes.

**Verification command:**
```bash
# Record pre-TPI-D07 hashes for operational files
sha256sum SeLe4n/Kernel/Service/Operations.lean SeLe4n/Model/State.lean \
          SeLe4n/Model/Object.lean SeLe4n/Prelude.lean
```

### M0.3 — Theorem TODO map (COMPLETE)

A structured comment block has been added in `Service/Invariant.lean` above the acyclicity section listing all planned intermediate lemmas. This serves as a verifiable implementation checklist and provides in-source navigation.

**Status:** Complete. The comment block reflects Strategy B (declarative acyclicity directly in `serviceDependencyAcyclic`). Key differences from the original plan:
- `serviceDependencyAcyclicDecl` (D4) is no longer needed as a separate definition — `serviceDependencyAcyclic` now IS the declarative definition.
- Layer 4 equivalence theorems (EQ1/EQ2) are subsumed — no translation between BFS and declarative forms is needed in the final proof.
- The proof infrastructure plan covers Layers 0–3 with 31 planned definitions and lemmas.

### M0.4 — Store lemma inventory

Confirm the following lemmas from `State.lean` are available and sufficient:

| Lemma | Location | Status |
|---|---|---|
| `storeServiceState_lookup_eq` | `State.lean:180–185` | Available — confirmed by inspection |
| `storeServiceState_lookup_ne` | `State.lean:187–193` | Available — confirmed by inspection |

**Additional lemmas needed** (to be proved in M1):

| Lemma | Purpose | Proof sketch |
|---|---|---|
| `storeServiceState_objectIndex_eq` | `objectIndex` unchanged after `storeServiceState` | Unfold `storeServiceState`; the `with` record update only touches `services` |
| `storeServiceState_services_eq` | Services function at `sid` returns `some entry` | Already covered by `storeServiceState_lookup_eq` |

**Verification command:**
```bash
rg 'theorem storeServiceState' SeLe4n/Model/State.lean
```

### M0.5 — BFS equational access audit

Verify how Lean 4 exposes the BFS function for proof purposes. Since `go` is a `where`-defined local function with non-trivial recursion, determine whether:

1. `serviceHasPathTo.go` is accessible as a namespace-qualified identifier.
2. Lean generates `serviceHasPathTo.go.eq_def` or similar equational lemmas.
3. Direct `unfold serviceHasPathTo` and `unfold serviceHasPathTo.go` work in tactic mode.

If `go` is not directly accessible, the BFS soundness proof (M2) may need to use `simp only [serviceHasPathTo]` or pattern-match on the definition's reduction behavior.

**Verification command:**
```bash
# Check if go is accessible as a separate declaration
rg 'serviceHasPathTo\.go' SeLe4n/
```

---

## Exit criteria

- [x] No changes to executable definitions in `Operations.lean`
- [ ] File hashes recorded for all frozen files
- [x] Theorem TODO map comment block added to `Invariant.lean`
- [ ] Store lemmas inventoried and confirmed available
- [ ] BFS equational access verified
- [ ] `lake build` passes with changes

## Artifacts modified

- `SeLe4n/Kernel/Service/Invariant.lean` (Layer 0 definitions + proof plan comment block; Risk 0 Strategy B prerequisite)

## Validation

```bash
./scripts/test_tier1_build.sh
```
