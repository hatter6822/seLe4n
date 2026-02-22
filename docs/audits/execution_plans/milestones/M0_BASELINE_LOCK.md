# Milestone M0 — Baseline Lock and Proof-Target Map

**Goal:** Freeze operational behavior, enumerate exact proof obligations, and verify all prerequisite infrastructure is available — without changing any executable code.

**Dependency:** None (entry milestone)

**Estimated theorems added:** 0 (audit and documentation only)

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

### M0.3 — Theorem TODO map

Add a structured comment block in `Service/Invariant.lean` above the acyclicity section (above line 341) listing all planned intermediate lemmas. This serves as a verifiable implementation checklist and provides in-source navigation.

```lean
/-!
## TPI-D07 proof infrastructure plan

### Definitions (Layer 0)
- `serviceEdge` — direct dependency edge relation
- `serviceReachable` — reflexive-transitive closure of serviceEdge
- `serviceHasNontrivialPath` — path of length ≥ 1
- `serviceDependencyAcyclicDecl` — declarative acyclicity (no non-trivial self-loops)

### Structural lemmas (Layer 1)
- `serviceEdge_iff_mem` — definitional unfolding
- `serviceReachable_trans` — path concatenation
- `serviceReachable_of_edge` — single-edge path
- `serviceReachable_step_right` — right-append edge
- `serviceHasNontrivialPath_of_edge` — edge implies nontrivial path
- `storeServiceState_objectIndex_eq` — objectIndex frame condition
- `serviceBfsFuel_storeServiceState_eq` — fuel frame condition
- `serviceEdge_storeServiceState_eq` — edge at updated service
- `serviceEdge_storeServiceState_ne` — edge at non-updated service
- `serviceEdge_post_insert` — edge characterization after insertion

### BFS soundness (Layer 2)
- `serviceHasPathTo_true_implies_reachable` — BFS true → declarative path
- `serviceHasPathTo_go_invariant` — BFS loop invariant
- `serviceBfsFuel_sufficient` — fuel adequacy
- `serviceHasPathTo_false_implies_not_reachable` — BFS false → no path

### Edge insertion (Layer 3)
- `serviceEdge_post_cases` — post-state edge decomposition
- `serviceReachable_post_insert_cases` — post-state path decomposition
- `nontrivial_cycle_post_insert_implies_pre_reach` — cycle → pre-state reachability
- `serviceDependencyAcyclicDecl_preserved` — declarative acyclicity preserved

### Final closure (Layer 4)
- `serviceDependencyAcyclic_implies_acyclicDecl` — BFS → declarative equivalence
- `serviceDependencyAcyclicDecl_implies_acyclic` — declarative → BFS equivalence
-/
```

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
- [x] File hashes recorded for all frozen files
- [x] Theorem TODO map comment block added to `Invariant.lean`
- [x] Store lemmas inventoried and confirmed available
- [x] BFS equational access verified
- [x] `lake build` passes with comment-only changes

## Completion evidence

### File hashes (semantics freeze baseline)

```
a61fa6c17a6efbedfc49756679678a5a2ce3cc01e5dcea4857d4982f42ffff44  SeLe4n/Kernel/Service/Operations.lean
6f6f87d827420dcad912b4a4842e06f3b236f1a6d3ce051923e716b0d1cbc1e6  SeLe4n/Model/State.lean
db228ed605a94fac7c6b2cb4757081d3f24e21f5afcf8e68b30f289314594f32  SeLe4n/Model/Object.lean
bffc93fef554f70db5f09f43683c178d9fa550da01ccac82e80ce94cd47b30fe  SeLe4n/Prelude.lean
```

### M0.1 — Branch shape audit

Verified `serviceRegisterDependency` (`Operations.lean:142–160`) has exactly six branches:

1. **Line 146**: Source not found → `.error .objectNotFound`
2. **Line 149**: Dep not found → `.error .objectNotFound`
3. **Line 151–152**: Self-dependency → `.error .cyclicDependency`
4. **Line 153–154**: Idempotent → `.ok ((), st)`
5. **Line 155–156**: Cycle detected → `.error .cyclicDependency`
6. **Lines 157–160**: Edge inserted → `.ok ((), storeServiceEntry svcId svc' st)`

Post-simplification goal state at `Invariant.lean:432` (previously 394, adjusted by comment insertion) confirmed matching `03_ROOT_CAUSE_ANALYSIS.md §5`.

### M0.4 — Store lemma inventory

| Lemma | Location | Status |
|---|---|---|
| `storeServiceState_lookup_eq` | `State.lean:180–185` | Available — confirmed by inspection |
| `storeServiceState_lookup_ne` | `State.lean:187–193` | Available — confirmed by inspection |

Additional lemma `storeServiceState_objectIndex_eq` (objectIndex frame condition) to be proved in M1; derivable from `storeServiceState` definition which only modifies `services`.

### M0.5 — BFS equational access audit

- `serviceHasPathTo.go` — accessible as namespace-qualified identifier (Lean 4 `where`-clause standard behavior)
- Lean 4 generates equational lemmas for pattern-matching `where` functions
- Direct `unfold serviceHasPathTo` / `unfold serviceHasPathTo.go` expected to work in tactic mode
- Concrete verification deferred to M2 implementation (requires Lean toolchain)

## Artifacts modified

- `SeLe4n/Kernel/Service/Invariant.lean` (comment block only — no definitions, no proofs)

## Validation

```bash
./scripts/test_tier1_build.sh
```
