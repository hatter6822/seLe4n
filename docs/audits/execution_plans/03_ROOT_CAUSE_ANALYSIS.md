# 03 — Root-Cause Analysis of the Proof Gap

## 1. Current proof skeleton

The existing proof in `serviceRegisterDependency_preserves_acyclicity` (`Invariant.lean:367–394`) is structurally complete through all non-insertion branches:

| Branch | Hypothesis | Discharge method | Status |
|---|---|---|---|
| Source not found | `lookupService st svcId = none` | `simp [hSvc] at hReg` — no success | Complete |
| Dep not found | `lookupService st depId = none` | `simp [hDep] at hReg` — no success | Complete |
| Self-loop | `svcId = depId` | `simp [hSelf] at hReg` — no success | Complete |
| Idempotent | `depId ∈ svc.dependencies` | `exact hAcyc` — state unchanged | Complete |
| Cycle found | `serviceHasPathTo ... = true` | `simp [hCycle] at hReg` — no success | Complete |
| **Edge inserted** | `serviceHasPathTo ... ≠ true` | **`sorry`** | **TPI-D07** |

After all case-splits, the final branch has the goal state documented in [02_CODEBASE_AUDIT.md §4.2](./02_CODEBASE_AUDIT.md#42-preservation-theorem-and-sorry-site).

---

## 2. The three infrastructure gaps

Three specific missing proof components prevent closing the `sorry`. They form a strict dependency chain — each gap requires the previous gap's infrastructure.

### Gap 1 — No relational graph semantics

**What's missing:** `serviceHasPathTo` is an executable `Bool`-valued BFS function. It is opaque to Lean's proof engine in the sense that reasoning about arbitrary graph paths requires unfolding the BFS recursion at every step. For proofs about "no path exists," we need a `Prop`-valued inductive relation that supports structural induction over path construction.

**Why it blocks the proof:** The goal requires proving that `sid` cannot reach itself in the post-state for **any** `sid`. Without an inductive path relation, we would need to unfold the BFS for every possible starting point and every possible graph shape — an intractable approach.

**What we need:**
- `serviceEdge st a b : Prop` — direct dependency relationship (one hop)
- `serviceReachable st a b : Prop` — reflexive-transitive closure (arbitrary-length path)
- Structural lemmas (transitivity, right-append, single-edge construction)

### Gap 2 — No BFS soundness bridge

**What's missing:** Even with Gap 1's declarative path relation, we need a theorem connecting the executable BFS result to the declarative semantics:

> If `serviceHasPathTo st src target fuel = false` and the fuel is adequate, then `¬ serviceReachable st src target`.

This requires:
1. A **loop invariant** for the inner `go` function relating BFS state (`frontier`, `visited`, `fuel`) to declarative reachability.
2. A **fuel adequacy** argument showing `serviceBfsFuel st` provides enough fuel to explore all reachable nodes.

**Why it blocks the proof:** The hypothesis `hCycle : ¬ serviceHasPathTo st depId svcId ... = true` gives us information about the BFS computation, but the goal requires reasoning about graph structure in the post-state. The bridge lemma translates the BFS result into a graph-theoretic statement we can compose with the edge-insertion analysis.

### Gap 3 — No edge-insertion decomposition

**What's missing:** The classic single-edge-insertion cycle analysis:

> Any cycle in the post-state graph that uses the new edge `svcId → depId` must correspond to a pre-state path from `depId` to `svcId`.

Without this decomposition, we cannot reduce the post-state acyclicity goal to the pre-state BFS hypothesis.

**Why it blocks the proof:** Even if we know "no pre-state path from `depId` to `svcId` exists" (Gap 2) and "the pre-state is acyclic" (`hAcyc`), we cannot conclude the post-state is acyclic without analyzing how paths in the post-state relate to paths in the pre-state.

---

## 3. Dependency chain

The three gaps form a strict sequential dependency:

```
Gap 1: Declarative path relation (serviceEdge, serviceReachable)
  │
  └──▶ Gap 2: BFS soundness bridge (false → ¬reachable)
         │    Requires Gap 1's definitions for the bridge target
         │
         └──▶ Gap 3: Edge-insertion acyclicity preservation
                │    Requires Gap 2's bridge to translate BFS hypothesis
                │
                └──▶ sorry elimination
                     Requires Gap 3's composition of all three
```

This ordering directly determines the milestone sequence: M1 → M2 → M3.

---

## 4. Detailed proof stall analysis

### 4.1 Why naive BFS unfolding fails

One might attempt to prove the goal by directly unfolding `serviceHasPathTo` in both the hypothesis and the goal, then reasoning about the BFS computation. This fails for several reasons:

1. **Arbitrary `sid` quantification.** The goal is universally quantified over `sid`. The BFS must be analyzed for every possible starting service, not just `depId` and `svcId`.

2. **Post-state graph structure.** The BFS in the goal operates on `st'` (post-insert state), where `lookupService st' svcId` returns the service with the expanded dependency list. Reasoning about the BFS behavior on this modified state requires understanding how each node's expansion changes — which is exactly what the edge-insertion decomposition (Gap 3) provides.

3. **Fuel consumption.** The `go` function's non-standard recursion (fuel recycling on visited nodes) means the BFS computation tree is not simply a decreasing chain on `fuel`. Induction on `fuel` alone doesn't capture the BFS semantics — the frontier and visited-set evolution must also be tracked.

### 4.2 Why the bridge must be bidirectional (or the invariant must be reformulated)

The current invariant `serviceDependencyAcyclic` is defined in terms of the executable BFS:

```lean
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasPathTo st sid sid (serviceBfsFuel st) = true
```

The hypothesis `hAcyc : serviceDependencyAcyclic st` says: in the **pre-state**, no `sid` can BFS-reach itself. The goal demands: in the **post-state**, no `sid` can BFS-reach itself.

To close this, we need to reason as follows:

1. Assume for contradiction that some `sid` BFS-reaches itself in `st'`.
2. **BFS completeness direction:** `serviceHasPathTo st' sid sid ... = true` implies `serviceReachable st' sid sid` (BFS is complete: a `true` return means a real path exists). *This is the "easy" direction for BFS.*
3. By edge-insertion decomposition (Gap 3): the post-state cycle implies a pre-state path from `depId` to `svcId`.
4. **BFS soundness direction:** `¬ serviceReachable st depId svcId` (from the hypothesis via Gap 2) contradicts step 3.

**Alternatively (recommended — Option 2):** Reformulate the invariant in terms of `serviceReachable` and prove a one-time equivalence. This eliminates the need for the BFS completeness direction entirely:

```lean
def serviceDependencyAcyclicDecl (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceReachable st sid sid ∨ sid reaches itself is trivial (refl)
```

Wait — `serviceReachable` includes `refl` (every node reaches itself). So the invariant should be stated as: no **non-trivial** cycle exists, i.e., no path of length ≥ 1 from `sid` back to `sid`.

The precise formulation matters. See [M1: Declarative Semantics](./milestones/M1_DECLARATIVE_SEMANTICS.md#23-acyclicity-in-declarative-terms) for the detailed treatment.

### 4.3 The invariant-definition strategy (critical design decision)

Two viable strategies exist for connecting the BFS-based invariant to the declarative proof:

**Option 1 — Prove both directions of the BFS bridge, keep the original invariant definition.**

- Requires: `serviceHasPathTo ... = false → ¬ serviceReachable ...` (soundness) **AND** `serviceReachable ... → serviceHasPathTo ... = true` (completeness, under fuel adequacy).
- Advantage: no change to any existing definition.
- Disadvantage: proving BFS completeness is significantly harder than proving BFS soundness. The completeness argument requires showing the BFS discovers all reachable nodes before exhausting the frontier — a stronger claim than soundness.

**Option 2 (recommended) — Introduce a declarative acyclicity predicate and prove equivalence.**

- Define `serviceDependencyAcyclicDecl st := ∀ sid, ¬ serviceHasNontrivialPath st sid sid` using the inductive relation.
- Prove `serviceDependencyAcyclic st ↔ serviceDependencyAcyclicDecl st` (one-time bridge, using both BFS soundness and a weaker form of BFS completeness limited to self-reachability).
- Prove preservation of `serviceDependencyAcyclicDecl` across edge insertion (clean inductive proof).
- Use the equivalence to discharge the original goal.
- Advantage: the core acyclicity-preservation proof works entirely in the declarative domain, which is much cleaner. The BFS bridge is confined to the equivalence proof.
- Disadvantage: slightly more definitions. But the total proof complexity is lower.

**Recommendation:** Option 2. The cleaner proof structure outweighs the additional definitions. The equivalence theorem also serves as a reusable artifact connecting the executable BFS to declarative graph semantics.

---

## 5. Proof-state evolution through the insertion branch

The following traces the exact Lean 4 proof state as the existing proof enters the insertion branch (the `sorry` site), providing the precise starting point for the M2/M3 proof work:

```
-- After: cases hSvc : lookupService st svcId; simp only [hSvc] at hReg
-- After: cases hDep : lookupService st depId; simp only [hDep] at hReg
-- After: by_cases hSelf : svcId = depId; simp [hSelf] at hReg
-- After: by_cases hExists : depId ∈ svc.dependencies; simp [hExists] at hReg
-- After: by_cases hCycle : serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
-- After: simp only [hCycle] at hReg
-- After: unfold serviceDependencyAcyclic; intro sid
-- After: unfold storeServiceEntry at hReg; simp at hReg; cases hReg

Context:
  svcId depId : ServiceId
  svc : ServiceGraphEntry          -- source service entry
  depSvc : ServiceGraphEntry       -- dependency target entry
  hSvc : lookupService st svcId = some svc
  hDep : lookupService st depId = some depSvc
  hSelf : ¬ svcId = depId
  hExists : ¬ depId ∈ svc.dependencies
  hCycle : ¬ serviceHasPathTo st depId svcId (serviceBfsFuel st) = true
  hAcyc : serviceDependencyAcyclic st
  sid : ServiceId                  -- universally quantified in the goal

Goal:
  ¬ serviceHasPathTo
    (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
    sid sid
    (serviceBfsFuel (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st))
    = true
```

This is the exact proof state where the M2/M3 infrastructure connects.
