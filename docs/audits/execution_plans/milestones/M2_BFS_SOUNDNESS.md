# Milestone M2 — BFS Soundness Bridge

**Goal:** Prove that a `false` return from `serviceHasPathTo` under sufficient fuel implies no declarative path exists. Also prove the converse direction (BFS `true` implies declarative path).

**Dependency:** M1 (declarative path definitions, structural lemmas)

**Estimated theorems added:** 7 (B1–B7 from the theorem inventory)

**Risk level:** HIGH — this is the technically hardest milestone. See [Risk R1](../05_RISK_REGISTER.md#risk-1) (fuel adequacy) and [Risk R3](../05_RISK_REGISTER.md#risk-3) (BFS loop invariant).

---

## 1. Overview: the two directions

| Direction | Statement | Difficulty | Required for |
|---|---|---|---|
| **Easy (completeness)** | BFS returns `true` → declarative path exists | Medium | EQ2 (declarative → BFS), edge-insertion proof |
| **Hard (soundness)** | BFS returns `false` → no declarative path | Hard | Core: translating `hCycle` hypothesis |

Both directions are needed for the full equivalence between `serviceDependencyAcyclic` and `serviceDependencyAcyclicDecl`.

---

## 2. Easy direction: BFS `true` → declarative path (B1, B2, B3)

### 2.1 Inner function — B1

```lean
/-- If `go frontier visited fuel = true`, then there exists some `node ∈ frontier` such that
    `serviceReachable st node target` holds. -/
theorem serviceHasPathTo_go_true_implies_exists_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hTrue : serviceHasPathTo.go st target frontier visited fuel = true) :
    ∃ node ∈ frontier, serviceReachable st node target
```

**Proof strategy:** Induction on `fuel`, generalizing over `frontier` and `visited`.

- **`fuel = 0`:** `go ... 0 = false`, contradicting `hTrue`.
- **`fuel + 1`, frontier empty:** `go ... [] = false`, contradicting `hTrue`.
- **`fuel + 1`, `node :: rest`:**
  - If `node = target`: witness is `node` with `serviceReachable.refl`.
  - If `node ∈ visited`: recursive call on `rest`. IH gives witness in `rest ⊆ frontier`.
  - If new node: recursive call on `rest ++ deps.filter ...`. IH gives witness `w`:
    - If `w ∈ rest`: `w` was already in the frontier.
    - If `w ∈ deps.filter ...`: `w` is a dependency of `node`. Compose `serviceEdge st node w` with `serviceReachable st w target` via `serviceReachable.step`.

**Key tactic pattern:**
```lean
induction fuel generalizing frontier visited with
| zero => simp [serviceHasPathTo.go] at hTrue
| succ n ih =>
    simp only [serviceHasPathTo.go] at hTrue
    match hFrontier : frontier with
    | [] => simp [hFrontier] at hTrue
    | node :: rest => ...
```

### 2.2 Outer function — B2

```lean
/-- If `serviceHasPathTo` returns `true`, then a declarative path exists. -/
theorem serviceHasPathTo_true_implies_reachable
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hTrue : serviceHasPathTo st src target fuel = true) :
    serviceReachable st src target := by
  -- serviceHasPathTo unfolds to go [src] [] fuel
  unfold serviceHasPathTo at hTrue
  rcases serviceHasPathTo_go_true_implies_exists_reachable st target [src] [] fuel hTrue
    with ⟨node, hMem, hReach⟩
  simp [List.mem_singleton] at hMem
  subst hMem
  exact hReach
```

### 2.3 Non-trivial variant — B3

```lean
/-- If src ≠ target and BFS returns true, the path is non-trivial. -/
theorem serviceHasPathTo_true_implies_nontrivial
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hNeq : src ≠ target)
    (hTrue : serviceHasPathTo st src target fuel = true) :
    serviceHasNontrivialPath st src target := by
  -- The BFS checks `node = target` before expanding. Since src ≠ target,
  -- the BFS must expand src and find a dependency edge to continue.
  -- This means the path has at least one edge.
  sorry -- Detailed proof depends on B1's internal structure
```

**Note:** B3 may require strengthening B1 to track that the first expansion step produces an edge. An alternative is to prove B3 from B2 by case analysis: if `serviceReachable st src target` and `src ≠ target`, then by inversion on the inductive type, the path must have a `.step` constructor, yielding a non-trivial path.

```lean
-- Alternative proof of B3 from B2:
theorem serviceHasPathTo_true_implies_nontrivial'
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hNeq : src ≠ target)
    (hTrue : serviceHasPathTo st src target fuel = true) :
    serviceHasNontrivialPath st src target := by
  have hReach := serviceHasPathTo_true_implies_reachable st src target fuel hTrue
  cases hReach with
  | refl => exact absurd rfl hNeq
  | step hedge hreach => exact ⟨_, hedge, hreach⟩
```

---

## 3. Hard direction: BFS `false` → no declarative path (B4, B5, B6, B7)

### 3.1 Loop invariant formulation — B4

The loop invariant for `go frontier visited fuel` captures the relationship between the BFS state and declarative reachability. For the **soundness** direction, we use the **contrapositive** formulation:

> If a declarative path from some frontier ancestor to `target` exists, then `go` returns `true`.

More precisely:

```lean
/-- BFS loop invariant (contrapositive soundness): if every reachable-from-frontier path
    to `target` is accounted for, then `go` finds `target` when it exists.

    Invariant: for any `a` such that `serviceReachable st a target` holds,
    if `a ∈ visited ∪ frontier`, then `go` returns `true` (assuming adequate fuel). -/
theorem serviceHasPathTo_go_complete
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    -- Fuel is adequate: at least as many as unvisited reachable nodes
    (hFuel : fuel ≥ cardReachableUnvisited st frontier visited)
    -- Some frontier node reaches target
    (hExists : ∃ node ∈ frontier, serviceReachable st node target)
    -- All predecessors of frontier nodes that are reachable are either visited or in frontier
    (hClosed : ∀ v ∈ visited, ∀ b, serviceEdge st v b → b ∈ visited ∨ b ∈ frontier) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

**This is extremely difficult to formalize directly.** A more practical approach:

#### Practical approach: contrapositive with fuel counting

Instead of proving the loop invariant directly, prove the **contrapositive** of B6:

> Assume `serviceReachable st src target`. Then `serviceHasPathTo st src target (serviceBfsFuel st) = true`.

This is the BFS **completeness** statement (under adequate fuel). Combined with B2 (true → reachable), this gives both directions.

**Proof strategy for completeness:**

1. Define a **decreasing measure** on BFS states: `(number of reachable nodes not in visited, fuel)` under lexicographic ordering.
2. Prove that each BFS step either finds the target (done) or strictly decreases the measure.
3. When the measure reaches `(0, _)`, all reachable nodes are visited, and if `target` is reachable, it must be in `visited`, which means the BFS would have returned `true` when it was first dequeued from the frontier.

**Alternative simpler approach:** Prove soundness via the **finite enumeration argument**:

1. The BFS explores nodes in BFS order. Each distinct expansion adds one node to `visited`.
2. After `k` expansions, `|visited| = k`. Since fuel starts at `serviceBfsFuel st` and each expansion decrements fuel by 1, the BFS can expand up to `serviceBfsFuel st` distinct nodes.
3. If `serviceBfsFuel st` exceeds the number of reachable nodes from `src`, then the BFS explores all reachable nodes.
4. If `target` is reachable, it will be encountered in the frontier at some point and the BFS returns `true`.
5. Contrapositive: if BFS returns `false`, `target` is not reachable.

### 3.2 Fuel adequacy — B5

This is the decision point described in [Risk R1](../05_RISK_REGISTER.md#risk-1).

#### Approach A (preferred): Preconditioned theorem

State fuel adequacy as an explicit hypothesis:

```lean
/-- Fuel adequacy precondition: the number of distinct services with entries in the graph
    is bounded by the BFS fuel. -/
def serviceFuelAdequate (st : SystemState) : Prop :=
  ∀ sid, lookupService st sid ≠ none →
    -- sid is "accounted for" by the fuel bound
    True  -- This is a placeholder; the actual condition depends on the counting argument

-- Practical formulation: the set of registered services is finite and bounded
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ bound : Nat, bound ≤ serviceBfsFuel st ∧
    ∀ (sids : List ServiceId),
      (∀ sid ∈ sids, lookupService st sid ≠ none) →
      sids.Nodup →
      sids.length ≤ bound
```

**The cleanest formulation** is to note that in the BFS, fuel is consumed only when expanding a **new** (unvisited) node. The BFS returns `false` only when either:
- The frontier is empty (all reachable nodes explored), or
- Fuel is exhausted (too many distinct nodes).

If we can show that the number of distinct nodes the BFS could ever visit is ≤ `serviceBfsFuel st`, then fuel exhaustion never occurs for reachable nodes.

**Concrete fuel adequacy lemma:**

```lean
/-- The BFS visits at most `serviceBfsFuel st` distinct nodes before fuel exhaustion.
    If the total number of registered services is at most `serviceBfsFuel st`,
    then the BFS explores all reachable nodes. -/
theorem serviceBfsFuel_sufficient
    (st : SystemState)
    (hBound : ∀ (sids : List ServiceId),
      (∀ sid ∈ sids, lookupService st sid ≠ none) →
      sids.Nodup →
      sids.length ≤ serviceBfsFuel st) :
    ∀ src target, serviceReachable st src target →
      serviceHasPathTo st src target (serviceBfsFuel st) = true
```

#### Approach B (fallback): Unconditional via model analysis

If we can prove that the `services` function in `SystemState` effectively has a finite support bounded by `objectIndex.length + 256`, this becomes unconditional. This requires showing that service creation always adds the backing object to `objectIndex`, providing the bound.

**Decision:** Make this choice during M2 implementation. If Approach A is chosen, the fuel adequacy hypothesis becomes a precondition on the final preservation theorem.

### 3.3 Soundness theorem — B6

```lean
/-- BFS soundness: if the BFS returns false with adequate fuel, no declarative path exists. -/
theorem serviceHasPathTo_false_implies_not_reachable
    (st : SystemState) (src target : ServiceId)
    (hFuel : serviceCountBounded st)  -- or whatever fuel adequacy formulation
    (hBfs : serviceHasPathTo st src target (serviceBfsFuel st) = false) :
    ¬ serviceReachable st src target := by
  intro hReach
  -- By fuel adequacy + BFS completeness, hReach implies BFS returns true
  have hTrue := serviceBfsFuel_sufficient st hFuel src target hReach
  -- Contradiction with hBfs
  rw [hTrue] at hBfs
  exact absurd rfl hBfs
```

### 3.4 Non-trivial soundness — B7

```lean
/-- BFS false implies no non-trivial path. -/
theorem serviceHasPathTo_false_implies_not_nontrivial
    (st : SystemState) (src target : ServiceId)
    (hFuel : serviceCountBounded st)
    (hBfs : serviceHasPathTo st src target (serviceBfsFuel st) = false) :
    ¬ serviceHasNontrivialPath st src target := by
  intro ⟨mid, hedge, hreach⟩
  exact serviceHasPathTo_false_implies_not_reachable st src target hFuel hBfs
    (.step hedge hreach)
```

---

## 4. Implementation guidance

### 4.1 Accessing the `go` function in proofs

The `where`-defined `go` function may require special handling in Lean 4:

```lean
-- Try these approaches in order:
-- 1. Direct unfold
unfold serviceHasPathTo serviceHasPathTo.go

-- 2. Simp with equational lemmas
simp only [serviceHasPathTo, serviceHasPathTo.go]

-- 3. If Lean generates .eq_def:
rw [serviceHasPathTo.go.eq_def]

-- 4. Pattern matching with split tactic
split <;> ...
```

### 4.2 Induction strategy for the BFS proof

The `go` function has **non-trivial recursion** (fuel recycling on visited nodes). For induction:

1. **Primary measure:** `fuel` (structurally decreasing in the expansion branch).
2. **Secondary measure for the visited branch:** `frontier.length` (strictly decreasing since `rest` is shorter than `node :: rest`).
3. **Combined:** Use strong induction on `fuel` with `frontier.length` tracked as an auxiliary argument, or use `termination_by` with a lexicographic measure.

**Practical approach:** Since the `go` function is well-founded (Lean accepted it), we can use the same termination measure Lean chose. In tactic mode, `induction fuel generalizing frontier visited` should work, with the visited-branch case resolved by noting the frontier strictly shrinks.

### 4.3 Key list reasoning lemmas

The BFS uses `List.filter`, `List.append`, and `List.mem`. Useful `simp` lemmas:

- `List.mem_append`
- `List.mem_filter`
- `List.mem_cons`
- `List.mem_singleton`
- `List.length_cons`
- `List.length_append`

If these are not available in the project's Lean/Std import set, they may need to be stated as local lemmas.

---

## 5. Exit criteria

> **Status: COMPLETED.** The full B1-B7 BFS soundness suite has been implemented
> and all theorems are proved without `sorry`. The BFS bridge
> `bfs_complete_for_nontrivialPath` is fully proved under the
> `serviceCountBounded` precondition (Approach A — explicit fuel adequacy
> hypothesis). Fuel adequacy is propagated as a precondition to
> `serviceRegisterDependency_preserves_acyclicity`.

- [x] `serviceHasPathTo_true_implies_reachable` (B2) — fully proved
- [x] `serviceHasPathTo_false_implies_not_reachable` (B7) — fully proved (contrapositive of B5)
- [x] Fuel adequacy approach: Approach A (preconditioned via `serviceCountBounded`)
- [x] Full BFS lemma suite (B1-B7) — all theorems proved without `sorry`
- [x] `lake build` succeeds with zero errors and zero `sorry` warnings

---

## 6. Implementation summary

The M2 milestone was completed using a direct BFS loop-invariant proof
strategy. Rather than decomposing into sub-milestones, all B1-B7 theorems
were proved in a single coherent implementation.

### 6.1 Proof architecture

The proof factors into two independent directions:

**Easy direction (B1-B3): BFS `true` → declarative path**
- B1 (`go_true_implies_exists_reachable`): Nested induction on `fuel` and
  `frontier`. If `go` returns `true`, some frontier node reaches target via
  `serviceReachable`. The key case is the expansion branch, where a
  dependency edge composes with the recursive result.
- B2 (`serviceHasPathTo_true_implies_reachable`): Wrapper that instantiates
  B1 with initial frontier `[src]` and empty visited list.
- B3 (`serviceHasPathTo_true_implies_nontrivial`): Derives from B2 by
  case-splitting `serviceReachable`: if `src ≠ target`, the `.refl` case
  is impossible, so the path has at least one `.step` constructor.

**Hard direction (B4-B7): declarative path → BFS `true`**
- `serviceCountBounded` (definition): Fuel adequacy precondition — for any
  source, all `Nodup` lists of reachable nodes have length < `serviceBfsFuel st`.
- `frontier_witness_of_reachable` (helper): Given the closure invariant
  (visited nodes' successors are in visited ∪ frontier), if a visited-or-frontier
  node reaches `target` and `target ∉ visited`, then some unvisited frontier
  node reaches `target`. Proved by induction on `serviceReachable`.
- B4 (`go_complete`): Core BFS loop completeness with 7 invariant conditions:
  (1) frontier witness reaches target, (2) frontier nodes reachable from src,
  (3) visited nodes reachable from src, (4) visited.Nodup, (5) target ∉ visited,
  (6) fuel + visited.length = serviceBfsFuel st, (7) closure invariant. Proved
  by induction on `fuel` with inner induction on `frontier`.
- B5 (`serviceHasPathTo_complete`): Outer wrapper instantiating B4 with
  initial state (frontier `[src]`, visited `[]`, vacuous closure).
- B6 (`bfs_complete_for_nontrivialPath`): Extracts reachability from
  nontrivial path and delegates to B5. Closes TPI-D07-BRIDGE.
- B7 (`serviceHasPathTo_false_implies_not_reachable`): Contrapositive of B5.

### 6.2 Key design decisions

1. **Fuel adequacy as precondition (Approach A):** `serviceCountBounded st`
   is an explicit hypothesis on `bfs_complete_for_nontrivialPath` and
   propagated to `serviceRegisterDependency_preserves_acyclicity`. This
   avoids model-level changes to `SystemState` while keeping the proof
   unconditional within its preconditions. The precondition is operationally
   guaranteed by the service creation protocol (service registration adds
   backing objects to `objectIndex`, bounding the service count).

2. **Induction strategy:** `go_complete` uses simple Nat induction on `fuel`,
   not well-founded or lexicographic induction. The fuel-recycling case
   (visited node skip) is handled by an inner induction on `frontier` within
   the `succ n` case: skipping a visited node does not consume fuel but
   strictly shrinks the frontier, so the inner IH applies. The expansion
   case consumes one fuel unit and strictly grows the visited list.

3. **Closure invariant formulation:** The invariant tracks that all successors
   of visited nodes are in visited ∪ frontier. This is maintained across both
   the skip and expansion cases. When the frontier witness enters the visited
   set (expansion case), `frontier_witness_of_reachable` extracts a new
   frontier witness, maintaining the invariant.

### 6.3 Theorem inventory (implemented)

| ID | Name | Status | Lines |
|---|---|---|---|
| B1 | `go_true_implies_exists_reachable` | Proved (private) | ~33 |
| B2 | `serviceHasPathTo_true_implies_reachable` | Proved | ~8 |
| B3 | `serviceHasPathTo_true_implies_nontrivial` | Proved | ~8 |
| — | `serviceCountBounded` (def) | Defined | ~5 |
| — | `frontier_witness_of_reachable` (helper) | Proved (private) | ~29 |
| B4 | `go_complete` | Proved (private) | ~100 |
| B5 | `serviceHasPathTo_complete` | Proved | ~15 |
| B6 | `bfs_complete_for_nontrivialPath` | Proved | ~5 |
| B7 | `serviceHasPathTo_false_implies_not_reachable` | Proved | ~6 |

## Validation

```bash
./scripts/test_tier1_build.sh
```
