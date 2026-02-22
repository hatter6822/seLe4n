# Milestone M2 — BFS Soundness Bridge

**Goal:** Prove that a `false` return from `serviceHasPathTo` under sufficient fuel implies no declarative path exists. Also prove the converse direction (BFS `true` implies declarative path).

**Dependency:** M1 (declarative path definitions, structural lemmas)

**Estimated theorems added:** 7 (B1–B7 from the theorem inventory)

**Risk level:** HIGH — this is the technically hardest milestone. See [Risk R1](../05_RISK_REGISTER.md#risk-1) (fuel adequacy) and [Risk R3](../05_RISK_REGISTER.md#risk-3) (BFS loop invariant).

---

## 1. Overview: the two directions

| Direction | Statement | Difficulty | Required for | Status |
|---|---|---|---|---|
| **Easy (extraction)** | BFS returns `true` → declarative path exists | Medium | Full bidirectional EQ2 | Deferred (not needed for sorry elimination) |
| **Hard (completeness)** | Declarative path exists → BFS returns `true` | Hard | **Core: closing TPI-D07-BRIDGE sorry** | Detailed strategy in §5-§9 |
| **Derived (soundness)** | BFS returns `false` → no declarative path | Easy (from completeness) | Contrapositive of completeness | Follows automatically |

Both directions are needed for the full bidirectional equivalence. However, the
**completeness direction is the sole blocking obligation** for sorry elimination.
The extraction direction (B1-B3) and derived soundness (B6-B7) are stretch goals.

**Revised priority**: The original M2 plan treated "BFS `true` → path" as easy
and "BFS `false` → no path" as hard. After implementation experience, the actual
critical path is **completeness** (path → BFS `true`), which is what
`bfs_complete_for_nontrivialPath` asserts. The soundness direction (B6) follows
trivially from completeness via contrapositive. See §5 for detailed analysis.

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

## 5. Architectural analysis: why completeness is the hard path

### 5.1 The sorry under the microscope

The sole deferred obligation is at `Invariant.lean:526-531`:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (_hPath : serviceNontrivialPath st a b)
    (_hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  sorry
```

This theorem must bridge two worlds:

1. **Declarative world** (`Prop`): `serviceNontrivialPath st a b` — an inductive
   proof-term asserting at least one dependency edge from `a` toward `b`.
2. **Executable world** (`Bool`): `serviceHasPathTo st a b fuel = true` — a
   concrete BFS traversal that terminates with `true`.

The declarative side is a *witness* (it carries the path structure). The executable
side is an *algorithm* (it searches for any path). Proving that a witness-carrying
path forces the algorithm to return `true` requires showing the algorithm is
**complete**: it does not miss any reachable node.

### 5.2 Why this is fundamentally harder than the other direction

The *easy direction* (B1-B3: BFS `true` → declarative path) is extraction:
the BFS returns `true` only when it finds `target` in the frontier, and every
frontier element got there by following dependency edges. Reconstructing the
declarative path from BFS's execution trace is mechanical.

The *hard direction* (completeness: declarative path → BFS `true`) requires a
**coverage argument**: every node reachable from `src` eventually enters the BFS
frontier, given sufficient fuel. This is the standard BFS completeness argument
from algorithms textbooks, but formalizing it in a dependently-typed proof
assistant raises three interlocking challenges:

| Challenge | Root cause | Section |
|---|---|---|
| **Fuel recycling** | Visited-node branches recur with *same* fuel — simple Nat induction fails | §5.3 |
| **Frontier growth** | Expansion appends deps to frontier — frontier length is non-monotone | §5.4 |
| **Fuel adequacy** | `services : ServiceId → Option ServiceGraphEntry` is a function, not a finite map — counting registered services requires a bounding argument | §5.5 |

### 5.3 Challenge: fuel recycling in the visited branch

The `go` function has three recursive shapes:

```
go (node :: rest) visited (fuel + 1):
  Case A: node = target                    → true  (base case)
  Case B: node ∈ visited                   → go rest visited (fuel + 1)
  Case C: node ∉ visited, node ≠ target    → go (rest ++ newDeps) (node :: visited) fuel
```

In **Case B**, fuel does NOT decrease (`fuel + 1` is passed unchanged). This means
`Nat.rec` on `fuel` alone cannot drive the induction — the recursive call has the
same fuel. However, the *frontier shrinks* (`rest` is strictly shorter than
`node :: rest`).

In **Case C**, fuel decreases by 1 but the frontier can *grow* (deps are appended).

The correct termination/induction measure is **lexicographic on `(fuel, frontier.length)`**:
- Case B: `fuel` same, `frontier.length` strictly decreases.
- Case C: `fuel` strictly decreases (frontier.length irrelevant).

This is exactly the measure Lean's kernel used to accept the definition. The proof
must mirror it.

**Tactic template:**
```lean
-- Strong induction on fuel, with inner structural reasoning on frontier
induction fuel using Nat.strong_rec_on generalizing frontier visited with
| ind fuel ih =>
    match hF : frontier with
    | [] => ...
    | node :: rest =>
        if hTarget : node = target then ...
        else if hVis : node ∈ visited then
          -- frontier shrinks: apply ih with same fuel, rest
          ...
        else
          -- fuel decreases: apply ih with fuel, expanded frontier
          ...
```

### 5.4 Challenge: frontier growth and the closure invariant

When a node is expanded (Case C), the new frontier is
`rest ++ (lookupDeps st node).filter (· ∉ visited)`. The filter removes nodes
already in `visited` but NOT nodes already in `rest`. This means:

1. **Duplicates in frontier** are possible (same node can appear in `rest` and
   in `deps`). This does not affect correctness — the duplicate is handled as a
   visited-skip on second encounter — but it complicates frontier-length reasoning.

2. **Frontier length is non-monotone**: it can grow on expansion steps and shrink
   on visited-skip steps.

The key insight: we do NOT need frontier length to decrease globally. We only need
it to decrease within same-fuel recursive calls (Case B), and those always shrink
the frontier by exactly one element. Cross-fuel calls (Case C) can have any
frontier length because fuel has already decreased.

### 5.5 Challenge: fuel adequacy and the service counting problem

`serviceBfsFuel st = st.objectIndex.length + 256` provides a concrete fuel bound.
The BFS consumes fuel only when expanding a *new* (unvisited) node. So the BFS
can expand at most `serviceBfsFuel st` distinct nodes before fuel exhaustion.

For completeness, we need: the number of distinct nodes reachable from `src` is
at most `serviceBfsFuel st`. This requires bounding the **total number of
registered services**.

**The fundamental obstacle**: `st.services : ServiceId → Option ServiceGraphEntry`
is an opaque function. We cannot enumerate its domain or count its `some` values.
There is no `services.keys` or `services.length`.

**Resolution strategies** (choose during implementation):

| Strategy | Precondition style | Complexity | Recommended? |
|---|---|---|---|
| **A: Explicit bound hypothesis** | Add `hBound : serviceCountBounded st` as a precondition on `bfs_complete_for_nontrivialPath` | Low | Yes — pragmatic first step |
| **B: Model-level bound proof** | Prove that `storeServiceState` always adds to `objectIndex`, giving `|services| ≤ |objectIndex| + 256` unconditionally | Medium | Yes — eliminates precondition |
| **C: Reachability-local bound** | Prove fuel ≥ path length (not all services), avoiding global counting entirely | Medium-High | Attractive but subtle |

**Strategy A** is recommended as the initial implementation because it decouples
the completeness proof from the model analysis. The precondition can be discharged
later (Strategy B) or validated operationally.

**Strategy C** is an interesting alternative: instead of bounding *all* services,
bound only the nodes on the specific path. Since `serviceNontrivialPath` has
finite length, we can extract a path-length bound from the inductive structure.
However, the BFS might explore nodes *not* on the shortest path, consuming fuel
on irrelevant branches. So path-length alone is insufficient — we need a bound on
all nodes the BFS *could* explore, which brings us back to global counting.

---

## 6. Prerequisite lemmas (Phase 0 — implement first)

These lemmas are mechanical unfoldings of `serviceHasPathTo.go` and can be proved
immediately. They form the foundation for all subsequent work and should be placed
in `Invariant.lean` between the Layer 1 frame lemmas and the Layer 2 BFS bridge.

### 6.1 Helper definition: `lookupDeps`

The BFS computes dependency lists inline. A named helper simplifies proof reasoning:

```lean
/-- Extract the dependency list for a service, returning [] if not found.
    This mirrors the inline computation in serviceHasPathTo.go. -/
def lookupDeps (st : SystemState) (node : ServiceId) : List ServiceId :=
  match lookupService st node with
  | some svc => svc.dependencies
  | none => []
```

**Bridge lemma** connecting `lookupDeps` to `serviceEdge`:

```lean
/-- serviceEdge is equivalent to membership in lookupDeps.
    This bridges the Prop-level edge relation to the Bool-level BFS. -/
theorem serviceEdge_iff_lookupDeps {st : SystemState} {a b : ServiceId} :
    serviceEdge st a b ↔ b ∈ lookupDeps st a := by
  unfold serviceEdge lookupDeps
  constructor
  · rintro ⟨svc, hLookup, hMem⟩; rw [hLookup]; exact hMem
  · intro h
    cases hLookup : lookupService st a with
    | none => simp [hLookup] at h
    | some svc => exact ⟨svc, hLookup, by rwa [hLookup] at h⟩
```

**Why this matters**: The BFS `go` function pattern-matches on `lookupService` and
uses `svc.dependencies`. Every completeness proof case will need to connect
`serviceEdge st node w` (from the declarative path) to `w ∈ deps` (in the BFS
expansion). Without `serviceEdge_iff_lookupDeps`, this connection requires
re-deriving the pattern match each time.

### 6.2 BFS unfolding lemmas

These are definitional consequences of the `go` implementation. Each should be
provable by `simp [serviceHasPathTo.go]` or `unfold` + case analysis.

```lean
-- U1: Empty frontier always returns false
theorem go_nil_false (st : SystemState) (target : ServiceId)
    (visited : List ServiceId) (fuel : Nat) :
    serviceHasPathTo.go st target [] visited fuel = false

-- U2: Zero fuel always returns false
theorem go_fuel_zero_false (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) :
    serviceHasPathTo.go st target frontier visited 0 = false

-- U3: Target at head of frontier returns true (for fuel ≥ 1)
theorem go_target_cons (st : SystemState) (target : ServiceId)
    (rest visited : List ServiceId) (fuel : Nat) :
    serviceHasPathTo.go st target (target :: rest) visited (fuel + 1) = true

-- U4: Visited node is skipped without consuming fuel (when not target)
theorem go_visited_skip (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId) (fuel : Nat)
    (hNeTarget : node ≠ target) (hVis : node ∈ visited) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) =
    serviceHasPathTo.go st target rest visited (fuel + 1)

-- U5: Unvisited non-target node triggers expansion
theorem go_expand (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId) (fuel : Nat)
    (hNeTarget : node ≠ target) (hNotVis : node ∉ visited) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) =
    serviceHasPathTo.go st target
      (rest ++ (lookupDeps st node).filter (· ∉ visited))
      (node :: visited)
      fuel
```

**Implementation note on U5**: The `lookupDeps` helper must match the inline
`match` in `go` exactly. Verify by checking that `simp [serviceHasPathTo.go, lookupDeps]`
closes the goal, or use `unfold` + `split` + `rfl` if `simp` doesn't handle the
nested `match`.

### 6.3 BFS monotonicity lemma

This is useful but NOT required for the main completeness proof. It says that
*more fuel never hurts*:

```lean
-- U6 (optional): More fuel preserves true results
theorem go_fuel_mono (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel fuel' : Nat)
    (hLe : fuel ≤ fuel')
    (hTrue : serviceHasPathTo.go st target frontier visited fuel = true) :
    serviceHasPathTo.go st target frontier visited fuel' = true
```

**Proof strategy**: Induction on `(fuel, frontier.length)` lexicographic, mirroring
the `go` termination measure. Each case applies the IH with `fuel' - 1 ≥ fuel - 1`
or `fuel' ≥ fuel` (visited-skip case). This lemma would allow future proofs to
reason about "fuel ≥ N is sufficient" without tracking exact fuel values.

---

## 7. Completeness proof strategy (Phase 1 — the core)

### 7.1 Theorem decomposition

The sorry on `bfs_complete_for_nontrivialPath` should be discharged by composing
three lemmas:

```
bfs_complete_for_nontrivialPath
    = go_complete                     -- core loop completeness
    ∘ serviceReachable_of_nontrivialPath  -- (already proved, Layer 1)
    ∘ fuel_adequacy                   -- fuel bound justification
```

Concretely:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  -- Step 1: Extract reachability from nontrivial path
  have hReach : serviceReachable st a b := serviceReachable_of_nontrivialPath hPath
  -- Step 2: Apply core completeness with fuel adequacy
  exact go_complete_outer st a b (serviceBfsFuel st) hReach hNe (fuel_adequate st)
```

Where `go_complete_outer` and `fuel_adequate` are defined below.

### 7.2 Core completeness lemma: `go_complete_outer`

This is the entry-point wrapper that unfolds `serviceHasPathTo` to `go [src] [] fuel`:

```lean
/-- If src reaches target and src ≠ target, with adequate fuel,
    then serviceHasPathTo returns true. -/
theorem go_complete_outer
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hReach : serviceReachable st src target)
    (hNe : src ≠ target)
    (hFuel : serviceCountBounded st)  -- or explicit fuel ≥ bound
    : serviceHasPathTo st src target fuel = true := by
  unfold serviceHasPathTo
  exact go_complete_inner st target [src] [] fuel
    ⟨src, List.mem_cons_self _ _, hReach⟩  -- hFrontierReachable
    (by simp)                               -- hClosure (vacuous for empty visited)
    (by simp)                               -- hTargetNotVisited
    hFuel                                   -- fuel adequacy
```

### 7.3 Core loop invariant: `go_complete_inner`

This is the heart of the proof — the generalized statement over arbitrary
`frontier`/`visited`/`fuel` triples:

```lean
/-- BFS loop completeness: if the frontier contains a node that reaches target,
    the visited set is closed under expansion, target is not yet visited,
    and fuel is adequate, then go returns true.

    INV1 (frontier reachable): ∃ node ∈ frontier, serviceReachable st node target
    INV2 (visited closure):    ∀ v ∈ visited, ∀ w, serviceEdge st v w →
                                 w ∈ visited ∨ w ∈ frontier
    INV3 (target fresh):       target ∉ visited
    INV4 (fuel adequate):      fuel ≥ |distinct unvisited non-target nodes
                                        reachable from frontier|  -/
theorem go_complete_inner
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hReachable : ∃ node ∈ frontier, serviceReachable st node target)
    (hClosure : ∀ v ∈ visited, ∀ w, serviceEdge st v w → w ∈ visited ∨ w ∈ frontier)
    (hTargetFresh : target ∉ visited)
    (hFuel : fuel ≥ fuelNeeded st target frontier visited) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

Where `fuelNeeded` counts the number of distinct nodes the BFS might need to
expand (details in §7.5).

### 7.4 Proof of `go_complete_inner` — case analysis

**Induction measure**: Strong induction on `fuel`, with inner case analysis on
`frontier`. Within each fuel level, visited-skip cases (Case B) reduce frontier
length with same fuel, which terminates because frontier is finite.

**Case 1: `frontier = []`**
Contradicts `hReachable` (no node in empty frontier).

**Case 2: `frontier = node :: rest`, `node = target`**
By `go_target_cons` (U3), `go` returns `true`. Done.

**Case 3: `frontier = node :: rest`, `node ≠ target`, `node ∈ visited`**
By `go_visited_skip` (U4), the call reduces to `go rest visited (fuel + 1)`.
Apply the IH with:
- Same `fuel` (technically `fuel + 1`, but we use strong induction on the
  outer fuel which hasn't changed).
- `frontier' = rest` (strictly shorter).
- `visited' = visited` (unchanged).

Need to verify all invariants are maintained:
- **INV1**: `hReachable` gives `∃ node ∈ (node :: rest), ...`. Since `node ∈ visited`
  and `hClosure` ensures all children of `node` are in `visited ∨ frontier`, we need
  to show some node in `rest` reaches target. This is the *critical sub-lemma*:

  > **Lemma (frontier_reachable_after_skip)**: If `node ∈ visited`, `node ≠ target`,
  > and `hClosure` holds, and some node in `(node :: rest)` reaches target, then
  > some node in `rest` reaches target.

  **Proof sketch**: If the witness was `node` itself, then since
  `serviceReachable st node target` and `node ≠ target`, by `serviceReachable`
  inversion there exists `w` with `serviceEdge st node w` and
  `serviceReachable st w target`. Since `node ∈ visited` and `hClosure` holds,
  `w ∈ visited ∨ w ∈ frontier`. If `w ∈ frontier = node :: rest` and `w ≠ node`
  (or `w ∈ rest`), we have a witness in `rest`. If `w = node`, we have a
  self-loop which contradicts progress (but this needs careful handling).
  If `w ∈ visited`, we need to chase the closure chain further.

  **This is the hardest sub-case.** The resolution requires an inductive argument
  over the visited closure: from any visited node, follow edges through visited
  nodes until reaching a frontier node (which must happen because target is NOT
  in visited but IS reachable, so the path must eventually leave the visited set).

  **Recommended helper lemma:**

  ```lean
  /-- From a visited node that reaches target, there exists a frontier node
      that also reaches target, assuming the closure invariant. -/
  theorem visited_reaches_frontier
      (st : SystemState) (target : ServiceId)
      (frontier visited : List ServiceId)
      (hClosure : ∀ v ∈ visited, ∀ w, serviceEdge st v w →
                    w ∈ visited ∨ w ∈ frontier)
      (hTargetFresh : target ∉ visited)
      (v : ServiceId) (hVis : v ∈ visited)
      (hReach : serviceReachable st v target) (hNe : v ≠ target) :
      ∃ f ∈ frontier, serviceReachable st f target
  ```

  **Proof**: By induction on `serviceReachable st v target`. The `refl` case is
  impossible (`v ≠ target`). The `step` case gives `serviceEdge st v w` and
  `serviceReachable st w target`. By `hClosure`, `w ∈ visited ∨ w ∈ frontier`.
  If `w ∈ frontier`, done. If `w ∈ visited`, apply IH on `w`. Termination: the
  path through visited nodes is finite (bounded by the reachability proof structure).

  **Critical subtlety**: This induction works because `serviceReachable` is an
  inductive Prop — we're inducting on the *proof structure*, not on the visited
  set. The path in the proof has finite length, so the chain through visited nodes
  terminates.

- **INV2 (closure)**: Unchanged — visited didn't change.
- **INV3**: Unchanged — visited didn't change.
- **INV4**: `fuelNeeded` may decrease or stay the same — the frontier shrank but
  visited didn't change, so some unvisited frontier nodes may have been removed.

**Case 4: `frontier = node :: rest`, `node ≠ target`, `node ∉ visited`**
By `go_expand` (U5), the call reduces to:
```
go (rest ++ (lookupDeps st node).filter (· ∉ visited)) (node :: visited) fuel
```

Apply the IH with:
- `fuel' = fuel` (decreased from `fuel + 1`; strong induction step).
- `frontier' = rest ++ (lookupDeps st node).filter (· ∉ visited)`.
- `visited' = node :: visited`.

Need to verify all invariants are maintained:

- **INV1**: Need `∃ f ∈ frontier', serviceReachable st f target`. The original
  witness is some `w ∈ (node :: rest)` with `serviceReachable st w target`.
  - If `w ∈ rest`: `w ∈ frontier'` (since `rest ⊆ frontier'`).
  - If `w = node`: since `node ≠ target` and `serviceReachable st node target`,
    by inversion there's `serviceEdge st node u` and `serviceReachable st u target`.
    Then `u ∈ lookupDeps st node` (by `serviceEdge_iff_lookupDeps`). If
    `u ∉ visited`, then `u ∈ (lookupDeps st node).filter (· ∉ visited) ⊆ frontier'`.
    If `u ∈ visited`: need `visited_reaches_frontier` on `u` with the *updated*
    closure and frontier. This requires showing `hClosure` extends to `node :: visited`
    and `frontier'`.

- **INV2 (closure for `node :: visited`)**: For `v ∈ node :: visited`:
  - If `v = node`: For any `w` with `serviceEdge st node w`, we need
    `w ∈ (node :: visited) ∨ w ∈ frontier'`. We have
    `w ∈ lookupDeps st node` (by `serviceEdge_iff_lookupDeps`).
    If `w ∈ visited`: `w ∈ node :: visited`. Done.
    If `w ∉ visited`: `w ∈ (lookupDeps st node).filter (· ∉ visited) ⊆ frontier'`. Done.
  - If `v ∈ visited` (old): By `hClosure`, `w ∈ visited ∨ w ∈ (node :: rest)`.
    If `w ∈ visited`: `w ∈ node :: visited`. Done.
    If `w ∈ node :: rest`: either `w = node` (then `w ∈ node :: visited`) or
    `w ∈ rest ⊆ frontier'`. Done.

  **This case is clean.** The closure invariant is maintained because:
  (a) the newly visited node's children are all in the new frontier, and
  (b) old visited nodes' children that were in the old frontier are either
  still in the new frontier or are the newly visited node.

- **INV3 (target fresh in `node :: visited`)**: Since `node ≠ target` and
  `target ∉ visited`, we have `target ∉ node :: visited`.

- **INV4 (fuel adequacy)**: `fuelNeeded` decreases by at least 1 because `node`
  was an unvisited non-target frontier element and is now in visited.
  So `fuel' = fuel ≥ fuelNeeded - 1 = fuelNeeded'`.

### 7.5 The `fuelNeeded` measure

The fuel measure must count the maximum number of expansion steps remaining.
Each expansion adds exactly one new node to `visited` and consumes exactly one
fuel unit. So `fuelNeeded` is bounded by the number of distinct nodes that the
BFS might expand.

**Simplest correct definition** (proof-only, not computable):

```lean
/-- Upper bound on BFS expansion steps remaining: the number of distinct
    nodes that are (a) reachable from some frontier node via edges,
    (b) not in visited, and (c) not equal to target. -/
noncomputable def fuelNeeded
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) : Nat :=
  -- Conceptually: |{ n | ∃ f ∈ frontier, serviceReachable st f n,
  --                       n ∉ visited, n ≠ target }|
  -- In practice: bounded by serviceCountBounded st
```

**The problem**: This is not computable (it quantifies over all `ServiceId` values
reachable via a `Prop`). We cannot define it as a `Nat` directly.

**Practical resolution**: Instead of defining `fuelNeeded` as a concrete `Nat`,
state the fuel adequacy condition as an **abstract bound**:

```lean
-- Instead of: fuel ≥ fuelNeeded st target frontier visited
-- Use:        fuel ≥ distinctServiceCount st - visited.dedup.length
-- Where distinctServiceCount is bounded by serviceBfsFuel
```

Or more directly: parameterize the theorem by a list witnessing all reachable
services:

```lean
theorem go_complete_inner
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    -- ... (INV1, INV2, INV3 as before) ...
    -- INV4: There exists a finite set S containing all service IDs
    --        that could ever enter the BFS visited set, and fuel ≥ |S \ visited|.
    (allNodes : List ServiceId)
    (hAllNodes : ∀ sid, lookupService st sid ≠ none → sid ∈ allNodes)
    (hNodup : allNodes.Nodup)
    (hFuel : fuel ≥ allNodes.length - visited.dedup.length) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

**Why this works**: Every node the BFS could expand must be a registered service
(otherwise `lookupDeps` returns `[]` and no children are added). So the total
expansion count is bounded by `|allNodes|`. After each expansion, one node moves
from "unvisited" to "visited", so the remaining count decreases by 1.

**At the outer level**, `allNodes` is instantiated with a witness list from the
fuel adequacy precondition (Strategy A) or derived from the model (Strategy B).

### 7.6 Lemma dependency graph

```
go_complete_inner (§7.3)
  ├── go_nil_false (U1)
  ├── go_target_cons (U3)
  ├── go_visited_skip (U4)
  ├── go_expand (U5)
  ├── serviceEdge_iff_lookupDeps (§6.1)
  ├── visited_reaches_frontier (§7.4 helper)
  │     └── serviceReachable (induction on proof structure)
  ├── serviceReachable inversion (cases on .refl/.step)
  └── List reasoning (mem_append, mem_filter, mem_cons)

go_complete_outer (§7.2)
  ├── go_complete_inner
  └── fuel_adequate (§8)

bfs_complete_for_nontrivialPath (§7.1)
  ├── go_complete_outer
  └── serviceReachable_of_nontrivialPath (Layer 1, already proved)
```

---

## 8. Fuel adequacy strategy (Phase 2 — implement after core completeness)

### 8.1 Strategy A: explicit `serviceCountBounded` precondition

Add a precondition that the number of registered services is bounded:

```lean
/-- The total number of registered services is bounded by BFS fuel. -/
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ (allSids : List ServiceId),
    allSids.Nodup ∧
    (∀ sid, lookupService st sid ≠ none → sid ∈ allSids) ∧
    allSids.length ≤ serviceBfsFuel st
```

This is a clean Prop-level statement. The `allSids` witness enumerates all
registered services and is bounded by fuel. The BFS fuel is
`objectIndex.length + 256`, so this says: "there are at most
`objectIndex.length + 256` registered services."

**Impact on the preservation theorem**: The acyclicity preservation theorem
(`serviceRegisterDependency_preserves_acyclicity`) would gain an additional
hypothesis `(hBound : serviceCountBounded st)`. This is acceptable because:

1. Every concrete `SystemState` constructed by the test harness satisfies this
   bound (verifiable by `decide`).
2. The bound is preserved by `storeServiceState` (adding a service at most adds
   one entry, but also adds to `objectIndex` if the backing object is new).

**Preservation of `serviceCountBounded` across mutations:**

```lean
/-- storeServiceState preserves serviceCountBounded when the service
    is already registered (update, not insertion). -/
theorem serviceCountBounded_storeServiceState_update
    {st : SystemState} {sid : ServiceId} {entry : ServiceGraphEntry}
    (hBound : serviceCountBounded st)
    (hExists : lookupService st sid ≠ none) :
    serviceCountBounded (storeServiceState sid entry st)

/-- storeServiceState preserves serviceCountBounded when the service
    is new, provided the objectIndex grows (or the +256 slack absorbs it). -/
theorem serviceCountBounded_storeServiceState_new
    {st : SystemState} {sid : ServiceId} {entry : ServiceGraphEntry}
    (hBound : serviceCountBounded st)
    (hSlack : serviceBfsFuel (storeServiceState sid entry st) ≥
              serviceBfsFuel st) :
    serviceCountBounded (storeServiceState sid entry st)
```

### 8.2 Strategy B: unconditional bound from the model

If we can prove that every registered service has a backing object in
`objectIndex`, then `|registered services| ≤ |objectIndex| + 256 = serviceBfsFuel`:

```lean
/-- Every registered service has a backing object in objectIndex. -/
theorem service_has_backing_object (st : SystemState) (sid : ServiceId) :
    lookupService st sid ≠ none →
    ∃ oid ∈ st.objectIndex, (lookupService st sid).get! .identity.backingObject = oid
```

**Difficulty**: This requires a *global invariant* on `SystemState` — that the
services map was populated by kernel operations that always record backing objects.
The current model defines `services` as an opaque function, so this invariant
cannot be proved from the type alone; it must be carried as a hypothesis or proved
from operation traces.

**Recommendation**: Start with Strategy A. Migrate to Strategy B as a follow-up
if the precondition becomes burdensome.

### 8.3 Strategy C: reachability-local bound (advanced)

Instead of bounding all services, bound only the reachable subgraph:

```lean
/-- The BFS explores at most the nodes reachable from src. -/
theorem go_explores_only_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat) :
    -- If go returns true, it visited only nodes reachable from the initial frontier
    ... -- (not directly needed for completeness, but useful for fuel tightening)
```

The idea: since `serviceNontrivialPath st a b` has a concrete inductive structure
with finite depth, the reachable subgraph from `a` is bounded by the path's
structure. However, the BFS does not know about the shortest path and may explore
the entire connected component, making path-length bounds insufficient for fuel.

**Verdict**: Strategy C is elegant but requires additional infrastructure
(connected-component size bounds). Defer to a future optimization pass.

---

## 9. Implementation roadmap

### 9.1 Ordered implementation plan

| Step | Lemma / Task | Depends on | Difficulty | Est. LOC |
|---|---|---|---|---|
| **P0.1** | Define `lookupDeps` helper | — | Trivial | 5 |
| **P0.2** | `serviceEdge_iff_lookupDeps` | P0.1 | Easy | 10 |
| **P0.3** | BFS unfolding lemmas U1-U5 | P0.1 | Easy | 30 |
| **P0.4** | `go_fuel_mono` (U6, optional) | U1-U5 | Medium | 40 |
| **P1.1** | `visited_reaches_frontier` helper | — | Medium | 25 |
| **P1.2** | `go_complete_inner` (core loop) | U1-U5, P0.2, P1.1 | Hard | 80-120 |
| **P1.3** | `go_complete_outer` (wrapper) | P1.2 | Easy | 10 |
| **P2.1** | `serviceCountBounded` definition | — | Trivial | 5 |
| **P2.2** | `serviceCountBounded_storeServiceState_update` | P2.1 | Easy | 15 |
| **P2.3** | Integrate: close the sorry on `bfs_complete_for_nontrivialPath` | P1.3, P2.1 | Easy | 10 |
| **P2.4** | Update `serviceRegisterDependency_preserves_acyclicity` if needed | P2.3 | Easy | 5 |

### 9.2 What to implement vs what to defer

**Implement now (sorry elimination)**:
- P0.1-P0.3 (prerequisites)
- P1.1-P1.3 (core completeness)
- P2.1, P2.3 (fuel adequacy with Strategy A precondition)

**Implement as follow-up (polish)**:
- P0.4 (fuel monotonicity — useful but not blocking)
- P2.2 (bound preservation — needed for full composability)
- Strategy B (unconditional bound — eliminates precondition)

**Defer indefinitely (nice-to-have)**:
- B1 (inner function true → reachable): needed only if bidirectional equivalence is required
- B6 (false → no path): follows immediately from completeness by contrapositive
- B7 (false → no nontrivial path): follows from B6

### 9.3 File placement

All new definitions and lemmas go in `SeLe4n/Kernel/Service/Invariant.lean`:

```
Line ~508:  end of Layer 1 frame lemmas
            ──────────────────────────────────────
            NEW: §6 lookupDeps + serviceEdge_iff_lookupDeps
            NEW: §6 BFS unfolding lemmas U1-U5
            NEW: §7 visited_reaches_frontier
            NEW: §7 go_complete_inner
            NEW: §7 go_complete_outer
            NEW: §8 serviceCountBounded
            ──────────────────────────────────────
Line ~510:  Layer 2 BFS completeness bridge
            (bfs_complete_for_nontrivialPath — sorry replaced)
Line ~533:  Layer 3 post-insertion path decomposition
Line ~574:  Layer 4 acyclicity preservation
```

The Layer 2 header and `bfs_complete_for_nontrivialPath` theorem stay in place —
its `sorry` body is replaced with the composition from §7.1.

---

## 10. Known pitfalls and mitigations

### 10.1 Lean 4 `where`-defined functions and equation lemmas

The `go` function is defined using `where` syntax inside `serviceHasPathTo`. In
Lean 4, this generates `serviceHasPathTo.go` as a separate definition, but
equational lemmas (`.eq_def`, `.eq_1`, `.eq_2`, etc.) may or may not be generated
depending on the Lean version and recursion structure.

**Mitigation**: If `simp [serviceHasPathTo.go]` fails to unfold, try:
1. `unfold serviceHasPathTo.go`
2. `rw [serviceHasPathTo.go.eq_def]` (if generated)
3. `delta serviceHasPathTo.go` (nuclear option — may produce huge terms)

Test early (in P0.3) which approach works for the current toolchain (Lean 4.27.0).

### 10.2 `List.mem` decidability for `ServiceId`

The BFS uses `node ∈ visited` as a `Bool` test (via `BEq`/`DecidableEq` on
`ServiceId`). The proof-level `v ∈ visited` is `List.Mem v visited` (a `Prop`).
These are connected by `List.mem_iff_get` or `List.elem_iff_mem` depending on
the Lean/Std version.

**Mitigation**: Verify that `decide` can bridge between `Bool` membership and
`Prop` membership for `ServiceId`. If not, add:

```lean
theorem serviceId_mem_decide (sid : ServiceId) (l : List ServiceId) :
    (sid ∈ l) = true ↔ sid ∈ l := by
  simp [List.elem_iff_mem]  -- or: decide
```

### 10.3 Filter interaction with membership

The expression `deps.filter (· ∉ visited)` produces a list where:
- `x ∈ deps.filter (· ∉ visited) ↔ x ∈ deps ∧ x ∉ visited`

This must be used extensively in Case 4 of the loop invariant. Ensure that
`List.mem_filter` is available in the project's import set. If not:

```lean
theorem List.mem_filter' {α : Type} [DecidableEq α] {p : α → Bool}
    {a : α} {l : List α} :
    a ∈ l.filter p ↔ a ∈ l ∧ p a = true := by
  simp [List.mem_filter]
```

### 10.4 `List.Nodup` and `visited` growth

The `visited` list can contain duplicates in principle (the BFS adds `node`
to `node :: visited` without checking). However, by construction, the BFS only
adds a node to `visited` when `node ∉ visited`, so `visited` is actually always
`Nodup`. This is NOT needed for the completeness proof but is useful for fuel
adequacy (counting distinct visited nodes).

If needed, prove:

```lean
/-- The BFS visited list maintains no-duplicates. -/
theorem go_visited_nodup
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hNodup : visited.Nodup) :
    -- go returns true OR the final visited list is Nodup
    ...
```

This is tricky to state because `go` returns `Bool`, not a state with the visited
list. The visited list is internal to the recursion. This lemma may require
refactoring `go` or proving properties about intermediate states via a wrapper.

**Recommendation**: Avoid depending on `Nodup` for the completeness proof. Use
the `allNodes` enumeration in the fuel adequacy condition instead, which
sidesteps the need to track visited-list properties.

---

## 11. Exit criteria (updated)

> **Status: PREPARATION COMPLETE.** The documentation now contains a complete
> proof strategy for eliminating the `bfs_complete_for_nontrivialPath` sorry.
> The implementation roadmap (§9) identifies 10 ordered steps with explicit
> dependencies. Phase 0 (prerequisites) can begin immediately.

### M2 completion criteria

- [ ] `lookupDeps` helper defined (P0.1)
- [ ] `serviceEdge_iff_lookupDeps` bridge proved (P0.2)
- [ ] BFS unfolding lemmas U1-U5 proved (P0.3)
- [ ] `visited_reaches_frontier` helper proved (P1.1)
- [ ] `go_complete_inner` core loop completeness proved (P1.2)
- [ ] `go_complete_outer` wrapper proved (P1.3)
- [ ] `serviceCountBounded` defined (P2.1)
- [ ] `bfs_complete_for_nontrivialPath` sorry eliminated (P2.3)
- [ ] `lake build` succeeds with zero `sorry` in Service/Invariant.lean
- [ ] `./scripts/test_smoke.sh` passes

### Stretch goals (post-M2)

- [ ] `go_fuel_mono` (U6) proved
- [ ] `serviceCountBounded` preservation proved (P2.2)
- [ ] Strategy B: unconditional fuel adequacy (no precondition)
- [ ] B1-B3 easy direction (BFS true → declarative path)
- [ ] Full bidirectional equivalence EQ1/EQ2

## Validation

```bash
./scripts/test_tier1_build.sh
# After sorry elimination:
rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean  # should return 0 matches
./scripts/test_smoke.sh
```

> **Status: DEFERRED.** The full B1-B7 BFS soundness suite was not implemented. Instead, a single focused `sorry` was placed on `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE, Invariant.lean:526-531), which asserts BFS completeness for nontrivial paths between distinct services. This was sufficient for the M3 preservation proof. Fuel adequacy (Risk R1) and BFS loop invariant (Risk R3) remain deferred.

- [ ] `serviceHasPathTo_true_implies_reachable` (B2) — not implemented (deferred)
- [ ] `serviceHasPathTo_false_implies_not_reachable` (B6) — not implemented (deferred)
- [x] Fuel adequacy approach chosen: Approach B (preconditioned, implicit in TPI-D07-BRIDGE)
- [ ] Full BFS lemma suite (B1-B7) — deferred; `bfs_complete_for_nontrivialPath` with focused `sorry` used instead
- [x] `lake build` succeeds (with TPI-D07-BRIDGE warning)

## Validation

```bash
./scripts/test_tier1_build.sh
```
