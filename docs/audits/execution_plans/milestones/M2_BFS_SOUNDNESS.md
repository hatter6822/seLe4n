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

---

## 6. Completeness proof roadmap — the harder path

> This section expands the deferred BFS completeness obligation
> (`bfs_complete_for_nontrivialPath`, TPI-D07-BRIDGE) into a concrete,
> implementable proof plan. The goal is to eliminate the sole remaining
> `sorry` in the proof surface by proving that the executable BFS is
> **complete**: every declarative nontrivial path is detected.

### 6.1 Precise obligation

The theorem to prove is:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

This is the **hard direction** of the BFS bridge. The easy direction
(BFS `true` → declarative path) is B1–B3 in the original plan. The hard
direction requires showing that the BFS explores enough of the graph to
find every reachable target.

**Decomposition:** The proof factors into two independent obligations:

1. **BFS completeness under adequate fuel (B4′):** If `serviceReachable st a b`
   and fuel is adequate, then `serviceHasPathTo st a b fuel = true`.
2. **Fuel adequacy (B5):** `serviceBfsFuel st` is adequate for any pair of
   registered services in state `st`.

The theorem then follows: `hPath` implies `serviceReachable st a b`
(by `serviceReachable_of_nontrivialPath`), apply B4′ with B5.

### 6.2 Strategy selection: induction on path length

There are two candidate proof strategies for B4′:

**Strategy A — Direct BFS simulation (loop-invariant approach):**
Prove that the BFS `go` function maintains an invariant relating its
`(frontier, visited)` state to declarative reachability. Show the invariant
implies `go` returns `true` when `target` is reachable. This is the approach
outlined in §3.1 (B4) but is extremely complex due to the non-standard
recursion (fuel recycling on visited nodes).

**Strategy B — Induction on declarative path length (recommended):**
Instead of reasoning about the BFS's internal state machine, reason about
the declarative path structure. Prove: if `serviceReachable st a b` holds,
then there exists a *simple* path (no repeated nodes) from `a` to `b`,
and the BFS with fuel ≥ the number of distinct services discovers this
path. This avoids the loop-invariant entirely.

**Recommendation: Strategy B.** The key insight is that we do not need to
characterize the full BFS behavior — we only need to show that for any
reachable pair, the BFS returns `true`. Strategy B decomposes this into
smaller, independently tractable lemmas.

### 6.3 Helper definitions needed

The following definitions should be added to `SeLe4n/Kernel/Service/Invariant.lean`
before attempting the completeness proof. Each is small and independently
verifiable.

#### 6.3.1 Service finiteness witness

```lean
/-- A list of service IDs that covers all registered services in state `st`.
    This is the finite support of the `services` function. -/
def registeredServices (st : SystemState) : List ServiceId :=
  -- Implementation note: Since `services : ServiceId → Option ServiceGraphEntry`
  -- has infinite domain, we cannot enumerate it directly. Two options:
  --
  -- Option A (preferred): Add a `serviceIndex : List ServiceId` field to
  --   SystemState that tracks registered services, mirroring `objectIndex`.
  --   All service-creating operations maintain this list.
  --
  -- Option B (preconditioned): State finiteness as a hypothesis:
  --   `∃ sids : List ServiceId, ∀ sid, lookupService st sid ≠ none → sid ∈ sids`
  --   This is weaker but avoids model changes.
  sorry
```

**Architectural recommendation:** Option A (adding `serviceIndex`) is cleaner.
The `objectIndex` field already establishes the pattern. Adding `serviceIndex`
to `SystemState` is a small, local change (see §6.8 for the migration plan).
If Option A is chosen, `registeredServices st = st.serviceIndex` and the
fuel adequacy proof becomes straightforward.

If modifying `SystemState` is undesirable, Option B works: the fuel adequacy
becomes a precondition on `bfs_complete_for_nontrivialPath`, which is
dischargeable in any concrete model where services are created through
`storeServiceState`.

#### 6.3.2 Predecessor lemma (BFS discovers immediate successors)

```lean
/-- If the BFS frontier contains `node`, `node` is not visited, fuel is
    sufficient, and `node = target`, then `go` returns `true`.

    This is the base case for completeness: the BFS checks `node = target`
    before anything else. -/
theorem serviceHasPathTo_go_finds_target_in_frontier
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hMem : target ∈ frontier) (hFuel : fuel ≥ 1) :
    -- NOTE: This requires induction on frontier prefix before `target`.
    -- If nodes before `target` are all visited, each is skipped with fuel
    -- recycling. If any is unvisited, it's expanded, but `target` remains
    -- in the frontier (in `rest` or via re-addition from deps).
    -- The precise statement needs: every node before `target` in `frontier`
    -- is either visited or does not remove `target` from future frontiers.
    sorry
```

**This is too strong as stated.** The issue is that expanding nodes before
`target` in the frontier may consume fuel and add new nodes, but `target`
could be pushed further back. A cleaner formulation uses the visited-set
monotonicity:

```lean
/-- If `target` is in the frontier and fuel is adequate, the BFS finds it.
    "Adequate" means: fuel ≥ number of unvisited non-target nodes that
    precede `target` in the BFS exploration order. -/
theorem serviceHasPathTo_go_frontier_contains_target
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hMem : target ∈ frontier)
    (hFuel : fuel ≥ frontier.length) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

**Proof strategy:** Induction on `frontier` with `fuel` generalized.

- **`frontier = []`:** contradicts `hMem`.
- **`frontier = node :: rest`:**
  - If `node = target`: BFS returns `true` immediately (fuel ≥ 1 since
    `frontier.length ≥ 1`).
  - If `node ∈ visited`: BFS calls `go rest visited (fuel + 1)`. Since
    `target ∈ rest` (from `hMem` and `node ≠ target`), and
    `fuel + 1 ≥ frontier.length ≥ rest.length + 1 > rest.length`, apply IH.
    Note: fuel *increases* here, so this is fine.
  - If `node` is new (unvisited, ≠ target): BFS calls
    `go (rest ++ deps.filter ...) (node :: visited) fuel`. We need
    `target ∈ rest ++ deps.filter ...` — which holds since `target ∈ rest`
    (from the frontier). And `fuel ≥ frontier.length = rest.length + 1`,
    but the new frontier is `rest ++ deps.filter ...` which may be longer.
    **This is where the simple bound breaks.**

**Refined approach — use fuel ≥ (number of distinct unvisited services):**

The key observation is that each expansion of a new node consumes exactly 1 fuel
and adds the node to `visited`. Since nodes in `visited` are never expanded again
(they are skipped with fuel recycling), the BFS expands at most `fuel` distinct
nodes total. If fuel ≥ (total number of registered services), every reachable
node is eventually expanded, and `target` must be found in the frontier at
the point it would be expanded.

This motivates the following cleaner formulation.

#### 6.3.3 Core completeness lemma (refined)

```lean
/-- Core BFS completeness: if some node in the frontier can reach `target`
    and the fuel exceeds the number of services not yet visited, then the
    BFS returns `true`.

    This is the precise loop invariant needed for completeness. -/
theorem serviceHasPathTo_go_complete
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    -- Some frontier node reaches target
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    -- Fuel exceeds unvisited reachable nodes
    -- (number of sids with lookupService st sid ≠ none that are not in visited)
    (hFuel : fuel ≥ countRegisteredNotIn st visited)
    -- Visited nodes are closed: all successors of visited nodes are
    -- either visited or in the frontier
    (hClosed : ∀ v ∈ visited, ∀ b, serviceEdge st v b →
      b ∈ visited ∨ b ∈ frontier) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

where:

```lean
/-- Count of registered services not in the given list.
    This serves as the fuel consumption bound for the BFS. -/
noncomputable def countRegisteredNotIn (st : SystemState) (visited : List ServiceId) : Nat :=
  -- Under Option A (serviceIndex field):
  --   (st.serviceIndex.filter (· ∉ visited)).length
  -- Under Option B (preconditioned):
  --   Given by hypothesis
  sorry
```

**Proof of `serviceHasPathTo_go_complete`:** Strong induction on `fuel` with
`frontier` and `visited` generalized.

**Base case (`fuel = 0`):** `hFuel` gives `0 ≥ countRegisteredNotIn st visited`.
This means every registered service is in `visited`. From `hReach`, some
`node ∈ frontier` reaches `target`. If `node = target`, we need the BFS to
check it — but `fuel = 0` means `go` returns `false`. **Contradiction:**
if all registered services are visited and `target` is registered (it must be,
since `node` reaches it via edges through registered services), then `target`
should be in `visited`. But `target ∈ visited` combined with `target` being
reachable means the BFS should have found it earlier... This doesn't quite
work for `fuel = 0` directly.

**Fix:** The base case needs: if `target ∈ frontier`, then `fuel ≥ 1` (since
the BFS needs at least one unit to process any frontier node). This is
guaranteed when `target ∉ visited` (since `target` is registered and not
visited, `countRegisteredNotIn ≥ 1`, so `fuel ≥ 1`). If `target ∈ visited`,
we need to show `target` was already found — but the BFS doesn't track that.

**The real fix** is to strengthen the invariant: add a precondition that
`target ∉ visited` (the BFS would have returned `true` when it first saw
`target`). See §6.4 for the properly formulated invariant.

### 6.4 Properly formulated BFS loop invariant

After careful analysis, the cleanest loop invariant for the completeness
direction is:

```lean
/-- BFS completeness invariant.

    Preconditions:
    (1) target ∉ visited (if target were visited, BFS would have already
        returned true when target was at the front of the frontier)
    (2) Every successor of a visited node is either visited or in the frontier
        (visited-set closure — the BFS doesn't miss reachable nodes)
    (3) Some node in the frontier reaches target
    (4) Fuel ≥ number of registered services not in visited

    Conclusion: go returns true. -/
theorem serviceHasPathTo_go_complete_inv
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hTargetNotVisited : target ∉ visited)
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    (hClosed : ∀ v ∈ visited, ∀ b, serviceEdge st v b →
      b ∈ visited ∨ b ∈ frontier)
    (hFuel : fuel ≥ countRegisteredNotIn st visited) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

**Proof by strong induction on `fuel`, generalizing `frontier` and `visited`:**

Obtain the witness: `⟨node, hNodeMem, hNodeReach⟩ := hReach`.

**Case `fuel = 0`:**
From `hFuel`: every registered service is visited. Since `target ∉ visited`,
target is not registered: `lookupService st target = none`. But `node` reaches
`target` via `serviceReachable` — if `node = target`, the path is trivial
(`.refl`) and the BFS checks `node = target` in the frontier... but `fuel = 0`
means `go` returns `false`. This gives us a contradiction ONLY if we can show
`frontier` is non-empty and `fuel ≥ 1`. Since `node ∈ frontier`, `frontier`
is non-empty, but `fuel = 0` means we can't process it. So we need
`fuel ≥ 1`.

Wait — `countRegisteredNotIn st visited = 0` means every registered service
is visited. `target ∉ visited`, so `target` is not registered. But
`serviceReachable st node target` requires either `node = target` (`.refl`)
or a chain of `serviceEdge`s. If `node = target`, we need fuel ≥ 1.
The problem is `hFuel : 0 ≥ 0` is satisfied vacuously.

**Resolution:** The `fuel = 0` case can't arise when `frontier` is non-empty
AND there is a reachable target not in visited. Here's why: `node ∈ frontier`
and `target ∉ visited`. If `node = target`, `node ∉ visited`, so `node` is
a registered service not in visited (assuming `node` is registered — which
it must be since it's in the frontier). So `countRegisteredNotIn ≥ 1`, and
`fuel ≥ 1`. **Key insight: we need to know that frontier nodes are registered.**

This leads to the following refined version.

### 6.5 Final refined invariant (recommended implementation)

```lean
/-- BFS completeness (final formulation).

    The proof proceeds by well-founded induction on the pair
    (fuel, frontier.length) under lexicographic ordering. -/
theorem serviceHasPathTo_go_complete_final
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    -- P1: target not yet visited
    (hTV : target ∉ visited)
    -- P2: some frontier node reaches target via edges between
    --     registered services
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    -- P3: visited-set closure (BFS explored all successors of visited nodes)
    (hClosed : ∀ v ∈ visited, ∀ b, serviceEdge st v b →
      b ∈ visited ∨ b ∈ frontier)
    -- P4: fuel bounds distinct unvisited registered services
    (hFuel : fuel ≥ countUnvisitedRegistered st visited)
    -- P5: all frontier nodes are either registered or target
    -- (ensures we can bound fuel consumption)
    (hFrontierReg : ∀ n ∈ frontier, lookupService st n ≠ none ∨ n = target) :
    serviceHasPathTo.go st target frontier visited fuel = true := by
  sorry -- Proof sketch follows in §6.6
```

where:

```lean
/-- Count of registered service IDs not in the visited list. -/
def countUnvisitedRegistered (st : SystemState) (visited : List ServiceId) : Nat :=
  -- With serviceIndex: (st.serviceIndex.filter (· ∉ visited)).length
  -- Without: requires external bound as hypothesis
  sorry
```

### 6.6 Proof sketch for the final formulation

The proof uses well-founded induction on
`(countUnvisitedRegistered st visited, frontier.length)` under
lexicographic order. Alternatively, strong induction on `fuel` with
`frontier.length` as an auxiliary measure for the visited-node case.

**Step 1: Unfold `go` and case-split on frontier.**

```lean
unfold serviceHasPathTo.go
match hF : frontier with
| [] => -- frontier empty: contradicts hReach (∃ node ∈ [], ...)
         exact absurd (List.not_mem_nil _) hNodeMem
| node :: rest => ...
```

**Step 2: Case-split on `node = target`.**

```lean
| node :: rest =>
    by_cases hEq : node = target
    | isTrue => -- node = target: BFS returns true immediately
                simp [hEq]
    | isFalse => ...
```

**Step 3: Case-split on `node ∈ visited`.**

```lean
    | isFalse =>
        by_cases hVis : node ∈ visited
        | isTrue =>
            -- node ∈ visited: BFS calls go rest visited (fuel + 1)
            -- Frontier shrinks: rest.length < (node :: rest).length
            -- Target still reachable from rest:
            --   If node was our witness, since node ∈ visited and target ∉ visited,
            --   node ≠ target. By hClosed, all successors of node are in
            --   visited ∨ frontier. Follow the path from node: the first
            --   unvisited node on the path must be in frontier (= rest, since
            --   node is removed). So ∃ node' ∈ rest, reachable st node' target.
            -- Apply IH with:
            --   frontier := rest (shorter)
            --   visited := visited (unchanged)
            --   fuel := fuel + 1 (≥ fuel ≥ countUnvisited, still adequate)
            sorry
        | isFalse => ...
```

**Step 4: New node expansion.**

```lean
        | isFalse =>
            -- node ∉ visited, node ≠ target: BFS expands node
            -- BFS calls: go (rest ++ deps.filter (· ∉ visited))
            --               (node :: visited) fuel
            -- Fuel decreases by 1 (structural decrease)
            -- countUnvisitedRegistered decreases by 1 (node was unvisited,
            --   now in visited)
            -- Need to show: hReach, hClosed, hTV, hFrontierReg hold for new state
            --
            -- hReach transfer: if our witness was `node`, since node ≠ target,
            --   node reaches target via at least one edge. Let node →edge mid →* target.
            --   mid is a successor of node. Either:
            --     - mid ∈ rest (already in frontier): witness transfers
            --     - mid ∉ visited: mid ∈ deps.filter (· ∉ visited), so mid ∈ new frontier
            --   In either case, ∃ mid ∈ newFrontier, reachable st mid target.
            --
            -- hClosed transfer: node is now visited. All successors of node are
            --   in (node :: visited) or (rest ++ deps.filter ...). For previously
            --   visited nodes, their successors were in visited ∨ (node :: rest).
            --   node is now visited, so successors pointing to node are covered.
            --   Successors in rest are in the new frontier (rest ⊆ newFrontier).
            --   ✓
            --
            -- hFuel transfer: fuel ≥ countUnvisited - 1 (node removed from
            --   unvisited). Since original fuel ≥ countUnvisited and we pass
            --   fuel (= original fuel - 1), need fuel - 1 ≥ countUnvisited - 1.
            --   ✓ (from fuel ≥ countUnvisited)
            --
            -- Apply IH with decreased fuel.
            sorry
```

### 6.7 Prerequisite lemma inventory

The following lemmas should be proved **before** attempting the main
completeness theorem. Each is small, focused, and independently testable.
They are ordered by dependency.

#### Tier 1: List membership and BFS structure (no sorry expected)

| # | Name | Statement | Difficulty | Notes |
|---|------|-----------|------------|-------|
| H1 | `go_eq_true_of_target_head` | `go st target (target :: rest) visited (fuel + 1) = true` | Easy | Direct unfolding; `if node = target then true` |
| H2 | `List.mem_filter_not_mem` | `a ∈ xs.filter (· ∉ ys) → a ∉ ys` | Easy | From `List.mem_filter` |
| H3 | `List.mem_filter_of_mem_not_mem` | `a ∈ xs → a ∉ ys → a ∈ xs.filter (· ∉ ys)` | Easy | From `List.mem_filter` |
| H4 | `frontier_rest_mem` | `a ∈ rest → a ∈ rest ++ deps.filter (· ∉ visited)` | Easy | `List.mem_append` left |
| H5 | `deps_filter_mem` | `a ∈ deps → a ∉ visited → a ∈ rest ++ deps.filter (· ∉ visited)` | Easy | `List.mem_append` right + H3 |

#### Tier 2: Reachability transfer through visited nodes

| # | Name | Statement | Difficulty | Notes |
|---|------|-----------|------------|-------|
| H6 | `reachable_from_visited_transfers_to_frontier` | If `v ∈ visited`, `serviceReachable st v target`, `target ∉ visited`, and `hClosed` holds, then `∃ n ∈ frontier, serviceReachable st n target` | Medium | Key lemma for Step 3. Induction on `serviceReachable`. At each step, the current node is visited; its successor is either visited (continue) or in frontier (found witness). Since target ∉ visited, the path must eventually leave visited. |
| H7 | `reachable_witness_transfer_on_expand` | If `node ≠ target`, `serviceReachable st node target`, then `∃ mid, serviceEdge st node mid ∧ serviceReachable st mid target` | Easy | Inversion on `serviceReachable`: must be `.step` case since `node ≠ target` rules out `.refl`. |

#### Tier 3: Fuel and counting

| # | Name | Statement | Difficulty | Notes |
|---|------|-----------|------------|-------|
| H8 | `countUnvisited_cons` | `n ∉ visited → lookupService st n ≠ none → countUnvisitedRegistered st (n :: visited) = countUnvisitedRegistered st visited - 1` | Medium | Depends on `countUnvisitedRegistered` definition. With `serviceIndex`, this is a list filter length lemma. |
| H9 | `countUnvisited_cons_le` | `countUnvisitedRegistered st (n :: visited) ≤ countUnvisitedRegistered st visited` | Easy | Monotonicity: more visited → fewer unvisited. |
| H10 | `fuel_adequate_after_expand` | `fuel ≥ countUnvisitedRegistered st visited → n ∉ visited → lookupService st n ≠ none → fuel - 1 ≥ countUnvisitedRegistered st (n :: visited)` | Medium | Combines H8 with arithmetic. |

#### Tier 4: Closure maintenance

| # | Name | Statement | Difficulty | Notes |
|---|------|-----------|------------|-------|
| H11 | `closure_maintained_on_expand` | If `hClosed` holds for `(visited, frontier = node :: rest)` and we expand `node` (adding successors), then `hClosed` holds for `(node :: visited, rest ++ deps.filter (· ∉ visited))` | Medium-Hard | Core invariant maintenance. For `v ∈ visited`: successors were in `visited ∨ (node :: rest)`. If successor was `node`, now `node ∈ (node :: visited)` ✓. If successor was in `rest`, it's in the new frontier ✓. For `v = node`: successors `b` are in `deps` (from `lookupService`). If `b ∈ visited`, done. If `b ∉ visited`, then `b ∈ deps.filter (· ∉ visited)` ⊆ new frontier ✓. |
| H12 | `closure_maintained_on_skip` | If `hClosed` holds for `(visited, node :: rest)` and `node ∈ visited`, then `hClosed` holds for `(visited, rest)` | Medium | For `v ∈ visited`: successors were in `visited ∨ (node :: rest)`. If successor was `node`, `node ∈ visited` ✓. If successor was in `rest`, still in rest ✓. |

### 6.8 Architectural change: `serviceIndex` field (Option A)

Adding a `serviceIndex` field to `SystemState` is the cleanest path to
fuel adequacy. This section documents the precise change and its impact.

#### Change description

```lean
-- In SeLe4n/Model/State.lean, add to SystemState:
structure SystemState where
  machine : SeLe4n.MachineState
  objects : SeLe4n.ObjId → Option KernelObject
  objectIndex : List SeLe4n.ObjId
  services : ServiceId → Option ServiceGraphEntry
  serviceIndex : List ServiceId        -- NEW: tracks registered service IDs
  scheduler : SchedulerState
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  lifecycle : LifecycleMetadata
```

#### Impact analysis

| Area | Impact | Effort |
|------|--------|--------|
| `SystemState` default instance | Add `serviceIndex := []` | Trivial |
| `storeServiceState` | Add `sid` to `serviceIndex` if not present | Small |
| `serviceBfsFuel` | Redefine as `st.serviceIndex.length + 1` (or keep current) | Small |
| `BootstrapBuilder` / test fixtures | Update to include `serviceIndex` | Small |
| Existing proofs | `storeServiceState` lemmas need updating for new field; existing frame lemmas (`serviceEdge_storeServiceState_ne` etc.) are unaffected since they only use `services` | Medium |
| `countUnvisitedRegistered` | Becomes `(st.serviceIndex.filter (· ∉ visited)).length` — computable, no sorry | Eliminates sorry |

#### Model-level invariant (with serviceIndex)

```lean
/-- The serviceIndex accurately reflects the services function:
    every registered service is indexed, and every indexed service is registered. -/
def serviceIndexSound (st : SystemState) : Prop :=
  (∀ sid ∈ st.serviceIndex, lookupService st sid ≠ none) ∧
  (∀ sid, lookupService st sid ≠ none → sid ∈ st.serviceIndex) ∧
  st.serviceIndex.Nodup
```

This invariant is straightforward to maintain across `storeServiceState`
calls and provides the fuel adequacy bridge.

#### Alternative: keep current model, use precondition

If the `serviceIndex` change is deferred, the fuel adequacy can be
stated as a precondition:

```lean
/-- Fuel adequacy precondition: there exists a finite bound on registered
    services that is ≤ serviceBfsFuel st. -/
def fuelAdequate (st : SystemState) : Prop :=
  ∃ (sids : List ServiceId),
    sids.Nodup ∧
    (∀ sid, lookupService st sid ≠ none → sid ∈ sids) ∧
    sids.length ≤ serviceBfsFuel st
```

Then `bfs_complete_for_nontrivialPath` becomes:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hFuel : fuelAdequate st)
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

**Trade-off:** This adds a precondition to the preservation theorem's
dependency chain. The precondition is always dischargeable in concrete
models (where services are created through `storeServiceState` and
the number is finite), but it weakens the unconditional guarantee.

### 6.9 Well-founded induction measure

The `go` function's termination is accepted by Lean via a measure that
handles the fuel-recycling pattern. For the completeness proof, we need
an explicit well-founded measure for our induction.

**Recommended measure:** Lexicographic `(fuel, frontier.length)` under the
standard `Nat × Nat` well-founded ordering (`Prod.Lex`).

| BFS branch | fuel change | frontier change | Measure decrease |
|------------|-------------|-----------------|------------------|
| `fuel = 0` | — | — | Base case |
| `frontier = []` | — | — | Base case |
| `node = target` | — | — | Returns `true` (no recursion) |
| `node ∈ visited` | `fuel → fuel + 1` (increase!) | `node :: rest → rest` (decrease) | Second component decreases; first may increase but we can use strong induction on fuel to handle this |
| `node ∉ visited` | `fuel + 1 → fuel` (decrease) | `node :: rest → rest ++ deps.filter ...` (may increase) | First component decreases |

**The visited-node case is the tricky one:** fuel increases but frontier
shrinks. For the proof, we can handle this by:

1. **Strong induction on `fuel`** (instead of structural): this lets us use the
   IH for any fuel′ ≤ fuel. Since the visited case passes `fuel + 1` to the
   recursive call, we cannot directly apply strong induction on the fuel
   argument passed to `go`.

2. **Better approach — induction on a combined measure:**
   Define `measure := countUnvisitedRegistered st visited`. This strictly
   decreases on every expansion (new node added to visited) and stays the same
   on visited-node skips (but frontier shrinks). Use lexicographic induction
   on `(countUnvisitedRegistered st visited, frontier.length)`.

   In the visited-node case: `countUnvisited` unchanged, `frontier.length`
   decreases → lexicographic decrease ✓.
   In the expansion case: `countUnvisited` decreases → lexicographic decrease ✓.

   This is the **correct** induction measure for the completeness proof.

**Implementation in Lean 4:**

```lean
-- Use well-founded recursion with explicit measure:
theorem serviceHasPathTo_go_complete_final ... := by
  -- Induct on the combined measure
  have hMeasure : (countUnvisitedRegistered st visited, frontier.length) ∈ ...
  induction h : (countUnvisitedRegistered st visited, frontier.length)
    using WellFoundedRelation.wf.induction
    generalizing frontier visited fuel with
  ...
```

Alternatively, use `Nat.strongRecOn` on `countUnvisitedRegistered st visited`
and inner induction on `frontier.length` for the visited-node case:

```lean
theorem serviceHasPathTo_go_complete_final ... := by
  -- Outer induction on unvisited count
  induction countUnvisitedRegistered st visited using Nat.strongRecOn
    generalizing frontier visited fuel with
  | ind n ih =>
    -- Inner case analysis (or induction on frontier.length for visited case)
    ...
```

### 6.10 Sequencing plan for implementation

The following sequence minimizes risk and produces independently verifiable
intermediate artifacts:

| Step | Deliverable | Depends on | Risk | Estimated theorems |
|------|-------------|------------|------|-------------------|
| S1 | Tier 1 helper lemmas (H1–H5) | None | Low | 5 |
| S2 | Tier 2 transfer lemmas (H6–H7) | S1 | Medium | 2 |
| S3 | `serviceIndex` field OR `fuelAdequate` precondition (§6.8) | None (parallel with S1–S2) | Medium | 1 definition + maintenance lemmas |
| S4 | Tier 3 fuel/counting lemmas (H8–H10) | S3 | Medium | 3 |
| S5 | Tier 4 closure lemmas (H11–H12) | S1, S2 | Medium-Hard | 2 |
| S6 | `serviceHasPathTo_go_complete_final` (§6.5) | S1–S5 | Hard | 1 |
| S7 | `bfs_complete_for_nontrivialPath` (eliminate sorry) | S6 | Easy | 1 (wrapper) |
| S8 | Easy direction B1–B3 (§2) | S1 | Medium | 3 |
| **Total** | | | | **~18 lemmas/theorems** |

**Critical path:** S3 → S4 → S5 → S6 → S7. The `serviceIndex` decision (S3)
is the earliest blocker: if Option A is chosen, S4 becomes straightforward;
if Option B, S4 requires a preconditioned approach.

**Parallelism:** S1–S2 and S3 can proceed in parallel. S8 (easy direction)
is independent of S3–S7.

### 6.11 Risk mitigations specific to the completeness path

| Risk | Mitigation | Fallback |
|------|------------|----------|
| `go` function opaque to unfolding | Use `serviceHasPathTo.go.eq_def` or `simp only [serviceHasPathTo.go]`. Test which tactic works in a minimal scratch file first. | If neither works, define a `go_unfold` lemma manually by case-splitting on fuel and frontier. |
| Fuel-recycling case complicates induction | Use `(countUnvisited, frontier.length)` lexicographic measure (§6.9) instead of raw `fuel` induction. | If lexicographic induction is awkward in Lean 4, use an auxiliary `go'` function with explicit decreasing measure and prove `go = go'`. |
| `countUnvisitedRegistered` not computable without `serviceIndex` | Precondition approach (§6.8 Option B): carry finiteness as hypothesis. | Add `serviceIndex` field (§6.8 Option A) to make it computable. |
| Closure maintenance (H11) too complex | Factor into sub-lemmas: one for old-visited-node successors, one for newly-expanded-node successors. | If list reasoning is intractable, introduce a `Finset`-based proof layer (Risk 2 fallback). |
| Path transfer through visited set (H6) | Prove by well-founded induction on path length. The path from a visited node to an unvisited target must cross the visited/frontier boundary. | If direct induction is hard, prove via the contrapositive: if no frontier node reaches target, then target is unreachable from all visited nodes. |

### 6.12 Relationship to the easy direction (B1–B3)

The easy direction (BFS `true` → declarative path) is independent of the
completeness proof but shares infrastructure. Specifically:

- **H1** (`go_eq_true_of_target_head`) is used in both directions.
- **The `serviceEdge` ↔ `lookupService` connection** (Layer 1 structural
  lemmas) is used in both directions.
- **B1** (`serviceHasPathTo_go_true_implies_exists_reachable`) is the
  easy-direction analogue of the core completeness lemma. Its proof by
  induction on `fuel` is structurally simpler because the conclusion follows
  from the BFS's constructive behavior (each `true` return witnesses a path),
  whereas the completeness direction must show that all paths are found.

**Recommendation:** Prove B1–B3 first as a warm-up. The tactic patterns
(BFS unfolding, frontier case-splitting, visited-node handling) directly
transfer to the harder completeness proof, and having the easy direction
proved builds confidence in the BFS unfolding infrastructure.

### 6.13 Integration with existing proof layers

After `bfs_complete_for_nontrivialPath` is proved (sorry eliminated),
the following downstream changes occur:

1. **Layer 4 (`serviceRegisterDependency_preserves_acyclicity`):**
   Already sorry-free. The `sorry` in `bfs_complete_for_nontrivialPath`
   is the only upstream dependency. Once eliminated, the entire Layer 0–4
   stack is fully proved.

2. **TPI-D07-BRIDGE annotation:** Remove the TPI-D07-BRIDGE annotation
   from the theorem and update all documentation references.

3. **Risk register:** Close Risk 1 (fuel adequacy) and Risk 3
   (BFS loop invariant). Update decision log entries D2 and D4.

4. **Test infrastructure:** The tier-0 hygiene check's `sorry` exclusion
   for `TPI-D*` annotations can be tightened — no `sorry` markers should
   remain in the proof surface.

5. **Claim evidence index:** Update TPI-D07 status from "CLOSED (with
   focused sorry)" to "CLOSED (fully proved)".

### 6.14 Estimating the difficulty gradient

| Component | Lines of proof (estimated) | Conceptual difficulty | Tactic difficulty |
|-----------|---------------------------|----------------------|-------------------|
| H1–H5 (Tier 1) | 5–15 | Easy | Easy (simp, List lemmas) |
| H6 (visited transfer) | 15–30 | Medium | Medium (well-founded induction on path) |
| H7 (reachable inversion) | 3–5 | Easy | Easy (cases on serviceReachable) |
| H8–H10 (fuel counting) | 10–20 | Medium | Medium (List.filter.length reasoning) |
| H11 (closure expand) | 20–40 | Medium-Hard | Hard (multiple case splits, membership reasoning) |
| H12 (closure skip) | 10–15 | Medium | Medium |
| Main theorem (§6.5) | 40–80 | Hard | Hard (lexicographic induction, 4 cases) |
| `bfs_complete_for_nontrivialPath` wrapper | 5–10 | Easy | Easy (compose main theorem with serviceReachable_of_nontrivialPath) |
| B1–B3 easy direction | 30–50 | Medium | Medium (fuel induction, 3 cases) |
| **Total** | **~140–270 lines** | | |

The bulk of the difficulty is in the main completeness theorem and the
closure maintenance lemma (H11). Everything else is standard list/membership
reasoning.
