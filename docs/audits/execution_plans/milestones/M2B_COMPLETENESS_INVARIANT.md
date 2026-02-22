# M2B — BFS Completeness Invariant

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Define and prove the loop invariant for the BFS `go` function that
enables the completeness proof. This is the conceptual core of the M2 milestone.

---

## 1. The invariant: what we need to track

The BFS `go` function maintains implicit state through its parameters: `frontier`,
`visited`, and `fuel`. To prove completeness (reachable target → BFS returns true),
we need to formalize what these parameters mean in terms of graph reachability.

### 1.1 Invariant components

The loop invariant for `go frontier visited fuel` consists of four properties:

```
BfsInvariant(st, target, frontier, visited) :=
  (I1) target ∉ visited
       "Target has not yet been found"

  (I2) ∀ v ∈ visited, ∀ dep, serviceEdge st v dep →
         dep ∈ visited ∨ dep ∈ frontier
       "Visited set is closed: every successor of every visited node
        is either visited or in the frontier"

  (I3) ∃ node ∈ frontier, serviceReachable st node target
       "Some frontier node can still reach the target"

  (I4) fuel ≥ freshCount(st, frontier, visited)
       "Enough fuel remains to expand all unvisited reachable nodes"
```

**Informal meaning:** The BFS has partially explored the graph. All expanded nodes
are in `visited`, and their successors have been accounted for (I2). The target hasn't
been found yet (I1), but some frontier node still has a path to it (I3). There's
enough fuel left to continue exploring (I4).

### 1.2 Why each component is needed

| Component | Without it | Used in |
|---|---|---|
| I1 | Can't distinguish "not yet found" from "already found" | Base case of completeness |
| I2 | Can't show new frontier nodes inherit reachability | Expansion step, boundary lemma |
| I3 | No witness that the BFS is making progress toward target | All cases |
| I4 | BFS could run out of fuel before reaching target | Fuel argument |

---

## 2. The closure property (I2) — the key insight

### 2.1 Definition

```lean
/-- The visited set is closed under successor edges: every dependency of
    every visited node is either also visited or present in the frontier. -/
def bfsClosed (st : SystemState) (frontier visited : List ServiceId) : Prop :=
  ∀ v ∈ visited, ∀ dep : ServiceId,
    serviceEdge st v dep → dep ∈ visited ∨ dep ∈ frontier
```

This is the BFS-specific analogue of a "closed set" in graph search theory. It
captures the fact that the BFS has fully processed every visited node — its
successors are known and tracked.

### 2.2 Initial state

```lean
/-- CB2: The closure property holds trivially for an empty visited set. -/
theorem closure_initial (st : SystemState) (frontier : List ServiceId) :
    bfsClosed st frontier [] := by
  intro v hv
  exact absurd hv (List.not_mem_nil v)
```

**Difficulty:** Trivial. The universal quantification over `v ∈ []` is vacuously true.

### 2.3 Preservation under visited skip (CB3)

When the BFS skips a visited node (`node ∈ visited`), the frontier becomes `rest`
and the visited set is unchanged.

```lean
/-- CB3: Skipping a visited node preserves closure.
    The key observation is that `node ∈ visited`, so all of node's successors
    are already accounted for by the existing closure property. Removing node
    from the frontier only makes the closure "tighter" — we need to verify that
    no successor pointed to node specifically (and not to the rest). -/
theorem closure_preserved_by_skip
    (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId)
    (hClosed : bfsClosed st (node :: rest) visited)
    (hVis : node ∈ visited) :
    bfsClosed st rest visited := by
  intro v hv dep hedge
  rcases hClosed v hv dep hedge with hVisited | hFrontier
  · exact Or.inl hVisited
  · -- dep ∈ node :: rest
    rcases List.mem_cons.mp hFrontier with rfl | hRest
    · -- dep = node, and node ∈ visited
      exact Or.inl hVis
    · exact Or.inr hRest
```

**Key insight:** When we remove `node` from the frontier, any dependency that
pointed to `node` in the frontier is fine because `node ∈ visited` — it's already
accounted for by the visited set.

**Difficulty:** Easy. The proof is a straightforward case split on whether `dep = node`
or `dep ∈ rest`.

### 2.4 Preservation under expansion (CB4)

When the BFS expands a new node, the frontier becomes `rest ++ deps.filter (· ∉ visited)`
and the visited set becomes `node :: visited`.

```lean
/-- CB4: Expanding a new node preserves closure.
    After expansion, `node` joins visited, and all of node's unvisited dependencies
    join the frontier. We must show that every successor of every node in the
    new visited set (old visited + node) is in the new visited set or new frontier. -/
theorem closure_preserved_by_expansion
    (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId)
    (hClosed : bfsClosed st (node :: rest) visited)
    (hNotVis : node ∉ visited) :
    let deps := match lookupService st node with
      | some svc => svc.dependencies
      | none => []
    bfsClosed st (rest ++ deps.filter (· ∉ visited)) (node :: visited) := by
  intro deps v hv dep hedge
  rcases List.mem_cons.mp hv with rfl | hOldVis
  · -- v = node: we just expanded this node
    -- dep is a successor of node, so dep ∈ deps(node)
    -- Need: dep ∈ (node :: visited) ∨ dep ∈ (rest ++ deps.filter (· ∉ visited))
    rcases hedge with ⟨svc, hLookup, hMem⟩
    by_cases hDepVis : dep ∈ visited
    · -- dep already visited → dep ∈ node :: visited
      exact Or.inl (List.mem_cons.mpr (Or.inr hDepVis))
    · by_cases hDepNode : dep = node
      · -- dep = node → dep ∈ node :: visited
        exact Or.inl (List.mem_cons.mpr (Or.inl hDepNode))
      · -- dep is fresh: dep ∈ deps.filter (· ∉ visited)
        right
        apply List.mem_append.mpr
        right
        -- Need: dep ∈ deps.filter (· ∉ visited)
        -- deps is determined by lookupService st node
        -- hMem : dep ∈ svc.dependencies, hLookup : lookupService st node = some svc
        -- So dep ∈ deps (after unfolding the match)
        -- And dep ∉ visited (by hDepVis)
        sorry -- requires showing dep ∈ deps from hMem + hLookup, then applying filter
  · -- v ∈ old visited: use old closure property
    rcases hClosed v (List.mem_cons.mpr (Or.inr hOldVis)) dep hedge with hOldV | hOldF
    · -- dep ∈ old visited → dep ∈ node :: visited
      exact Or.inl (List.mem_cons.mpr (Or.inr hOldV))
    · -- dep ∈ node :: rest (old frontier)
      rcases List.mem_cons.mp hOldF with rfl | hRest
      · -- dep = node → dep ∈ node :: visited
        exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
      · -- dep ∈ rest → dep ∈ rest ++ deps.filter ... (new frontier)
        exact Or.inr (List.mem_append.mpr (Or.inl hRest))
```

**Difficulty:** Medium. The proof has many cases but each is straightforward:

1. **New node's successors:** Each dependency of `node` is either already visited
   (→ in new visited), equals `node` itself (→ in new visited), or is fresh
   (→ in the filtered deps appended to the frontier).

2. **Old visited nodes' successors:** By the old closure property, each successor
   was in `old visited ∪ (node :: rest)`. If it was in `old visited`, it's still
   in `new visited`. If it was `node`, `node` is now in `new visited`. If it was
   in `rest`, `rest ⊆ new frontier`.

**The `sorry` in the new-node branch:** The remaining step connects `dep ∈ svc.dependencies`
(from the `serviceEdge` hypothesis) to `dep ∈ deps` (from the `match` expression).
This requires unfolding the `let deps := match ...` binding and using `hLookup` to
resolve the match. The exact tactic depends on how Lean represents the `let`:

```lean
-- Likely resolution:
simp only [hLookup] at *  -- or: rw [hLookup]
exact List.mem_filter.mpr ⟨hMem, hDepVis⟩
```

---

## 3. Target persistence

A crucial property for the completeness proof: if the target is in the frontier, it
remains in the frontier (or is found) across all BFS steps.

### 3.1 The property

```lean
/-- If target is in the frontier, the BFS returns true —
    regardless of the visited set or fuel (as long as fuel > 0). -/
theorem go_true_of_target_in_frontier
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hMem : target ∈ frontier)
    (hFuel : fuel ≥ 1) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

**Proof approach:** By strong induction on `frontier.length`.

- `frontier = []`: contradiction with `target ∈ []`.
- `frontier = node :: rest` with `fuel = f + 1`:
  - If `node = target`: by EQ3, returns true. ✓
  - If `node ≠ target` and `node ∈ visited`:
    - `target ∈ rest` (since `target ∈ node :: rest` and `target ≠ node`)
    - By EQ4: `go (node :: rest) visited (f+1) = go rest visited (f+1)`
    - By IH (rest is shorter): returns true. ✓
  - If `node ≠ target` and `node ∉ visited`:
    - `target ∈ rest` (same reasoning)
    - By EQ5: `go (node :: rest) visited (f+1) = go (rest ++ deps.filter ...) (node :: visited) f`
    - `target ∈ rest`, so `target ∈ rest ++ deps.filter ...`
    - Need `f ≥ 1`. Since `f + 1 ≥ 1` from hFuel... wait, `f` could be 0 if `fuel = 1`.

**Problem:** In the expansion case, fuel decreases from `f + 1` to `f`. If `f = 0`,
the recursive call gets `go ... 0`, which returns false. So we CAN'T prove this
unconditionally — we need fuel ≥ (number of non-visited, non-target nodes before
target in the frontier) + 1.

### 3.2 Refined target-in-frontier lemma

The correct statement accounts for fuel consumption by expansion steps:

```lean
/-- If target is in the frontier and there's enough fuel to process all nodes
    before it, the BFS returns true. -/
theorem go_true_of_target_in_frontier_with_fuel
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hMem : target ∈ frontier)
    -- Fuel must be enough to expand all fresh nodes before target
    (hFuel : fuel ≥ countFreshBefore target frontier visited) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

Where `countFreshBefore` counts nodes before `target` in the frontier that are
not in `visited` (only these consume fuel).

**This is a useful helper but NOT the main completeness theorem.** The main theorem
uses the stronger invariant-based approach.

### 3.3 The simpler alternative: avoid target-persistence entirely

Instead of proving target persistence as a standalone lemma, we can embed the
target-finding argument directly into the main completeness proof (CP1 in
[M2D](./M2D_COMPLETENESS_PROOF.md)). The invariant I3 (some frontier node reaches
target) is maintained across all steps, and when the frontier node IS the target,
EQ3 gives us the result directly.

**Recommendation:** Skip the standalone target-persistence lemma. Use the invariant
approach in CP1, which subsumes it.

---

## 4. The boundary lemma (CB1)

This is the most important structural lemma for the completeness proof.

### 4.1 Statement

```lean
/-- CB1: If a visited node reaches the target, and the target is not visited,
    and the closure property holds, then some frontier node reaches the target.

    Intuition: the path from the visited node to the unvisited target must
    "cross the boundary" between visited and frontier at some point. The
    closure property guarantees this boundary crossing lands in the frontier. -/
theorem reachable_frontier_boundary
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId)
    (v : ServiceId)
    (hReach : serviceReachable st v target)
    (hVis : v ∈ visited)
    (hTargetNotVis : target ∉ visited)
    (hClosed : bfsClosed st frontier visited) :
    ∃ f ∈ frontier, serviceReachable st f target := by
  sorry -- proof below
```

### 4.2 Proof

By induction on `serviceReachable st v target`:

**Case `refl` (v = target):**
`v ∈ visited` and `target ∉ visited` with `v = target` → contradiction. ✓

**Case `step` (serviceEdge st v mid, serviceReachable st mid target):**
By the closure property (hClosed), since `v ∈ visited` and `serviceEdge st v mid`:
- Either `mid ∈ visited`: recurse on `serviceReachable st mid target` with
  `mid ∈ visited`. The inductive hypothesis gives the result.
- Or `mid ∈ frontier`: witness is `mid` with path `serviceReachable st mid target`. ✓

```lean
-- Proof sketch in Lean:
theorem reachable_frontier_boundary
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId)
    (v : ServiceId)
    (hReach : serviceReachable st v target)
    (hVis : v ∈ visited)
    (hTargetNotVis : target ∉ visited)
    (hClosed : bfsClosed st frontier visited) :
    ∃ f ∈ frontier, serviceReachable st f target := by
  induction hReach with
  | refl =>
    -- v = target, but v ∈ visited and target ∉ visited → contradiction
    exact absurd hVis (by rwa [show v = target from rfl] at hTargetNotVis ▸ hTargetNotVis)
    -- Simpler: exact absurd hVis hTargetNotVis (after noting v = target)
  | step hedge hreach ih =>
    -- hedge : serviceEdge st v mid
    -- hreach : serviceReachable st mid target
    rcases hClosed v hVis mid hedge with hMidVis | hMidFrontier
    · -- mid ∈ visited: use IH
      exact ih hMidVis
    · -- mid ∈ frontier: witness found
      exact ⟨mid, hMidFrontier, hreach⟩
```

**Difficulty:** Medium. The induction is clean but requires careful handling of the
implicit variables in `serviceReachable`.

**Critical subtlety:** The induction on `serviceReachable` gives us an IH that is
parameterized by the intermediate node. In the `step` case, the IH applies to `mid`
(not `v`), which is exactly what we need — IF `mid ∈ visited`. If `mid ∈ frontier`,
we don't need the IH at all.

### 4.3 Why this lemma is crucial

The boundary lemma bridges the gap between "a visited node can reach target" and
"a frontier node can reach target." In the completeness proof, when we expand a
node and add it to visited, we may temporarily lose our frontier witness (if the
witness was the node being expanded). The boundary lemma recovers a new frontier
witness from the closure property.

**Usage pattern in CP1:**
1. Expanding node `w` where `w` was our frontier witness reaching target
2. After expansion, `w` moves to visited
3. `serviceReachable st w target` still holds
4. By CB1: since `w ∈ new_visited` and closure holds → ∃ new frontier witness

---

## 5. The fresh-count measure

### 5.1 Conceptual definition

```
freshCount(st, frontier, visited) :=
  |{x : ServiceId | serviceReachable st f x for some f ∈ frontier, x ∉ visited}|
```

This counts distinct nodes reachable from the frontier that haven't been visited yet.
It's the "work remaining" for the BFS.

### 5.2 Formalization challenge

Since `ServiceId` wraps `Nat` and `services` is a total function `ServiceId → Option`,
the set of reachable nodes may not be trivially `Finset`-typed. We have two options:

**Option A: Existential bound.** Instead of computing `freshCount` directly, state
the fuel adequacy as:

```lean
∃ bound : Nat, bound ≤ fuel ∧
  ∀ (sids : List ServiceId), sids.Nodup →
    (∀ s ∈ sids, s ∉ visited ∧ (∃ f ∈ frontier, serviceReachable st f s)) →
    sids.length ≤ bound
```

**Option B: Precondition.** Push the finiteness into a hypothesis (see
[M2C: Fuel Adequacy](./M2C_FUEL_ADEQUACY.md)).

**Option C: Nat-indexed counting.** Observe that the BFS can only visit nodes
discoverable through `svc.dependencies` lists. Since each list is finite and the
BFS tracks visited nodes, the total distinct visitable nodes form a finite set
(the transitive closure of the dependency relation from `frontier`). However,
formalizing this requires showing the transitive closure is finite, which circles
back to the same problem.

**Recommendation:** Use Option B. The fuel adequacy precondition cleanly separates
the graph-finiteness concern from the BFS correctness argument.

### 5.3 Monotonicity property

```lean
/-- FA2: Expanding a fresh node strictly decreases the fresh count.
    After expansion, the fresh count under (new_frontier, new_visited) is
    strictly less than under (old_frontier, old_visited), because the
    expanded node transitions from "fresh" to "visited." -/
theorem freshCount_decreases_on_expansion
    -- This is stated informally since freshCount may not be a computable function.
    -- The actual proof uses the fuel adequacy precondition.
```

In practice, this property is used implicitly: if fuel was adequate before expansion
(fuel ≥ freshCount), and expansion consumes one fuel unit while reducing freshCount
by at least one, then fuel is still adequate after expansion (fuel - 1 ≥ freshCount - 1).

---

## 6. Invariant preservation summary

| BFS step | I1 (target ∉ visited) | I2 (closure) | I3 (frontier witness) | I4 (fuel adequate) |
|---|---|---|---|---|
| **Skip (visited)** | Preserved (visited unchanged) | By CB3 | See §6.1 | Preserved (fuel unchanged, freshCount unchanged) |
| **Expand (new node)** | Preserved (node ≠ target) | By CB4 | See §6.2 | By FA2 (fuel-1 ≥ freshCount-1) |

### 6.1 Frontier witness under skip

When we skip node `v` (visited), the frontier becomes `rest`. Our witness `w` was
in `node :: rest` with `serviceReachable st w target`.

- If `w ≠ node`: `w ∈ rest`, witness preserved. ✓
- If `w = node`: `w ∈ visited`, so by CB1 (boundary lemma) with the old closure
  property, there exists a new witness in `node :: rest`. But we need a witness in
  `rest`, not in `node :: rest`... The boundary lemma gives us `∃ f ∈ (node :: rest)`.
  If `f = node`, that's still in visited, not helpful. We'd need to iterate.

**Resolution:** When `w = node` and `node ∈ visited`, apply CB1 to get
`∃ f ∈ frontier, serviceReachable st f target`. Since we're analyzing the state
BEFORE the skip, the frontier is `node :: rest`. CB1 may return `node` itself.
But `node ∈ visited`, and the path from `node` to `target` has at least one edge
(since `target ∉ visited`). By the closure property, the first hop from `node`
lands in `visited ∪ frontier`. Continue this argument...

Actually, the cleaner approach: **we don't need `w` to be specifically in the frontier.
We need `∃ f ∈ frontier, serviceReachable st f target`.** In the skip case:

- Old frontier: `node :: rest`. Old witness: `∃ f ∈ (node :: rest), serviceReachable st f target`.
- If some `f ∈ rest` witnesses: new frontier `rest` has a witness. ✓
- If only `f = node` witnesses: `node ∈ visited`, and `serviceReachable st node target`.
  By CB1 on the current state: `∃ f ∈ (node :: rest), serviceReachable st f target`.
  But we JUST said only node witnesses. So CB1 would need to find a non-node witness.

  Actually, CB1 works by induction on the reachable path. Since `node ∈ visited` and
  `serviceReachable st node target` has at least one step (target ∉ visited), the
  first edge from `node` leads to some `mid`. If `mid ∈ visited`, continue inducting.
  If `mid ∈ frontier = node :: rest`, and `mid ≠ node`, then `mid ∈ rest`. ✓
  If `mid = node`, that means `serviceEdge st node node` and
  `serviceReachable st node target` — this could loop.

**The fix:** The induction in CB1 is on the `serviceReachable` inductive type, which
is well-founded (finite). So the loop terminates. At each step, either we find a
frontier node that isn't `node`, or we descend deeper into the path. Since the path
is finite, we MUST eventually leave the visited set through a non-node frontier entry.

Wait, but what if ALL intermediate nodes on the path are `node`? That would mean
the path is `node → node → node → ... → target`, which means `serviceEdge st node node`
repeatedly. This IS possible in principle (a self-loop in the dependency graph). But
the path eventually reaches `target ≠ node` (since `target ∉ visited` and `node ∈ visited`),
so at some point an edge `node → mid` with `mid ≠ node` must exist on the path. By
closure, `mid ∈ visited ∨ mid ∈ frontier`. If `mid ∈ frontier` and `mid ≠ node`,
then `mid ∈ rest`. ✓ If `mid ∈ visited`, the induction on `serviceReachable` continues
with `mid`, which has a shorter remaining path to `target`.

**Conclusion:** CB1 handles this correctly because the induction is on the finite
`serviceReachable` structure, not on the graph (which may have cycles). The skip
case for the witness is correctly handled by CB1.

### 6.2 Frontier witness under expansion

When we expand node `w` (the witness reaching target), `w` moves to visited and
its dependencies join the frontier.

- `w` is now in `new_visited = w :: visited`
- `serviceReachable st w target` still holds
- `target ∉ new_visited` (by I1 and `w ≠ target` from the expansion condition)
- Closure holds for new state (by CB4)
- By CB1: `∃ f ∈ new_frontier, serviceReachable st f target` ✓

**This works cleanly.** The boundary lemma does all the heavy lifting.

When the witness `w` is NOT the expanded node (i.e., `w ∈ rest`), it's even simpler:
`w ∈ rest ⊆ new_frontier`, so the witness persists directly.

---

## 7. Putting it together

The invariant components (I1–I4) and the preservation lemmas (CB1–CB4) combine to
give the main completeness theorem in [M2D](./M2D_COMPLETENESS_PROOF.md). The structure is:

1. **Establish initial invariant:** `go [src] [] fuel` with I1 (target ≠ src initially
   handled by hNe), I2 (CB2), I3 (src reaches target by hypothesis), I4 (fuel adequate).

2. **Induction step:** At each BFS step, show the invariant is preserved (CB3 or CB4,
   plus frontier witness maintenance via CB1).

3. **Termination:** By I4, fuel is adequate. The BFS terminates either by finding
   the target (→ returns true) or by exhausting the frontier (→ all reachable nodes
   visited, but target is reachable and not visited → contradiction with I2+I3).
