# M2B — BFS Completeness Invariant

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Define and prove the loop invariant for the BFS `go` function that
enables the completeness proof. This is the conceptual core of the M2 milestone —
every other component serves this invariant.

---

## 1. The invariant: what we need to track

The BFS `go` function maintains implicit state through its parameters: `frontier`,
`visited`, and `fuel`. To prove completeness (reachable target → BFS returns true),
we must formalize what these parameters mean in terms of graph reachability.

### 1.1 Invariant components

The loop invariant for `go frontier visited fuel` consists of four properties:

```
BfsInvariant(st, target, frontier, visited, fuel) :=
  (I1) target ∉ visited
       "Target has not yet been found"

  (I2) ∀ v ∈ visited, ∀ dep, serviceEdge st v dep →
         dep ∈ visited ∨ dep ∈ frontier
       "Visited set is closed: every successor of every visited node
        is either visited or in the frontier"

  (I3) ∃ node ∈ frontier, serviceReachable st node target
       "Some frontier node can still reach the target"

  (I4) fuel ≥ |unvisited registered services|
       "Enough fuel remains to expand all unvisited reachable nodes"
```

### 1.2 Why each component is needed

| Component | Without it | Used in |
|---|---|---|
| I1 | Can't distinguish "not yet found" from "already found" — fuel = 0 base case breaks | Base case of completeness, boundary lemma |
| I2 | Can't show new frontier nodes inherit reachability — witness transfer breaks | Expansion step, boundary lemma (CB1) |
| I3 | No witness that BFS is making progress toward target | All cases of induction |
| I4 | BFS could exhaust fuel before reaching target | Fuel argument in expansion case |

---

## 2. The closure property (I2) — the key insight

### 2.1 Named definition

```lean
/-- The visited set is closed under successor edges: every dependency of
    every visited node is either also visited or present in the frontier. -/
def bfsClosed (st : SystemState) (frontier visited : List ServiceId) : Prop :=
  ∀ v ∈ visited, ∀ dep : ServiceId,
    serviceEdge st v dep → dep ∈ visited ∨ dep ∈ frontier
```

This is the BFS-specific analogue of a "closed set" in graph search theory. It
captures the fact that the BFS has fully processed every visited node — all
successors are known and tracked.

**Why a named definition:** Downstream lemmas (CB3, CB4, CP1) all take `bfsClosed`
as a hypothesis and produce `bfsClosed` as a conclusion. A named definition avoids
repeating the 3-line quantified proposition everywhere.

### 2.2 Initial state — CB2

```lean
/-- CB2: The closure property holds trivially for an empty visited set. -/
theorem closure_initial (st : SystemState) (frontier : List ServiceId) :
    bfsClosed st frontier [] := by
  intro v hv
  exact absurd hv (List.not_mem_nil v)
```

**Difficulty:** Trivial. The universal quantification over `v ∈ []` is vacuously true.

### 2.3 Preservation under visited skip — CB3

When the BFS skips a visited node (`node ∈ visited`), the frontier becomes `rest`
and the visited set is unchanged.

```lean
/-- CB3: Skipping a visited node preserves closure.
    node ∈ visited means its successors are already accounted for. Removing node
    from the frontier only matters if some visited node's successor was specifically
    node — but node ∈ visited covers that case. -/
theorem closure_preserved_by_skip
    (st : SystemState)
    (node : ServiceId) (rest visited : List ServiceId)
    (hClosed : bfsClosed st (node :: rest) visited)
    (hVis : node ∈ visited) :
    bfsClosed st rest visited := by
  intro v hv dep hedge
  rcases hClosed v hv dep hedge with hVisited | hFrontier
  · exact Or.inl hVisited
  · rcases List.mem_cons.mp hFrontier with rfl | hRest
    · exact Or.inl hVis       -- dep = node, and node ∈ visited
    · exact Or.inr hRest      -- dep ∈ rest
```

**Key insight:** When we remove `node` from the frontier, any dependency that
pointed to `node` is fine because `node ∈ visited`.

**Difficulty:** Easy.

### 2.4 Preservation under expansion — CB4

When the BFS expands a new node, the frontier becomes `rest ++ deps.filter (· ∉ visited)`
and the visited set becomes `node :: visited`.

```lean
/-- CB4: Expanding a new node preserves closure.
    After expansion, node joins visited and all of node's unvisited dependencies
    join the frontier. -/
theorem closure_preserved_by_expansion
    (st : SystemState)
    (node : ServiceId) (rest visited : List ServiceId)
    (hClosed : bfsClosed st (node :: rest) visited)
    (hNotVis : node ∉ visited) :
    let deps := lookupDeps st node
    bfsClosed st (rest ++ deps.filter (· ∉ visited)) (node :: visited) := by
  intro deps v hv dep hedge
  rcases List.mem_cons.mp hv with rfl | hOldVis
  · -- v = node: just expanded this node
    -- dep is a successor of node, so dep ∈ lookupDeps st node
    -- (by serviceEdge_iff_lookupDeps)
    by_cases hDepVis : dep ∈ visited
    · exact Or.inl (List.mem_cons.mpr (Or.inr hDepVis))
    · by_cases hDepNode : dep = node
      · exact Or.inl (List.mem_cons.mpr (Or.inl hDepNode))
      · -- dep is fresh → dep ∈ deps.filter (· ∉ visited) ⊆ new frontier
        right; apply List.mem_append.mpr; right
        exact List.mem_filter.mpr ⟨serviceEdge_iff_lookupDeps.mp hedge, hDepVis⟩
  · -- v ∈ old visited: use old closure property
    rcases hClosed v (List.mem_cons.mpr (Or.inr hOldVis)) dep hedge with hOldV | hOldF
    · exact Or.inl (List.mem_cons.mpr (Or.inr hOldV))
    · rcases List.mem_cons.mp hOldF with rfl | hRest
      · exact Or.inl (List.mem_cons.mpr (Or.inl rfl)) -- dep = node → new visited
      · exact Or.inr (List.mem_append.mpr (Or.inl hRest)) -- dep ∈ rest
```

**Difficulty:** Medium. Many cases but each is straightforward:

1. **New node's successors:** Each dependency of `node` is either already visited
   (→ new visited), equals `node` itself (→ new visited), or is fresh (→ filtered
   deps appended to frontier).

2. **Old visited nodes' successors:** By old closure, each successor was in
   `old visited ∪ (node :: rest)`. If in `old visited`, still in new visited.
   If `node`, now in new visited. If in `rest`, still in new frontier.

---

## 3. The boundary lemma (CB1) — the structural heart

This is the most important structural lemma for the completeness proof. It
bridges "a visited node reaches target" to "a frontier node reaches target".

### 3.1 Statement

```lean
/-- CB1: If a visited node reaches the target, the target is not visited,
    and closure holds, then some frontier node also reaches the target.

    Intuition: the path from the visited node to the unvisited target must
    cross the boundary between visited and frontier at some point. The
    closure property guarantees this crossing lands in the frontier. -/
theorem reachable_frontier_boundary
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId)
    (v : ServiceId)
    (hReach : serviceReachable st v target)
    (hVis : v ∈ visited)
    (hTargetNotVis : target ∉ visited)
    (hClosed : bfsClosed st frontier visited) :
    ∃ f ∈ frontier, serviceReachable st f target
```

### 3.2 Proof

By induction on `serviceReachable st v target`:

**Case `refl` (v = target):**
`v ∈ visited` and `target ∉ visited` with `v = target` → contradiction. ✓

**Case `step` (serviceEdge st v mid, serviceReachable st mid target):**
By closure (`hClosed`), since `v ∈ visited` and `serviceEdge st v mid`:
- Either `mid ∈ visited`: apply the inductive hypothesis on `mid`. The induction
  is well-founded because the `serviceReachable` proof structure is finite.
- Or `mid ∈ frontier`: witness is `⟨mid, hMidFrontier, hReachMidTarget⟩`. ✓

```lean
theorem reachable_frontier_boundary ... := by
  induction hReach with
  | refl => exact absurd hVis hTargetNotVis
  | step hedge hreach ih =>
    rcases hClosed v hVis _ hedge with hMidVis | hMidFrontier
    · exact ih hMidVis                          -- mid ∈ visited: recurse
    · exact ⟨_, hMidFrontier, hreach⟩           -- mid ∈ frontier: found
```

**Critical subtlety:** The induction is on the `serviceReachable` inductive type
— we're inducting on the *proof structure*, not on the visited set or graph. The
path in the proof has finite length, so the chain through visited nodes terminates.
This is what makes the argument work even if the dependency graph has cycles.

### 3.3 Why this lemma is crucial

The boundary lemma is used in the completeness proof (CP1, M2D) in two places:

1. **Skip case:** When the BFS skips a visited node `w` that was our frontier
   witness reaching target, CB1 recovers a new witness in `rest` (the reduced
   frontier after removing `w`).

2. **Expansion case:** When the BFS expands node `w` (our witness), `w` moves to
   visited. CB1 applied to the post-expansion state recovers a witness in the
   new frontier.

---

## 4. Invariant preservation summary

| BFS step | I1 (target ∉ visited) | I2 (closure) | I3 (frontier witness) | I4 (fuel adequate) |
|---|---|---|---|---|
| **Skip (visited)** | Preserved (visited unchanged) | By CB3 | By CB1 if witness was the skipped node; direct if witness ∈ rest | Preserved (fuel recycled, freshCount unchanged) |
| **Expand (new node)** | Preserved (node ≠ target) | By CB4 | By CB1 if witness was the expanded node; `List.mem_append` left if witness ∈ rest | By fuel arithmetic: fuel-1 ≥ freshCount-1 (see [M2C](./M2C_FUEL_ADEQUACY.md)) |

### 4.1 Frontier witness under skip (detailed)

When we skip node `v` (visited), frontier becomes `rest`. Our witness `w` was
in `node :: rest` with `serviceReachable st w target`.

- If `w ∈ rest` (i.e., `w ≠ v`): witness persists in `rest`. ✓
- If `w = v`: `w ∈ visited`, so apply CB1 with the *pre-skip* closure (which
  covers `node :: rest` as frontier). CB1 gives `∃ f ∈ (node :: rest)`. If
  `f ∈ rest`, done. If `f = v`, CB1's induction on `serviceReachable` ensures
  the chain through visited nodes eventually exits to a frontier node ≠ `v`
  (because `target ∉ visited` forces the path to cross the boundary).

**Actually**, a cleaner approach: apply CB1 using the *post-skip* closure (CB3
gives closure for `rest` over same `visited`). Since `w ∈ visited` and
`serviceReachable st w target`, CB1 with the post-skip closure gives
`∃ f ∈ rest, serviceReachable st f target`. ✓

### 4.2 Frontier witness under expansion (detailed)

When we expand `w` (our witness reaching target), `w` moves to
`node :: visited`. After expansion:
- `w ∈ node :: visited` (new visited set)
- `serviceReachable st w target` still holds
- `target ∉ node :: visited` (since `w ≠ target` and `target ∉ visited`)
- CB4 gives closure for the new state
- By CB1: `∃ f ∈ new_frontier, serviceReachable st f target`. ✓

When the witness `w` is NOT the expanded node (i.e., `w ∈ rest`): `w ∈ rest`
and `rest ⊆ new_frontier` (by `List.mem_append` left), so the witness persists
directly.

---

## 5. Relationship to other sub-milestones

- **M2A (equational theory):** CB3 and CB4 proofs use EQ4 and EQ5 to unfold `go`
  and identify which branch applies.
- **M2C (fuel adequacy):** I4 preservation in the expansion case requires the
  fuel arithmetic from M2C.
- **M2D (completeness proof):** CP1 directly relies on CB1-CB4 and I1-I4 as its
  invariant.

---

## 6. Implementation notes

### 6.1 Placement

All definitions and lemmas in this document go in
`SeLe4n/Kernel/Service/Invariant.lean`, after the `lookupDeps` bridge (M2A)
and before the equational lemmas:

```
-- M2A: lookupDeps + bridge
-- NEW: bfsClosed definition
-- NEW: CB2 (closure_initial)
-- M2A: EQ1-EQ5
-- NEW: CB3 (closure_preserved_by_skip)
-- NEW: CB4 (closure_preserved_by_expansion)
-- NEW: CB1 (reachable_frontier_boundary)
```

### 6.2 Implementation order

1. `bfsClosed` definition — trivial, no proof.
2. CB2 (`closure_initial`) — vacuous truth.
3. CB3 (`closure_preserved_by_skip`) — easy case split.
4. CB4 (`closure_preserved_by_expansion`) — medium, requires `serviceEdge_iff_lookupDeps`.
5. CB1 (`reachable_frontier_boundary`) — medium, induction on `serviceReachable`.

CB4 depends on the `serviceEdge_iff_lookupDeps` bridge from M2A. CB1 depends on
`bfsClosed` but not on CB3 or CB4 (it takes `bfsClosed` as a hypothesis, regardless
of how it was established).
