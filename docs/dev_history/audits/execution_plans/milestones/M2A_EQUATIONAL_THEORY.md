# M2A — BFS Equational Theory

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Establish equational lemmas that unfold `serviceHasPathTo.go` for each
branch of the function definition. These lemmas serve as the foundation for all BFS
reasoning in M2B–M2D and encapsulate access patterns so downstream proofs never need
to unfold `go` directly.

---

## 1. The access problem

The `go` function is defined with a `where` clause inside `serviceHasPathTo`:

```lean
def serviceHasPathTo ... : Bool :=
  go [src] [] fuel
where
  go (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false
  | fuel + 1 => match frontier with
    | [] => false
    | node :: rest =>
        if node = target then true
        else if node ∈ visited then go rest visited (fuel + 1)
        else
          let deps := match lookupService st node with
            | some svc => svc.dependencies
            | none => []
          let newFrontier := rest ++ deps.filter (· ∉ visited)
          go newFrontier (node :: visited) fuel
```

Lean 4 elaborates this as `serviceHasPathTo.go`. Accessing the function body in
proofs requires specific tactics. The equational lemmas here encapsulate these
patterns once so all downstream proofs use clean rewrite rules.

### 1.1 Tactic patterns for accessing `go`

Try these approaches in order on EQ1. The first one that works should be used
consistently across all subsequent lemmas:

```lean
-- Approach 1: simp with function name (preferred)
simp only [serviceHasPathTo.go]

-- Approach 2: Generated equational lemma
rw [serviceHasPathTo.go.eq_def]

-- Approach 3: Unfold
unfold serviceHasPathTo.go

-- Approach 4: Delta reduction (last resort — may produce huge terms)
delta serviceHasPathTo.go
```

---

## 2. Prerequisite helper: `lookupDeps`

The BFS computes dependency lists inline via a `match` on `lookupService`. A named
helper simplifies proof reasoning by avoiding repeated pattern-match unfolding.

### 2.1 Definition

```lean
/-- Extract the dependency list for a service, returning [] if not found.
    Mirrors the inline computation in serviceHasPathTo.go. -/
def lookupDeps (st : SystemState) (node : ServiceId) : List ServiceId :=
  match lookupService st node with
  | some svc => svc.dependencies
  | none => []
```

### 2.2 Bridge lemma

```lean
/-- serviceEdge is equivalent to membership in lookupDeps.
    Bridges the Prop-level edge relation to the Bool-level BFS. -/
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

**Why this matters**: Every completeness proof case needs to connect
`serviceEdge st node w` (from the declarative path) to `w ∈ deps` (in the BFS
expansion). Without this bridge, the connection requires re-deriving the pattern
match each time.

---

## 3. Equational lemmas

### EQ1: `go_zero_eq_false`

```lean
/-- Fuel exhaustion: go always returns false when fuel is zero. -/
theorem go_zero_eq_false
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) :
    serviceHasPathTo.go st target frontier visited 0 = false := by
  simp [serviceHasPathTo.go]
```

**Why this matters:** Base case for all fuel-induction proofs. When fuel runs
out, the BFS conservatively reports no path.

**Difficulty:** Trivial.

---

### EQ2: `go_nil_eq_false`

```lean
/-- Empty frontier: go returns false when no nodes remain to explore. -/
theorem go_nil_eq_false
    (st : SystemState) (target : ServiceId)
    (visited : List ServiceId) (fuel : Nat) :
    serviceHasPathTo.go st target [] visited (fuel + 1) = false := by
  simp [serviceHasPathTo.go]
```

**Why this matters:** Second base case. An empty frontier contradicts the
invariant I3 (some frontier node reaches target), closing the vacuous branch
in the completeness proof.

**Difficulty:** Trivial.

---

### EQ3: `go_cons_target`

```lean
/-- Target found: go returns true when the head of the frontier is the target. -/
theorem go_cons_target
    (st : SystemState) (target : ServiceId)
    (rest visited : List ServiceId) (fuel : Nat) :
    serviceHasPathTo.go st target (target :: rest) visited (fuel + 1) = true := by
  simp [serviceHasPathTo.go]
```

**Important property:** The BFS checks `if node = target` BEFORE checking visited
status. This means:

1. If target is anywhere in the frontier, it will eventually be found (once
   preceding nodes are processed).
2. The target check is independent of visited — even a previously visited node
   triggers success if it equals the target.

**Variant for hypothesis form** (if Lean doesn't reduce `if node = target`
when `node` is definitionally `target`):

```lean
theorem go_cons_target'
    (st : SystemState) (target node : ServiceId) (rest visited : List ServiceId)
    (fuel : Nat) (hEq : node = target) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) = true := by
  subst hEq; simp [serviceHasPathTo.go]
```

**Difficulty:** Trivial. May need `decide` or `rfl` for the `if` reduction.

---

### EQ4: `go_cons_visited_skip`

```lean
/-- Visited skip: when the head node is not the target and is already visited,
    go skips it without consuming fuel. -/
theorem go_cons_visited_skip
    (st : SystemState) (target node : ServiceId)
    (rest visited : List ServiceId) (fuel : Nat)
    (hNeq : node ≠ target) (hVis : node ∈ visited) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) =
    serviceHasPathTo.go st target rest visited (fuel + 1) := by
  simp [serviceHasPathTo.go, hNeq, hVis]
```

**Key behavioral property:** This is the fuel-recycling branch:
- Fuel is preserved: the recursive call uses `fuel + 1`, the same as the input.
- Frontier shrinks: `rest` is strictly shorter than `node :: rest`.
- Visited unchanged.

This branch is what makes simple Nat induction on fuel impossible and motivates
the lexicographic induction measure in M2D.

**Difficulty:** Easy.

---

### EQ5: `go_cons_expand`

```lean
/-- Node expansion: when the head node is not the target and not visited,
    go expands it by adding its unvisited dependencies to the frontier. -/
theorem go_cons_expand
    (st : SystemState) (target node : ServiceId)
    (rest visited : List ServiceId) (fuel : Nat)
    (hNeq : node ≠ target) (hNotVis : node ∉ visited) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) =
    serviceHasPathTo.go st target
      (rest ++ (lookupDeps st node).filter (· ∉ visited))
      (node :: visited)
      fuel := by
  simp [serviceHasPathTo.go, hNeq, hNotVis, lookupDeps]
```

**Key behavioral properties:**
1. Fuel consumed: `fuel + 1` → `fuel` (strictly decreases).
2. Frontier evolves: `node :: rest` → `rest ++ deps.filter (· ∉ visited)`.
3. Visited grows: `visited` → `node :: visited`.
4. Dependencies source: `lookupService st node` determines the adjacency list.
   If the node has no service entry, dependencies are `[]`.

**Subtlety:** The `let deps := match ...` binding in `go` may or may not be
inlined by Lean. If `simp` doesn't fully reduce, try:

```lean
unfold serviceHasPathTo.go
simp only [hNeq, hNotVis, ite_false, Bool.false_eq_true]
```

**Difficulty:** Easy, but may need tactic adjustment.

---

## 4. Optional: fuel monotonicity

```lean
/-- More fuel preserves true results: if go returns true with fuel f,
    it also returns true with fuel f + k. -/
theorem go_fuel_mono
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel k : Nat)
    (hTrue : serviceHasPathTo.go st target frontier visited fuel = true) :
    serviceHasPathTo.go st target frontier visited (fuel + k) = true
```

**Proof strategy:** Induction on `fuel` with `frontier`, `visited`, `k`
generalized. Each case applies the IH with `fuel' ≤ fuel`. The visited-skip
case preserves fuel, and the expansion case decreases fuel by 1.

**Status:** Useful but NOT required for the main completeness proof. Defer to
post-M2 if implementation is not immediate.

**Difficulty:** Medium.

---

## 5. Implementation order

1. **`lookupDeps` + `serviceEdge_iff_lookupDeps`** — validates the deps bridge.
2. **EQ1** — validates the tactic approach for accessing `go`.
3. **EQ2** — confirms the pattern works for different cases.
4. **EQ3** — validates `if` reduction for `DecidableEq ServiceId`.
5. **EQ4** — first lemma with hypotheses; tests `simp` with conditional rewriting.
6. **EQ5** — most complex; may need tactic adjustment for the `lookupDeps` match.

**If `simp [serviceHasPathTo.go, ...]` fails** on any lemma, fall back to:
```lean
unfold serviceHasPathTo.go
split  -- handles the Nat pattern match
· <zero case>
· split  -- handles the List pattern match
  · <nil case>
  · simp only [...]  -- handles the if chain
```

## 6. Placement

All equational lemmas should be placed in `SeLe4n/Kernel/Service/Invariant.lean`,
immediately before the `bfs_complete_for_nontrivialPath` theorem (currently at
line 526), after the Layer 1 frame lemmas:

```
Line 508: end of Layer 1 frame lemmas
-- NEW: lookupDeps + serviceEdge_iff_lookupDeps
-- NEW: Layer 2A equational lemmas (EQ1–EQ5)
Line 526: theorem bfs_complete_for_nontrivialPath
```
