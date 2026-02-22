# M2A — BFS Equational Theory

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Establish equational lemmas that unfold `serviceHasPathTo.go` for each
branch of the function definition. These lemmas serve as the foundation for all BFS
reasoning in Layers 2B–2E.

---

## 1. The access problem

The `go` function is defined with a `where` clause inside `serviceHasPathTo`:

```lean
def serviceHasPathTo ... : Bool :=
  go [src] [] fuel
where
  go (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false
  | fuel + 1 => match frontier with ...
```

Lean 4 elaborates `where`-defined functions as `serviceHasPathTo.go`. Accessing
this in proofs requires specific tactics. The equational lemmas in this document
encapsulate these access patterns so that downstream proofs (2B–2E) never need to
unfold `go` directly.

### 1.1 Tactic patterns for accessing `go`

Try these approaches in order. The first one that works for the project's Lean version
should be used consistently:

```lean
-- Approach 1: Direct simp with equational lemma (preferred)
simp only [serviceHasPathTo.go]

-- Approach 2: Using the generated .eq_def
rw [serviceHasPathTo.go.eq_def]

-- Approach 3: Unfold
unfold serviceHasPathTo.go

-- Approach 4: Delta reduction (last resort)
delta serviceHasPathTo.go
```

**Implementation note:** Before writing any proofs, verify which approach works by
attempting a simple lemma (EQ1). Lock in that approach for all subsequent lemmas.

---

## 2. Equational lemmas

### EQ1: `go_zero_eq_false`

```lean
/-- Fuel exhaustion: `go` always returns `false` when fuel is zero. -/
theorem go_zero_eq_false
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) :
    serviceHasPathTo.go st target frontier visited 0 = false := by
  simp [serviceHasPathTo.go]
  -- Alternative: rfl (if Lean reduces the pattern match directly)
```

**Why this matters:** This is the base case for all fuel-induction proofs. When fuel
runs out, the BFS conservatively reports no path. Every induction on `fuel` will
discharge the zero case using this lemma.

**Expected difficulty:** Trivial. If `simp` doesn't work, try `rfl` or `unfold`.

---

### EQ2: `go_nil_eq_false`

```lean
/-- Empty frontier: `go` returns `false` when no nodes remain to explore. -/
theorem go_nil_eq_false
    (st : SystemState) (target : ServiceId)
    (visited : List ServiceId) (fuel : Nat) :
    serviceHasPathTo.go st target [] visited (fuel + 1) = false := by
  simp [serviceHasPathTo.go]
```

**Why this matters:** This is the second base case. When the BFS has explored all
reachable nodes from the initial frontier without finding the target, the frontier
empties and the search terminates with `false`.

**Expected difficulty:** Trivial.

---

### EQ3: `go_cons_target`

```lean
/-- Target found: `go` returns `true` when the head of the frontier is the target. -/
theorem go_cons_target
    (st : SystemState) (target : ServiceId)
    (rest visited : List ServiceId) (fuel : Nat) :
    serviceHasPathTo.go st target (target :: rest) visited (fuel + 1) = true := by
  simp [serviceHasPathTo.go]
```

**Why this matters:** This is the success case. The BFS checks `if node = target`
BEFORE checking visited status. This means:

1. If target is anywhere in the frontier, it will eventually be found (once preceding
   nodes are processed).
2. The target check is independent of visited — even a previously visited node
   triggers success if it equals the target.

Property (1) is the foundation of the "target persistence" argument used in the
completeness proof (see [M2B §3](./M2B_COMPLETENESS_INVARIANT.md#3-target-persistence)).

**Expected difficulty:** Trivial. May need `decide` or `rfl` for the `if` reduction.

**Possible variant needed:**
```lean
-- If Lean doesn't reduce `if node = target` when node is definitionally target,
-- we may need the hypothesis version:
theorem go_cons_target'
    (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId) (fuel : Nat)
    (hEq : node = target) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) = true := by
  subst hEq
  simp [serviceHasPathTo.go]
```

---

### EQ4: `go_cons_visited_skip`

```lean
/-- Visited skip: when the head node is not the target and is already visited,
    `go` skips it without consuming fuel. -/
theorem go_cons_visited_skip
    (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId) (fuel : Nat)
    (hNeq : node ≠ target)
    (hVis : node ∈ visited) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) =
    serviceHasPathTo.go st target rest visited (fuel + 1) := by
  simp [serviceHasPathTo.go, hNeq, hVis]
```

**Why this matters:** This lemma captures the fuel-recycling behavior. When a visited
node is encountered:

- **Fuel is preserved:** The recursive call uses `fuel + 1`, the same as the input.
- **Frontier shrinks:** `rest` is strictly shorter than `node :: rest`.
- **Visited unchanged:** The visited set doesn't grow.

This is the branch that complicates the termination measure — fuel doesn't decrease,
but frontier length does. The lexicographic measure `(fuel, frontier.length)` handles
this: same first component, strictly smaller second component.

**For the completeness invariant:** The skip branch preserves all invariant properties
(closure, reachability witness) because no state changes except removing one node
from the frontier — and that node's successors are already accounted for (it's in
visited, so by the closure property, its successors are in visited ∪ frontier).

**Expected difficulty:** Easy. The `simp` should handle the `if` chain.

---

### EQ5: `go_cons_expand`

```lean
/-- Node expansion: when the head node is not the target and not visited,
    `go` expands it by adding its unvisited dependencies to the frontier. -/
theorem go_cons_expand
    (st : SystemState) (target : ServiceId)
    (node : ServiceId) (rest visited : List ServiceId) (fuel : Nat)
    (hNeq : node ≠ target)
    (hNotVis : node ∉ visited) :
    serviceHasPathTo.go st target (node :: rest) visited (fuel + 1) =
    serviceHasPathTo.go st target
      (rest ++ (match lookupService st node with
                | some svc => svc.dependencies
                | none => []).filter (· ∉ visited))
      (node :: visited)
      fuel := by
  simp [serviceHasPathTo.go, hNeq, hNotVis]
```

**Why this matters:** This is the core expansion step. Key properties:

1. **Fuel consumed:** `fuel + 1` → `fuel` (strictly decreases).
2. **Frontier evolves:** `node :: rest` → `rest ++ deps.filter (· ∉ visited)`.
   - `rest` preserves all existing frontier nodes (minus `node`).
   - New nodes from `deps` are appended (FIFO / BFS order).
   - Filter uses the OLD visited set (before adding `node`).
3. **Visited grows:** `visited` → `node :: visited`.
4. **Dependencies source:** `lookupService st node` determines the adjacency list.
   If the node has no service entry, dependencies are `[]` (no successors).

**Subtlety about the deps expression:** The `let` binding in the original `go`
function may or may not be inlined by Lean. The equational lemma should match
whichever form Lean produces. If `simp` doesn't fully reduce, try:

```lean
-- Alternative with explicit let unfolding:
unfold serviceHasPathTo.go
simp only [hNeq, hNotVis, ite_false, Bool.false_eq_true]
```

**Expected difficulty:** Easy, but may require adjusting the RHS to match Lean's
internal representation. Test this lemma early.

---

## 3. Derived equational properties

These are not separate lemmas but useful consequences that may be needed inline:

### 3.1 Self-query always returns true

```lean
-- Not a separate lemma; used for understanding only.
-- serviceHasPathTo st a a (fuel+1) = go [a] [] (fuel+1)
-- go [a] [] (fuel+1): node = a, target = a, if a = a → true
-- Therefore: serviceHasPathTo st a a (fuel+1) = true for all st, a, fuel.
-- This is why the original serviceDependencyAcyclic was vacuous (Risk 0).
```

### 3.2 Fuel monotonicity (informal)

If `go frontier visited fuel = true`, then `go frontier visited (fuel + k) = true`
for any `k`. This follows because extra fuel only enables MORE exploration, never
less. A formal proof would proceed by induction on `fuel` — but this may not be
needed for the completeness proof (we work with adequate fuel from the start).

If needed, formalize as:
```lean
theorem go_fuel_mono
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel k : Nat)
    (hTrue : serviceHasPathTo.go st target frontier visited fuel = true) :
    serviceHasPathTo.go st target frontier visited (fuel + k) = true
```

**Proof approach:** Induction on `fuel` with `frontier`, `visited`, and `k`
generalized. The expansion case uses `fuel + k` ≥ `fuel`, and the skip case
preserves fuel. This is Medium difficulty but may be avoidable.

---

## 4. Implementation order

1. **EQ1** first — validates the tactic approach for accessing `go`.
2. **EQ2** — same difficulty, confirms the pattern works for different cases.
3. **EQ3** — validates `if` reduction for `DecidableEq ServiceId`.
4. **EQ4** — first lemma with hypotheses; tests `simp` with conditional rewriting.
5. **EQ5** — the most complex; may need tactic adjustment.

**If `simp [serviceHasPathTo.go, ...]` fails** on any lemma, fall back to:
```lean
unfold serviceHasPathTo.go
split  -- handles the Nat pattern match
· <zero case>
· split  -- handles the List pattern match
  · <nil case>
  · simp only [...]  -- handles the if chain
```

---

## 5. Placement

All equational lemmas should be placed in `SeLe4n/Kernel/Service/Invariant.lean`,
immediately before the `bfs_complete_for_nontrivialPath` theorem (currently at
line 526). This keeps them adjacent to the BFS bridge infrastructure:

```
Line 508: end of Layer 1 frame lemmas
-- NEW: Layer 2A equational lemmas (EQ1–EQ5)
Line 526: theorem bfs_complete_for_nontrivialPath
```

Alternatively, these could be placed in `Operations.lean` alongside the BFS
definition. Co-locating with the invariant file is preferred for self-containment.
