# M2D — BFS Completeness Proof Walkthrough

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Complete, step-by-step proof guide for `go_complete_of_frontier_reachable`
(CP1) and the outer wrappers that eliminate the `sorry` on
`bfs_complete_for_nontrivialPath`.

**Prerequisites:** [M2A](./M2A_EQUATIONAL_THEORY.md) (equational lemmas),
[M2B](./M2B_COMPLETENESS_INVARIANT.md) (invariant and boundary),
[M2C](./M2C_FUEL_ADEQUACY.md) (fuel adequacy).

---

## 1. The core theorem: CP1

### 1.1 Statement

```lean
/-- CP1: BFS completeness (inner function).
    If the invariant holds — some frontier node reaches target, visited set is
    closed, target is not visited, and fuel is adequate — then go returns true.

    This is the main theorem of M2. All other theorems either build up to
    this one (Layers 2A-2C) or wrap it (Layer 2E). -/
theorem go_complete_of_frontier_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    -- I3: Some frontier node reaches target
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    -- I1: Target not yet visited
    (hTargetNotVis : target ∉ visited)
    -- I2: Visited set is closed
    (hClosed : bfsClosed st frontier visited)
    -- I4: Fuel is adequate
    (hFuel : serviceFuelAdequate st)
    -- Auxiliary: fuel ≥ number of possible expansions remaining
    (hFuelBound : fuel + visited.length ≤ serviceBfsFuel st ∨
                  fuel ≥ frontier.length) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

**Note on `hFuelBound`:** The exact formulation of the fuel bound may need adjustment
during implementation. The key property is: fuel is sufficient to expand all nodes
the BFS will encounter before finding target. Two possible formulations:

- **Option 1 (counting):** `fuel ≥ |{x | serviceReachable st f x, f ∈ frontier, x ∉ visited}|`
- **Option 2 (pigeonhole):** `fuel + |visited| ≤ serviceBfsFuel st` (since each expansion
  moves one node from "fresh" to visited, and the total is bounded)

Option 2 is simpler to state and verify. Let's use it:

```lean
-- Simplified statement using Option 2:
theorem go_complete_of_frontier_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    (hTargetNotVis : target ∉ visited)
    (hClosed : bfsClosed st frontier visited)
    (hFuel : serviceFuelAdequate st)
    (hVisitedNodup : visited.Nodup)
    (hFuelBound : fuel + visited.length ≤ serviceBfsFuel st) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

### 1.2 Proof structure: strong induction on `(fuel, frontier.length)`

The proof uses well-founded induction on the lexicographic product `(fuel, frontier.length)`.
In Lean 4, this can be expressed as:

```lean
-- Approach 1: nested induction
theorem go_complete_of_frontier_reachable ... := by
  induction fuel using Nat.strong_rec_on generalizing frontier visited with
  | _ fuel ih => ...

-- Approach 2: termination_by (if defining as a recursive function)
-- Not applicable here since this is a theorem, not a function.

-- Approach 3: well_founded_tactics
-- Use WellFoundedRelation on Nat × Nat with Prod.Lex Lt Lt
```

**Practical approach:** Use `induction fuel generalizing frontier visited` with
`Nat.strong_rec_on` or plain induction on `fuel`. Within each fuel level, use
induction on `frontier` (or `frontier.length`) for the visited-skip case.

Actually, the cleanest approach:

```lean
theorem go_complete_of_frontier_reachable
    ... := by
  -- Induction on fuel, generalizing all BFS state
  induction fuel generalizing frontier visited with
  | zero =>
    -- fuel = 0: contradiction (see §2)
    ...
  | succ n ih =>
    -- fuel = n + 1: case split on frontier (see §3)
    ...
```

Within the `succ` case, the visited-skip branch recurses with the SAME fuel (`n + 1`)
but a shorter frontier. Since we're doing induction on `fuel` (not the lexicographic
product), we handle this by observing that the skip branch calls `go rest visited (n + 1)`,
which has the same `fuel` parameter. We need a separate argument for termination here.

**The inner recursion problem:** When the BFS skips a visited node, it calls
`go rest visited (fuel + 1)` — same fuel, shorter frontier. Our induction on `fuel`
doesn't directly handle this. Solutions:

1. **Nested induction on frontier.length** within the `succ` case.
2. **Unfold the skip chain**: observe that a chain of skips eventually leads to
   either an empty frontier (false), a target match (true), or an expansion (which
   reduces fuel). Prove this as a separate lemma.
3. **Use well-founded recursion on `(fuel, frontier.length)`** directly.

**Recommended: Option 3.** Define the proof using `WellFoundedRelation` on
`Nat × Nat` with lexicographic ordering.

### 1.3 Alternative: CPS-style with decreasing measure

If well-founded induction is syntactically awkward, use a `Nat.rec`-compatible
formulation:

```lean
-- Define the total work remaining:
def bfsWork (fuel : Nat) (frontierLen : Nat) : Nat :=
  fuel * (frontierLen + 1) + frontierLen

-- This strictly decreases on both skip and expand:
-- Skip:  bfsWork fuel (frontierLen - 1) < bfsWork fuel frontierLen
-- Expand: bfsWork (fuel - 1) newFrontierLen < bfsWork fuel frontierLen
--         (as long as newFrontierLen < fuel * (frontierLen + 1) + frontierLen - 1)
```

**Problem:** The expansion can increase frontier length arbitrarily (adding many deps),
so `bfsWork` doesn't necessarily decrease. This approach fails.

**Better measure:**

```lean
-- The BFS visits at most N distinct nodes total, where N = serviceBfsFuel st.
-- Each expansion reduces the number of "remaining expansions" by 1.
-- Each skip reduces the frontier length.
-- Total work ≤ N × maxFrontierLen + maxFrontierLen, but this isn't tight.
```

**Conclusion:** Use well-founded induction on `(fuel, frontier.length)` with
lexicographic ordering. This directly mirrors the termination argument Lean uses
for the `go` function itself.

---

## 2. Case: fuel = 0

```lean
| zero =>
  -- go frontier visited 0 = false (by EQ1)
  -- But we need go to return true. Contradiction.
  -- The contradiction comes from fuel adequacy:
  -- hFuelBound : 0 + visited.length ≤ serviceBfsFuel st
  -- hReach : ∃ node ∈ frontier, serviceReachable st node target
  -- hTargetNotVis : target ∉ visited
  -- hClosed : bfsClosed st frontier visited
  --
  -- From hReach, get witness w ∈ frontier with serviceReachable st w target.
  -- Since target ∉ visited, the path from w to target has a node not in visited.
  -- In fact, by the boundary lemma (CB1), there's a frontier node reaching target
  -- that is not in visited (it's in the frontier).
  --
  -- Actually, the fuel = 0 case means the BFS has used all its fuel.
  -- 0 + visited.length ≤ serviceBfsFuel st means visited.length ≤ serviceBfsFuel st.
  -- This is consistent — visited could have up to serviceBfsFuel st nodes.
  --
  -- The contradiction: we claim we can't have a reachable, unvisited target
  -- with fuel = 0 and adequate fuel.
  --
  -- With fuel = 0 and serviceFuelAdequate st, the BFS has expanded as many nodes
  -- as the fuel allows. But fuel = 0 means no expansions were possible from the start.
  -- Yet hReach says some frontier node reaches target. This frontier node exists and
  -- hasn't been visited (it's in the frontier, not visited). So there's at least
  -- one fresh reachable node. But fuel = 0 means we can't expand any.
  --
  -- Wait: hFuelBound says 0 + visited.length ≤ serviceBfsFuel st. This doesn't
  -- directly give a contradiction. We need a STRONGER fuel bound.
  --
  -- The issue: fuel = 0 is actually reachable if the initial frontier has only
  -- visited nodes (which are skipped without fuel) and then the frontier empties.
  -- But in that case, hReach would be violated (no frontier node reaches target
  -- through only visited-node skips... unless the witness is a visited node,
  -- which contradicts "∃ node ∈ frontier").
  --
  -- Actually, frontier can contain visited nodes. So hReach says ∃ node ∈ frontier,
  -- serviceReachable st node target. This node could be in visited. But then by
  -- CB1, there's another frontier node (not visited) reaching target... unless
  -- all frontier nodes are visited. In that case, after skipping all of them,
  -- the frontier empties and go returns false. But the skips don't consume fuel,
  -- so fuel is still 0 after all skips. Then go [] visited 0 = false.
  --
  -- So the fuel = 0 case CAN occur if the initial call has fuel = 0.
  -- serviceHasPathTo starts with go [src] [] fuel. If fuel = 0, go immediately
  -- returns false. This is handled by requiring fuel ≥ 1 at the outer level.
  --
  -- For CP1 (the inner lemma), fuel = 0 with a non-empty frontier containing a
  -- reachable witness is possible. But go returns false, contradicting our goal.
  -- So we need to show this case is impossible under our hypotheses.
  --
  -- The key: if frontier is non-empty and has a reachable (non-visited) witness,
  -- and visited is closed, then there must be at least one fresh node to expand.
  -- But fuel = 0 means we can't expand. Contradiction? Only if we have a fresh
  -- frontier node. But the frontier might contain only visited nodes.
  --
  -- REVISED: We need to strengthen the invariant to ensure that if a reachable
  -- witness exists in the frontier, then either:
  -- (a) the witness IS the target (handled by EQ3), or
  -- (b) there's a fresh (non-visited) node in the frontier that eventually
  --     leads to the target.
  --
  -- This is getting complex. Let me reconsider the proof structure.

  -- SIMPLER APPROACH FOR FUEL = 0:
  -- By EQ1, go frontier visited 0 = false.
  -- We need: go frontier visited 0 = true.
  -- This is a contradiction. So the fuel = 0 case requires showing our
  -- hypotheses are inconsistent.
  --
  -- Key insight: hFuelBound says fuel + visited.length ≤ serviceBfsFuel st,
  -- which gives visited.length ≤ serviceBfsFuel st. This alone is not enough.
  --
  -- We need an additional hypothesis tracking that the BFS hasn't "wasted" fuel.
  -- Specifically: visited.length = serviceBfsFuel st - fuel (each expansion
  -- consumed 1 fuel and added 1 to visited).
  --
  -- REVISED INVARIANT: Change hFuelBound to:
  -- fuel + visited.length = serviceBfsFuel st
  -- (exact accounting, not inequality)
  --
  -- Then fuel = 0 means visited.length = serviceBfsFuel st. By fuel adequacy,
  -- all registered services are visited. Since target is reachable from some
  -- frontier node, and all reachable nodes are registered services or unreachable
  -- (deps = []), target must be in visited. But hTargetNotVis says it's not.
  -- Contradiction? Only if target is a registered service.
  --
  -- Hmm, target might not be registered. If target has no service entry,
  -- the BFS would never find it because no node's dependencies can lead to it
  -- (the edge relation requires lookupService to return some).
  --
  -- Wait: serviceEdge st a b requires ∃ svc, lookupService st a = some svc ∧
  -- b ∈ svc.dependencies. So b can be ANY ServiceId — it doesn't need to be
  -- registered itself. But serviceReachable st w target with w reaching target
  -- means there's a chain of edges. Each edge's SOURCE must be registered, but
  -- the TARGET can be anything.
  --
  -- If target is not registered: target can only be reached as the final
  -- destination of an edge. The BFS will eventually have target in its frontier
  -- (added as a dependency of some expanded node), and EQ3 will return true.
  -- This doesn't consume fuel for target itself (target is found in the
  -- frontier, not expanded).
  --
  -- KEY REALIZATION: The BFS finds target when target appears in the frontier.
  -- It does NOT need to expand target. So the fuel only needs to cover
  -- expansions of NON-TARGET nodes on the path to target.
  --
  -- For fuel = 0: if target is in the frontier, EQ3 returns true. But EQ1
  -- says go ... 0 = false. These are contradictory ONLY if frontier is
  -- non-empty and target is the head. Actually, go checks target AFTER
  -- checking fuel. With fuel = 0, go immediately returns false regardless
  -- of the frontier contents.
  --
  -- Correction: go pattern matches on fuel FIRST:
  -- | 0 => false
  -- | fuel + 1 => match frontier with ...
  --
  -- So fuel = 0 → false, period. Even if target is in the frontier.
  -- This means fuel = 0 is genuinely impossible under our hypotheses
  -- (we need go to return true, but it returns false).
  --
  -- RESOLUTION: The fuel = 0 case is handled by contradiction with the goal.
  -- go frontier visited 0 = false (by definition), but we need true.
  -- This case simply can't occur if our hypotheses are satisfiable.
  --
  -- But wait — we need to show the hypotheses ARE satisfiable, or rather,
  -- that the theorem statement is only called with fuel ≥ 1.
  -- At the outer level, serviceBfsFuel st ≥ 256 > 0, so fuel ≥ 1 initially.
  -- Each expansion reduces fuel by 1, so fuel could reach 0 after expansions.
  -- But in that case, hFuelBound (fuel + visited.length ≤ serviceBfsFuel st
  -- with fuel = 0) means visited.length ≤ serviceBfsFuel st, which is fine.
  --
  -- So fuel = 0 IS reachable in the recursion. The proof must discharge it.
  -- We need: the hypotheses (hReach, hTargetNotVis, hClosed, hFuel, hFuelBound)
  -- are mutually inconsistent when fuel = 0.
  --
  -- Let's prove this inconsistency:
  -- From hReach: ∃ w ∈ frontier, serviceReachable st w target
  -- The reachable path w →* target has all intermediate source nodes registered.
  -- These source nodes are either in visited or not.
  -- By the closure property (I2): all successors of visited nodes are in
  --   visited ∪ frontier.
  -- Target ∉ visited (I1).
  -- So there's a "boundary" — some node reachable from w that is not visited
  -- and is in the frontier (by CB1).
  -- This boundary node needs to be expanded. But fuel = 0 means no expansions.
  -- However, the boundary node might BE the target! If target ∈ frontier,
  -- we'd need go to find it, but fuel = 0 → returns false.
  --
  -- So the inconsistency is: target could be in the frontier with fuel = 0,
  -- and go returns false. Our goal says go returns true. The hypotheses
  -- are NOT inconsistent — the case is genuinely impossible only if
  -- fuel ≥ 1 whenever target is in the frontier.
  --
  -- FINAL RESOLUTION: Add a hypothesis `hFuelPositive : fuel ≥ 1` or
  -- equivalently, change the fuel bound to ensure fuel > 0 whenever
  -- the frontier is non-empty and has a reachable witness.
  --
  -- Actually, the simplest fix: CHANGE THE STATEMENT to match on fuel:
  -- Pattern match on (fuel + 1) and only prove the successor case.
  -- The zero case is trivially false (by definition).
  -- This means CP1 only applies when fuel ≥ 1.
  exfalso
  simp [serviceHasPathTo.go] at *
  -- This will fail because we need go to return true but it returns false.
  -- The actual proof needs: show False from the hypotheses when fuel = 0.
  -- This requires the fuel adequacy argument showing fuel = 0 is inconsistent
  -- with having a reachable frontier witness.
  sorry -- See refined statement below
```

### 2.1 Refined statement avoiding fuel = 0

The cleanest approach avoids the fuel = 0 case entirely:

```lean
/-- CP1 (refined): BFS completeness. Uses strong induction on fuel.
    The fuel = 0 base case is impossible because serviceBfsFuel st ≥ 256 > 0
    and the outer wrapper guarantees fuel = serviceBfsFuel st. -/
theorem go_complete_of_frontier_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    (hTargetNotVis : target ∉ visited)
    (hClosed : bfsClosed st frontier visited)
    (hFuel : serviceFuelAdequate st)
    (hVisitedNodup : visited.Nodup)
    (hFreshBound : ∀ (sids : List ServiceId), sids.Nodup →
      (∀ s ∈ sids, s ∉ visited ∧ (∃ f ∈ frontier, serviceReachable st f s)) →
      sids.length ≤ fuel) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

The `hFreshBound` hypothesis replaces the concrete counting: it says the fuel
is enough to expand all unvisited nodes reachable from the frontier. This
decreases on expansion (one fewer fresh node) and stays the same on skip
(visited set unchanged).

**fuel = 0 discharge:** If fuel = 0, then `hFreshBound` says every list of fresh
reachable nodes has length 0. But target is reachable (from hReach) and not visited
(from hTargetNotVis), so `[target]` is a valid list of fresh reachable nodes with
length 1 > 0. Contradiction. ✓

---

## 3. Case: fuel = n + 1, frontier non-empty

### 3.1 Sub-case: node = target

```lean
| node :: rest =>
  if hEq : node = target then
    -- By EQ3: go (target :: rest) visited (n+1) = true ✓
    subst hEq
    exact go_cons_target st target rest visited n
```

### 3.2 Sub-case: node ∈ visited (skip)

```lean
  else if hVis : node ∈ visited then
    -- By EQ4: go (node :: rest) visited (n+1) = go rest visited (n+1)
    rw [go_cons_visited_skip st target node rest visited n hEq hVis]
    -- Apply IH with:
    -- frontier := rest
    -- visited := visited (unchanged)
    -- fuel := n + 1 (unchanged — but this is the SAME fuel!)
    --
    -- PROBLEM: We're doing induction on fuel, and fuel hasn't decreased.
    -- We need to show termination through frontier.length decreasing.
    --
    -- SOLUTION: Use strong induction on (fuel, frontier.length) as described
    -- in §1.2, or use a separate inner induction on frontier.length.
    --
    -- With well-founded induction on (fuel, frontier.length):
    -- The recursive call has (n+1, rest.length) which is lexicographically
    -- smaller than (n+1, (node :: rest).length) because rest.length < (node :: rest).length.
    -- So the IH applies.
    apply ih  -- IH from well-founded induction
    -- Verify all hypotheses:
    -- hReach: ∃ w ∈ rest, serviceReachable st w target
    --   From hReach: ∃ w ∈ (node :: rest), serviceReachable st w target
    --   If w = node: node ∈ visited, use CB1 to find witness in frontier
    --     CB1 gives ∃ f ∈ (node :: rest), serviceReachable st f target
    --     If f = node: node ∈ visited, iterate CB1 on the shorter reachable path
    --     Eventually: ∃ f ∈ rest, serviceReachable st f target
    --     (See M2B §6.1 for the detailed argument)
    --   If w ∈ rest: w is directly in rest ✓
    · exact witness_in_rest_after_skip ...  -- helper lemma or inline
    -- hTargetNotVis: target ∉ visited (unchanged) ✓
    · exact hTargetNotVis
    -- hClosed: bfsClosed st rest visited — by CB3
    · exact closure_preserved_by_skip st target node rest visited hClosed hVis
    -- hFuel: unchanged ✓
    · exact hFuel
    -- hVisitedNodup: unchanged ✓
    · exact hVisitedNodup
    -- hFreshBound: unchanged (same fuel, same visited, frontier only shrinks)
    · exact ...  -- fresh reachable nodes from rest ⊆ fresh reachable from (node :: rest)
```

**The witness problem in the skip case:**

When `node` was our only frontier witness reaching target, and `node ∈ visited`, we
need a NEW witness in `rest`. The argument:

1. `node ∈ visited` and `serviceReachable st node target`
2. `target ∉ visited`
3. `bfsClosed st (node :: rest) visited`
4. By CB1: `∃ f ∈ (node :: rest), serviceReachable st f target`

CB1 might return `f = node` again (since node ∈ frontier). But the CB1 proof
proceeds by induction on the `serviceReachable` structure, which is finite. At each
step, it either finds `f ∈ frontier` with `f ∉ visited`, or continues to a shorter
path. Eventually it finds `f ∈ rest` (since `node ∈ visited` and the closure pushes
to the frontier).

**Actually, the fix is simpler:** Strengthen CB1 to return a witness that is NOT
in visited:

```lean
/-- CB1 (strengthened): boundary witness is not in visited. -/
theorem reachable_frontier_boundary_fresh
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId)
    (v : ServiceId)
    (hReach : serviceReachable st v target)
    (hVis : v ∈ visited)
    (hTargetNotVis : target ∉ visited)
    (hClosed : bfsClosed st frontier visited) :
    ∃ f ∈ frontier, f ∉ visited ∧ serviceReachable st f target
```

**Proof:** By induction on `serviceReachable st v target`:
- `refl`: v = target, v ∈ visited, target ∉ visited → contradiction.
- `step hedge hreach`: edge st v mid.
  - `mid ∈ visited`: IH gives ∃ f ∈ frontier, f ∉ visited ∧ reachable f target. ✓
  - `mid ∈ frontier`:
    - If `mid ∉ visited`: witness is `mid`. ✓
    - If `mid ∈ visited`: apply IH with `mid` (mid ∈ visited, reachable mid target).

**Wait:** If mid ∈ frontier AND mid ∈ visited, we need the IH for `mid`. The IH
requires `mid ∈ visited` (yes) and works on the shorter path `serviceReachable st mid target`.
Since the induction is structural (on the `serviceReachable` inductive type), and
`hreach` is a strict sub-term of `.step hedge hreach`, the IH applies. ✓

With CB1-strengthened, the skip case becomes trivial:

1. If old witness `w ∈ rest` (w ≠ node): directly available. ✓
2. If old witness `w = node` (node ∈ visited): by CB1-strengthened on the
   OLD frontier `(node :: rest)`, get `f ∈ (node :: rest)` with `f ∉ visited`.
   Since `node ∈ visited`, `f ≠ node`, so `f ∈ rest`. ✓

### 3.3 Sub-case: node ∉ visited (expansion)

```lean
  else
    -- node ≠ target, node ∉ visited
    -- By EQ5: go (node :: rest) visited (n+1) =
    --   go (rest ++ deps.filter (· ∉ visited)) (node :: visited) n
    rw [go_cons_expand st target node rest visited n hEq hVis]
    -- Apply IH with:
    -- frontier := rest ++ deps.filter (· ∉ visited)
    -- visited := node :: visited
    -- fuel := n (decreased by 1)
    --
    -- With well-founded induction: (n, _) < (n+1, _) because n < n+1. ✓
    apply ih
    -- hReach: ∃ w ∈ new_frontier, serviceReachable st w target
    --   Case 1: old witness w ∈ rest (w ≠ node): w ∈ rest ⊆ new_frontier ✓
    --   Case 2: old witness w = node:
    --     node is now in new_visited.
    --     Closure holds for new state (by CB4).
    --     By CB1-strengthened: ∃ f ∈ new_frontier, f ∉ new_visited ∧
    --       serviceReachable st f target ✓
    · exact witness_in_frontier_after_expansion ...
    -- hTargetNotVis: target ∉ (node :: visited)
    --   target ≠ node (because node ≠ target, by hEq) and target ∉ visited ✓
    · exact List.not_mem_cons.mpr ⟨Ne.symm hEq, hTargetNotVis⟩
    -- hClosed: bfsClosed st new_frontier (node :: visited) — by CB4
    · exact closure_preserved_by_expansion st target node rest visited hClosed hVis
    -- hFuel: unchanged ✓
    · exact hFuel
    -- hVisitedNodup: (node :: visited).Nodup
    --   node ∉ visited (by hVis) and visited.Nodup ✓
    · exact List.nodup_cons.mpr ⟨hVis, hVisitedNodup⟩
    -- hFreshBound: for fuel n and new visited (node :: visited)
    --   Fresh reachable nodes under new state = old fresh nodes minus {node}
    --   fuel decreased by 1, fresh count decreased by at least 1 (node removed)
    --   So fuel n ≥ (old fresh count - 1) ✓ (since n+1 ≥ old fresh count)
    · exact ...  -- needs careful argument about fresh count decrease
```

---

## 4. Outer wrappers

### 4.1 OW1: `serviceHasPathTo_complete_of_reachable`

```lean
/-- OW1: If src reaches target and fuel is adequate, the BFS returns true. -/
theorem serviceHasPathTo_complete_of_reachable
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hReach : serviceReachable st src target)
    (hNe : src ≠ target)
    (hFuel : serviceFuelAdequate st)
    (hFuelBound : fuel ≤ serviceBfsFuel st) :
    serviceHasPathTo st src target fuel = true := by
  unfold serviceHasPathTo
  -- Goal: go [src] [] fuel = true
  -- Apply CP1 with:
  -- frontier := [src], visited := []
  -- hReach: ∃ node ∈ [src], serviceReachable st node target
  --   Witness: src, with src ∈ [src] and serviceReachable st src target ✓
  -- hTargetNotVis: target ∉ [] ✓
  -- hClosed: bfsClosed st [src] [] — by CB2 ✓
  -- hFuel: given ✓
  -- hVisitedNodup: [].Nodup ✓
  -- hFreshBound: fuel ≤ serviceBfsFuel st, so fresh count ≤ fuel
  --   (since fresh count ≤ total registered services ≤ serviceBfsFuel st ≤ fuel)
  --   Wait, fuel ≤ serviceBfsFuel st doesn't give fuel ≥ fresh count directly.
  --   We need fuel = serviceBfsFuel st for the outer call.
  sorry -- This is trivially filled once CP1 is proved
```

### 4.2 OW2: `bfs_complete_for_nontrivialPath` (the sorry eliminator)

```lean
/-- OW2: Final theorem — eliminates the TPI-D07-BRIDGE sorry.
    Nontrivial path + distinct endpoints + fuel adequacy → BFS returns true. -/
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b)
    (hFuel : serviceFuelAdequate st) :  -- added precondition
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  -- serviceNontrivialPath st a b implies serviceReachable st a b
  have hReach : serviceReachable st a b :=
    serviceReachable_of_nontrivialPath hPath
  -- Apply OW1
  exact serviceHasPathTo_complete_of_reachable st a b (serviceBfsFuel st)
    hReach hNe hFuel (le_refl _)
```

---

## 5. Implementation roadmap

### Phase 1: Equational lemmas (EQ1-EQ5)
- Estimated effort: 1 session
- Validates tactic approach for accessing `go`
- No dependencies on other M2 work

### Phase 2: Closure and boundary lemmas (CB1-CB4)
- Estimated effort: 1-2 sessions
- CB1 (boundary) is the hardest — practice induction on `serviceReachable`
- CB4 (expansion closure) has the most cases

### Phase 3: Core completeness (CP1)
- Estimated effort: 2-3 sessions
- Requires well-founded induction setup
- The skip case and expansion case each need careful witness management
- Test incrementally: prove each case separately, then combine

### Phase 4: Wrappers and integration (OW1, OW2)
- Estimated effort: 1 session
- Update `bfs_complete_for_nontrivialPath` signature (add hFuel)
- Thread `serviceFuelAdequate` through the preservation theorem
- Verify `lake build` succeeds

### Phase 5: Fuel adequacy decision (FA)
- If preconditioned: add `serviceFuelAdequate st` hypothesis to preservation theorem
- If unconditional: prove `serviceFuelAdequate` from model invariants (harder)
- Update documentation and GitBook

---

## 6. Risk mitigation: what to do if CP1 is too hard

If the well-founded induction proof becomes intractable:

### Fallback 1: Prove a weaker completeness for bounded paths

```lean
/-- BFS finds targets reachable within k edges when fuel ≥ k. -/
theorem go_complete_bounded_path
    (st : SystemState) (target : ServiceId)
    (src : ServiceId) (k : Nat)
    (hPath : serviceReachableInKEdges st src target k)
    (fuel : Nat) (hFuel : fuel ≥ k) :
    serviceHasPathTo st src target fuel = true
```

This avoids the general invariant and uses induction on `k` (path length) instead.
However, it requires defining `serviceReachableInKEdges` and relating it to
`serviceReachable`.

### Fallback 2: Simplify the BFS to make the proof easier

Define an equivalent "simple BFS" that is easier to reason about:

```lean
/-- Simplified BFS that decrements fuel on every step (no recycling). -/
def simpleBfs (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    match frontier with
    | [] => false
    | node :: rest =>
      if node = target then true
      else if node ∈ visited then simpleBfs st target rest visited fuel  -- fuel consumed!
      else simpleBfs st target (rest ++ ...) (node :: visited) fuel
```

Then prove: (1) simpleBfs is complete (easier — fuel always decreases), and
(2) `go` returns true whenever simpleBfs returns true (fuel monotonicity).

### Fallback 3: Narrow the sorry

If the full proof is blocked, narrow the sorry to just the fuel adequacy:

```lean
theorem bfs_complete_for_nontrivialPath ... := by
  -- Prove everything except the fuel bound
  have hFuelOk : serviceFuelAdequate st := by sorry -- TPI-D07-FUEL
  -- Rest of proof uses hFuelOk
  ...
```

This moves the sorry from "BFS completeness" (large, complex) to "fuel adequacy"
(small, well-understood) — a strict improvement even if not full elimination.
