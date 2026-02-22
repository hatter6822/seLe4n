# M2D — BFS Completeness Proof

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Walk through the complete proof that eliminates the `sorry` on
`bfs_complete_for_nontrivialPath`. This document synthesizes M2A (equational
theory), M2B (invariant), and M2C (fuel adequacy) into the final proof.

---

## 1. Target theorem

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hBound : serviceCountBounded st)
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true
```

**Note:** The `hBound` precondition (from [M2C](./M2C_FUEL_ADEQUACY.md) Approach A)
is new. The original theorem had no `serviceCountBounded` hypothesis — the fuel
adequacy was assumed implicitly. Making it explicit is the pragmatic path to sorry
elimination.

---

## 2. Proof structure: three layers

The proof decomposes into three layers:

```
OW2: bfs_complete_for_nontrivialPath
  │
  ├── serviceReachable_of_nontrivialPath (Layer 1, already proved)
  │
  └── OW1: serviceHasPathTo_complete_of_reachable
        │
        └── CP1: go_complete_of_frontier_reachable (core)
              │
              ├── EQ1-EQ5 (M2A: equational theory)
              ├── CB1-CB4 (M2B: closure invariant)
              └── serviceCountBounded (M2C: fuel adequacy)
```

---

## 3. CP1 — Core loop completeness

### 3.1 Statement

```lean
/-- Core BFS completeness: if the invariant holds, the BFS returns true.

    This is the heart of the M2 proof. It carries the four-part invariant
    through all branches of the go function via well-founded induction. -/
theorem go_complete_of_frontier_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    -- I1: target not yet visited
    (hTV : target ∉ visited)
    -- I2: visited-set closure
    (hClosed : bfsClosed st frontier visited)
    -- I3: some frontier node reaches target
    (hReach : ∃ node ∈ frontier, serviceReachable st node target)
    -- I4: fuel bounds unvisited registered services
    (hFuel : ∀ (sids : List ServiceId), sids.Nodup →
             (∀ s ∈ sids, lookupService st s ≠ none ∧ s ∉ visited) →
             sids.length ≤ fuel) :
    serviceHasPathTo.go st target frontier visited fuel = true
```

### 3.2 Proof by well-founded induction

**Induction measure:** `(fuel, frontier.length)` under lexicographic ordering.

```lean
theorem go_complete_of_frontier_reachable ... := by
  -- Outer strong induction on fuel
  induction fuel using Nat.strongRecOn generalizing frontier visited with
  | ind fuel ih_fuel =>
    -- Case analysis on frontier
    obtain ⟨witness, hWitMem, hWitReach⟩ := hReach
    ...
```

### 3.3 Case analysis

**Case A: `frontier = []`**

`witness ∈ []` contradicts `hWitMem`. Close by `exact absurd hWitMem (List.not_mem_nil _)`.

**Case B: `frontier = node :: rest`, `fuel = 0`**

By `go_zero_eq_false` (EQ1), `go` returns `false`. We need a contradiction.

Since `witness ∈ frontier`, at least one node is in the frontier.
`serviceReachable st witness target` with `target ∉ visited` means `target` is
reachable. If `witness = target`, then `target ∈ frontier` and `target ∉ visited`,
so `target` is a registered service not in visited (it must be registered since it
has at least an incoming edge). By `hFuel`, `fuel ≥ 1`. But `fuel = 0` →
contradiction. If `witness ≠ target`, the path from `witness` to `target` has at
least one edge, and the intermediate or `witness` itself is registered and not
visited, giving `fuel ≥ 1`.

More precisely: `witness ∈ frontier` and either `witness = target` (giving a
registered node not in visited) or `witness ≠ target` (giving `witness` itself
as registered and not in visited, via the edge chain). Either way, `hFuel`
applied to `[witness]` or `[target]` gives `fuel ≥ 1`, contradicting `fuel = 0`.

**Case C: `frontier = node :: rest`, `fuel = fuel' + 1`, `node = target`**

By `go_cons_target` (EQ3), `go` returns `true`. Done.

**Case D: `frontier = node :: rest`, `fuel = fuel' + 1`, `node ≠ target`, `node ∈ visited`**

By `go_cons_visited_skip` (EQ4):
```
go (node :: rest) visited (fuel' + 1) = go rest visited (fuel' + 1)
```

Apply `ih_fuel` with:
- `fuel := fuel' + 1` (same fuel — not a decrease, so we need auxiliary argument)
- `frontier := rest` (frontier.length decreases)
- `visited := visited` (unchanged)

**Invariant verification:**
- **I1:** `target ∉ visited` (unchanged). ✓
- **I2:** By CB3 (`closure_preserved_by_skip`). ✓
- **I3:** Need `∃ f ∈ rest, serviceReachable st f target`.
  - If `witness ∈ rest` (i.e., `witness ≠ node`): direct. ✓
  - If `witness = node`: `node ∈ visited`, `serviceReachable st node target`,
    `target ∉ visited`, and CB3 gives `bfsClosed st rest visited`. By CB1
    (`reachable_frontier_boundary`): `∃ f ∈ rest, serviceReachable st f target`. ✓
- **I4:** Unchanged (visited unchanged, fuel unchanged). ✓

**Induction argument for Case D:** Same fuel, shorter frontier. Since `ih_fuel`
is strong induction on fuel, we can't directly apply it with the same fuel.
Instead, use an inner argument: within a fixed fuel level, the frontier shrinks,
so the visited-skip case can only happen finitely many times before we reach a
different case (empty frontier, target found, or expansion).

**Implementation approach:** Use `Nat.strongRecOn` on fuel as the outer induction,
and for the visited-skip sub-case, use an auxiliary inner induction on
`frontier.length` (or use the fact that we can always re-enter the outer induction
with `fuel' + 1 ≤ fuel' + 1`).

Alternatively, use `WellFoundedRelation.wf.induction` on the lexicographic pair
`(fuel, frontier.length)` directly.

**Case E: `frontier = node :: rest`, `fuel = fuel' + 1`, `node ≠ target`, `node ∉ visited`**

By `go_cons_expand` (EQ5):
```
go (node :: rest) visited (fuel' + 1)
  = go (rest ++ deps.filter (· ∉ visited)) (node :: visited) fuel'
```

where `deps = lookupDeps st node`.

Apply `ih_fuel` with:
- `fuel := fuel'` (strictly less than `fuel' + 1` — strong induction step)
- `frontier := rest ++ deps.filter (· ∉ visited)` (new frontier)
- `visited := node :: visited` (new visited)

**Invariant verification:**
- **I1:** `target ∉ node :: visited`. Since `node ≠ target` and `target ∉ visited`. ✓
- **I2:** By CB4 (`closure_preserved_by_expansion`). ✓
- **I3:** Need `∃ f ∈ newFrontier, serviceReachable st f target`.
  - If `witness ∈ rest` (i.e., `witness ≠ node`): `witness ∈ rest ⊆ newFrontier`. ✓
  - If `witness = node`: `node` is now in visited. Since `node ≠ target` and
    `serviceReachable st node target`, the path has at least one edge:
    `serviceEdge st node mid` and `serviceReachable st mid target` for some `mid`.
    By `serviceEdge_iff_lookupDeps`: `mid ∈ lookupDeps st node = deps`.
    - If `mid ∉ visited`: `mid ∈ deps.filter (· ∉ visited) ⊆ newFrontier`.
      Witness is `⟨mid, ..., hReachMidTarget⟩`. ✓
    - If `mid ∈ visited`: `mid ∈ node :: visited` (new visited). Apply CB1
      (`reachable_frontier_boundary`) with new closure (CB4): gives
      `∃ f ∈ newFrontier, serviceReachable st f target`. ✓
- **I4:** Need `hFuel'` for `fuel'` and `node :: visited`. Since `node` was
  unvisited and registered (it has successors looked up by BFS, or it was in the
  frontier), adding `node` to visited reduces the unvisited count by 1. The fuel
  decreased by 1 (`fuel' = fuel' + 1 - 1`). So the new bound holds:
  any Nodup list of registered services not in `node :: visited` is at most
  `fuel' = fuel - 1` long (since it's a subset of the old list minus `node`). ✓

---

## 4. OW1 — Outer wrapper

```lean
/-- If src reaches target and src ≠ target, with adequate fuel,
    then serviceHasPathTo returns true. -/
theorem serviceHasPathTo_complete_of_reachable
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hReach : serviceReachable st src target)
    (hNe : src ≠ target)
    (hBound : serviceCountBounded st)
    (hFuelAdequate : ∀ (sids : List ServiceId), sids.Nodup →
                     (∀ s ∈ sids, lookupService st s ≠ none) →
                     sids.length ≤ fuel) :
    serviceHasPathTo st src target fuel = true := by
  unfold serviceHasPathTo
  apply go_complete_of_frontier_reachable
  -- I1: target ∉ [] (empty visited)
  · exact List.not_mem_nil target
  -- I2: bfsClosed st [src] []
  · exact closure_initial st [src]
  -- I3: ∃ node ∈ [src], serviceReachable st node target
  · exact ⟨src, List.mem_cons_self _ _, hReach⟩
  -- I4: fuel adequacy
  · intro sids hNodup hAll
    exact hFuelAdequate sids hNodup (fun s hs => (hAll s hs).1)
```

**Difficulty:** Easy. This is a straightforward application of CP1 with the
initial BFS state: `frontier = [src]`, `visited = []`, `fuel = fuel`.

---

## 5. OW2 — Sorry elimination

```lean
/-- BFS completeness bridge: the sorry is eliminated. -/
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hBound : serviceCountBounded st)
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  -- Step 1: Extract reachability from nontrivial path
  have hReach := serviceReachable_of_nontrivialPath hPath
  -- Step 2: Apply OW1 with serviceBfsFuel and the bound
  exact serviceHasPathTo_complete_of_reachable st a b
    (serviceBfsFuel st) hReach hNe hBound
    (fun sids hNodup hReg => by
      -- The bound gives allSids with length ≤ serviceBfsFuel
      -- sids is a sublist of allSids (all registered, Nodup)
      obtain ⟨allSids, hAllNodup, hAllCover, hAllBound⟩ := hBound
      exact Nat.le_trans (List.Nodup.length_le_of_forall_mem hNodup
        (fun s hs => hAllCover s (hReg s hs))) hAllBound)
```

**Difficulty:** Easy. The key step is showing that any Nodup list of registered
services is bounded by `serviceBfsFuel st`, which follows directly from
`serviceCountBounded`.

---

## 6. Dependency graph

```
OW2 (bfs_complete_for_nontrivialPath)
  ├── serviceReachable_of_nontrivialPath (Layer 1, existing)
  └── OW1 (serviceHasPathTo_complete_of_reachable)
        ├── closure_initial (CB2, M2B)
        └── CP1 (go_complete_of_frontier_reachable)
              ├── go_zero_eq_false (EQ1, M2A)
              ├── go_nil_eq_false (EQ2, M2A)
              ├── go_cons_target (EQ3, M2A)
              ├── go_cons_visited_skip (EQ4, M2A)
              ├── go_cons_expand (EQ5, M2A)
              ├── serviceEdge_iff_lookupDeps (M2A)
              ├── closure_preserved_by_skip (CB3, M2B)
              ├── closure_preserved_by_expansion (CB4, M2B)
              ├── reachable_frontier_boundary (CB1, M2B)
              └── serviceCountBounded (M2C)
```

---

## 7. Estimated proof sizes

| Component | Lines (estimated) | Difficulty |
|---|---|---|
| `lookupDeps` + `serviceEdge_iff_lookupDeps` | 10-15 | Easy |
| EQ1-EQ5 | 20-35 | Easy |
| `bfsClosed` + CB2 | 5-10 | Trivial |
| CB3 (closure skip) | 10-15 | Easy |
| CB4 (closure expansion) | 20-40 | Medium |
| CB1 (boundary lemma) | 15-25 | Medium |
| `serviceCountBounded` | 5 | Trivial |
| CP1 (core completeness) | 60-100 | **Hard** |
| OW1 (outer wrapper) | 10-15 | Easy |
| OW2 (sorry elimination) | 10-15 | Easy |
| **Total** | **~165-275 lines** | |

The bulk of the difficulty is in CP1 (core completeness) and CB4 (closure
expansion). Everything else is standard list/membership reasoning.

---

## 8. Post-M2 stretch goals

After the sorry is eliminated, the following extensions become possible:

### 8.1 Extraction direction (B1-B3)

```lean
-- B1: BFS true → declarative path exists
theorem serviceHasPathTo_go_true_implies_reachable
    (st : SystemState) (target : ServiceId)
    (frontier visited : List ServiceId) (fuel : Nat)
    (hTrue : serviceHasPathTo.go st target frontier visited fuel = true) :
    ∃ node ∈ frontier, serviceReachable st node target
```

**Proof:** Induction on `fuel` with frontier/visited generalized. Structurally
simpler than completeness because the `true` return witnesses the path constructively.

### 8.2 Full bidirectional equivalence

With both directions proved:
```lean
-- EQ: BFS = reachability (modulo fuel adequacy)
theorem serviceHasPathTo_iff_reachable
    (st : SystemState) (src target : ServiceId) (fuel : Nat)
    (hBound : serviceCountBounded st) (hNe : src ≠ target) :
    serviceHasPathTo st src target fuel = true ↔
    serviceReachable st src target
```

### 8.3 Fuel monotonicity

```lean
theorem go_fuel_mono ... -- see M2A §4
```

These are independent of the sorry elimination and can be pursued in any order.

---

## 9. Implementation checklist

- [ ] `lookupDeps` + `serviceEdge_iff_lookupDeps` (M2A)
- [ ] EQ1-EQ5 (M2A)
- [ ] `bfsClosed` + CB2 (M2B)
- [ ] CB3, CB4 (M2B)
- [ ] CB1 (M2B)
- [ ] `serviceCountBounded` (M2C)
- [ ] CP1 (this document, §3)
- [ ] OW1 (this document, §4)
- [ ] OW2 — sorry elimination (this document, §5)
- [ ] `lake build` succeeds with zero `sorry` in Service/Invariant.lean
- [ ] `./scripts/test_smoke.sh` passes
