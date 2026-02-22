# 04 — Theorem Dependency Graph

This document is the complete inventory of definitions and theorems required for TPI-D07 closure, ordered by dependency. Each theorem depends only on those above it in the same layer or prior layers.

> **Implementation status:** Layers 0, 1, 3, and 4 are fully implemented in `SeLe4n/Kernel/Service/Invariant.lean` (lines 381-637). Layer 2 (BFS soundness) was reduced to a single focused `sorry` on `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE, line 531) rather than the full B1-B7 theorem suite originally planned here. Naming evolved during implementation: planned `serviceHasNontrivialPath` (D3) became `serviceNontrivialPath` (inductive type rather than existential def); planned `serviceDependencyAcyclicDecl` (D4) was eliminated — `serviceDependencyAcyclic` itself was redefined declaratively.

---

## Layer 0 — New definitions

These introduce the declarative graph semantics. No proofs required — only well-formed definitions.

| ID | Name | Signature | File | Milestone |
|---|---|---|---|---|
| D1 | `serviceEdge` | `SystemState → ServiceId → ServiceId → Prop` | `Service/Invariant.lean` | M1 |
| D2 | `serviceReachable` | `SystemState → ServiceId → ServiceId → Prop` (inductive) | `Service/Invariant.lean` | M1 |
| D3 | `serviceHasNontrivialPath` | `SystemState → ServiceId → ServiceId → Prop` (at least one edge) | `Service/Invariant.lean` | M1 |
| D4 | `serviceDependencyAcyclicDecl` | `SystemState → Prop` (declarative version, optional if Option 2) | `Service/Invariant.lean` | M1 |

### Definition details

```lean
-- D1: Direct dependency edge (one hop)
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies

-- D2: Reflexive-transitive closure of serviceEdge
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl  : serviceReachable st a a
  | step  : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c

-- D3: Non-trivial path (at least one step)
def serviceHasNontrivialPath (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ mid, serviceEdge st a mid ∧ serviceReachable st mid b

-- D4: Declarative acyclicity (no non-trivial self-loops)
def serviceDependencyAcyclicDecl (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasNontrivialPath st sid sid
```

**Design rationale for D3:** `serviceReachable` includes `refl` (every node trivially reaches itself), so `¬ serviceReachable st sid sid` is always false. The acyclicity invariant must exclude trivial paths. `serviceHasNontrivialPath` captures "reachable via at least one edge."

---

## Layer 1 — Structural lemmas (M1)

These establish basic properties of the declarative path relation and its interaction with store operations.

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| L1 | `serviceEdge_iff_mem` | `serviceEdge st a b ↔ ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies` | D1 | `simp [serviceEdge]` |
| L2 | `serviceReachable_trans` | `serviceReachable st a b → serviceReachable st b c → serviceReachable st a c` | D2 | Induction on first `serviceReachable` |
| L3 | `serviceReachable_of_edge` | `serviceEdge st a b → serviceReachable st a b` | D1, D2 | `exact .step h .refl` |
| L4 | `serviceReachable_step_right` | `serviceReachable st a b → serviceEdge st b c → serviceReachable st a c` | L2, L3 | `exact L2 h (L3 hedge)` |
| L5 | `serviceHasNontrivialPath_of_edge` | `serviceEdge st a b → serviceHasNontrivialPath st a b` | D1, D3 | `exact ⟨b, h, .refl⟩` |
| L6 | `serviceHasNontrivialPath_trans_edge` | `serviceHasNontrivialPath st a b → serviceEdge st b c → serviceHasNontrivialPath st a c` | D3, L4 | Unfold, compose with L4 |
| L7 | `serviceHasNontrivialPath_of_edge_reachable` | `serviceEdge st a b → serviceReachable st b c → serviceHasNontrivialPath st a c` | D1, D2, D3 | `exact ⟨b, h, hreach⟩` |

### Store-interaction lemmas

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| S1 | `storeServiceState_objectIndex_eq` | `(storeServiceState sid entry st).objectIndex = st.objectIndex` | — | `simp [storeServiceState]` |
| S2 | `serviceBfsFuel_storeServiceState_eq` | `serviceBfsFuel (storeServiceState sid entry st) = serviceBfsFuel st` | S1 | `simp [serviceBfsFuel, S1]` |
| S3 | `serviceEdge_storeServiceState_eq` | `serviceEdge (storeServiceState svcId svc' st) svcId b ↔ b ∈ svc'.dependencies` | D1, `storeServiceState_lookup_eq` | Unfold, apply lookup_eq |
| S4 | `serviceEdge_storeServiceState_ne` | `sid ≠ svcId → (serviceEdge (storeServiceState svcId svc' st) sid b ↔ serviceEdge st sid b)` | D1, `storeServiceState_lookup_ne` | Unfold, apply lookup_ne |
| S5 | `serviceEdge_post_insert` | For the specific `svc' = { svc with dependencies := svc.dependencies ++ [depId] }`: `serviceEdge st' svcId b ↔ b ∈ svc.dependencies ∨ b = depId` | S3 | `simp [S3, List.mem_append, List.mem_singleton]` |

---

## Layer 2 — BFS completeness infrastructure (M2)

> **Revised plan (M2 preparation).** The original B1-B7 suite was a bidirectional
> bridge. After implementation experience, only the *completeness direction*
> (declarative path → BFS `true`) is needed to close the sorry. The extraction
> direction (B1-B3: BFS `true` → declarative path) is a stretch goal. See
> [`M2_BFS_SOUNDNESS.md` §5-§11](milestones/M2_BFS_SOUNDNESS.md) for the
> detailed proof strategy.

### Phase 0: Prerequisites

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| P0.1 | `lookupDeps` | `SystemState → ServiceId → List ServiceId` (helper definition) | — | Definition only |
| P0.2 | `serviceEdge_iff_lookupDeps` | `serviceEdge st a b ↔ b ∈ lookupDeps st a` | D1, P0.1 | Unfold both; case split on `lookupService` |
| U1 | `go_nil_false` | `go st target [] visited fuel = false` | — | `simp [serviceHasPathTo.go]` or `cases fuel` |
| U2 | `go_fuel_zero_false` | `go st target frontier visited 0 = false` | — | `simp [serviceHasPathTo.go]` |
| U3 | `go_target_cons` | `go st target (target :: rest) visited (fuel + 1) = true` | — | `simp [serviceHasPathTo.go]` |
| U4 | `go_visited_skip` | `node ≠ target → node ∈ visited → go (node :: rest) visited (fuel+1) = go rest visited (fuel+1)` | — | Unfold, apply `if` rewrites |
| U5 | `go_expand` | `node ≠ target → node ∉ visited → go (node :: rest) visited (fuel+1) = go (rest ++ deps.filter ...) (node :: visited) fuel` | P0.1 | Unfold, apply `if` rewrites |

### Phase 1: Core completeness

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| P1.1 | `visited_reaches_frontier` | `v ∈ visited → serviceReachable st v target → v ≠ target → hClosure → ∃ f ∈ frontier, serviceReachable st f target` | D2 | Induction on `serviceReachable` proof structure |
| P1.2 | `go_complete_inner` | Core loop: INV1 + INV2 + INV3 + INV4 → `go frontier visited fuel = true` | U1-U5, P0.2, P1.1 | Strong induction on `fuel`; lex with `frontier.length` |
| P1.3 | `go_complete_outer` | `serviceReachable st src target → src ≠ target → fuel adequate → serviceHasPathTo st src target fuel = true` | P1.2 | Unfold `serviceHasPathTo`, instantiate inner with `[src]`, `[]` |

### Phase 2: Fuel adequacy and integration

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| P2.1 | `serviceCountBounded` | `∃ allSids, allSids.Nodup ∧ (∀ sid, lookupService st sid ≠ none → sid ∈ allSids) ∧ allSids.length ≤ serviceBfsFuel st` | — | Definition only |
| P2.3 | `bfs_complete_for_nontrivialPath` | **Sorry elimination** — compose `serviceReachable_of_nontrivialPath` + `go_complete_outer` + `serviceCountBounded` | P1.3, P2.1, existing Layer 1 | See M2_BFS_SOUNDNESS.md §7.1 |

### Original B1-B7 (stretch goals — not needed for sorry elimination)

| ID | Name | Statement sketch | Depends on | Status |
|---|---|---|---|---|
| B1 | `serviceHasPathTo_go_true_implies_reachable` | `go` true → reachable | D2, L1 | Deferred |
| B2 | `serviceHasPathTo_true_implies_reachable` | BFS true → reachable | B1 | Deferred |
| B3 | `serviceHasPathTo_true_implies_nontrivial` | BFS true + `src ≠ target` → nontrivial path | B2, D3 | Deferred |
| B6 | `serviceHasPathTo_false_implies_not_reachable` | BFS false → not reachable | P2.3 (contrapositive) | Follows automatically |
| B7 | `serviceHasPathTo_false_implies_not_nontrivial` | BFS false → no nontrivial path | B6 | Follows automatically |

### Loop invariant details (for `go_complete_inner`)

The four-part invariant for `go frontier visited fuel`:

```
INV1 (frontier reachable): ∃ node ∈ frontier, serviceReachable st node target
INV2 (visited closure):    ∀ v ∈ visited, ∀ w, serviceEdge st v w →
                             w ∈ visited ∨ w ∈ frontier
INV3 (target fresh):       target ∉ visited
INV4 (fuel adequate):      fuel ≥ |unvisited expandable nodes|
```

The proof uses strong induction on `fuel` with four cases:

1. **`frontier = []`:** Contradicts INV1.
2. **`node = target` at head:** `go` returns `true` by U3.
3. **`node ∈ visited`:** By U4, recurse on `rest`. INV1 maintained via
   `visited_reaches_frontier` (P1.1). INV2, INV3 unchanged. INV4: fuel same,
   frontier shorter.
4. **`node ∉ visited`, `node ≠ target`:** By U5, recurse on expanded frontier
   with `node :: visited`. INV1 maintained because children of `node` that
   reach target are in new frontier (via `serviceEdge_iff_lookupDeps`). INV2
   maintained because `node`'s children are in frontier, and old visited
   nodes' frontier references are preserved. INV3 maintained since
   `node ≠ target`. INV4: fuel decreases by 1, one new node visited.

---

## Layer 3 — Edge-insertion decomposition (M3)

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| E1 | `serviceEdge_post_cases` | `serviceEdge st' x y → (x = svcId ∧ (y ∈ svc.dependencies ∨ y = depId)) ∨ (x ≠ svcId ∧ serviceEdge st x y)` | S3, S4, S5 | Case split on `x = svcId` |
| E2 | `serviceReachable_post_insert_of_pre` | `serviceReachable st a b → serviceReachable st' a b` | S4, S5, D2 | Induction on `serviceReachable st a b`; each edge either preserved or strengthened |
| E3 | `serviceReachable_post_insert_cases` | Post-state path decomposes: `serviceReachable st' a b → serviceReachable st a b ∨ (serviceReachable st a svcId ∧ serviceReachable st depId b)` | E1, D2, L2 | Induction on `serviceReachable st' a b` |
| E4 | `nontrivial_cycle_post_insert_implies_pre_reach` | `serviceHasNontrivialPath st' sid sid → serviceDependencyAcyclicDecl st → serviceReachable st depId svcId` | E3, D4 | From E3: cycle uses new edge (else pre-state cycle, contradiction) |
| E5 | `serviceDependencyAcyclicDecl_preserved` | `serviceDependencyAcyclicDecl st → ¬ serviceReachable st depId svcId → serviceDependencyAcyclicDecl st'` | E4 | Contrapositive of E4 |

### Critical proof: E3 (post-state reachability decomposition)

This is the heart of the edge-insertion analysis. The proof proceeds by induction on `serviceReachable st' a b`:

**Case `refl`:** `a = b`, so `serviceReachable st a b` holds by `refl`. Left disjunct.

**Case `step`:** We have `serviceEdge st' a mid` and `serviceReachable st' mid b`. By the induction hypothesis on the second premise, either:
- `serviceReachable st mid b`, or
- `serviceReachable st mid svcId ∧ serviceReachable st depId b`.

For the edge `serviceEdge st' a mid`, we case-split using E1:

- **`a ≠ svcId`:** The edge exists in the pre-state (`serviceEdge st a mid`). Compose with the IH.
- **`a = svcId` and `mid ∈ svc.dependencies`:** The edge exists in the pre-state. Compose with the IH.
- **`a = svcId` and `mid = depId`:** This is the **new edge**. Now `a = svcId` and the path continues from `depId`. The IH gives us either `serviceReachable st depId b` (which yields the right disjunct with `serviceReachable st svcId svcId` via refl... wait, we need `serviceReachable st a svcId`; since `a = svcId`, this is `refl`). So the right disjunct is `serviceReachable st svcId svcId ∧ serviceReachable st depId b`, i.e., `True ∧ serviceReachable st depId b`. But we actually need `serviceReachable st a svcId` — which is `.refl` since `a = svcId`.

The composition is: `serviceReachable st a svcId` (by `a = svcId`, `refl`) and `serviceReachable st depId b` (from IH). This gives the right disjunct.

---

## Layer 4 — Final closure (M3)

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| EQ1 | `serviceDependencyAcyclic_implies_acyclicDecl` | `serviceDependencyAcyclic st → serviceDependencyAcyclicDecl st` | B2, D3, D4 | Contrapositive: nontrivial path implies BFS true (via B2), contradicting acyclic |
| EQ2 | `serviceDependencyAcyclicDecl_implies_acyclic` | `serviceDependencyAcyclicDecl st → serviceDependencyAcyclic st` | B6, D4 | Contrapositive: BFS true implies nontrivial path (via BFS true → reachable, and src = target → nontrivial if BFS found it) |
| F1 | `serviceRegisterDependency_preserves_acyclicity` | The final theorem — replaces `sorry` | EQ1, EQ2, E5, B6, S2 | See proof sketch below |

### Final proof sketch for F1

```lean
-- At the sorry site, after all case splits:
-- We have: hAcyc, hCycle, hSvc, hDep, hSelf, hExists, sid
-- Goal: ¬ serviceHasPathTo st' sid sid (serviceBfsFuel st') = true

-- Step 1: Rewrite fuel in the goal
rw [S2]  -- serviceBfsFuel st' = serviceBfsFuel st

-- Step 2: Translate pre-state acyclicity to declarative form
have hAcycDecl : serviceDependencyAcyclicDecl st := EQ1 hAcyc

-- Step 3: Establish no pre-state path from depId to svcId
have hNoPath : ¬ serviceReachable st depId svcId := B6 hCycle

-- Step 4: Prove declarative acyclicity of post-state
have hAcycDecl' : serviceDependencyAcyclicDecl st' := E5 hAcycDecl hNoPath

-- Step 5: Translate back to BFS-based definition
have hAcyc' : serviceDependencyAcyclic st' := EQ2 hAcycDecl'

-- Step 6: Specialize to the universally quantified sid
exact hAcyc' sid
```

**Note:** Steps 2 and 5 use the equivalence theorems EQ1 and EQ2. If Option 1 is chosen instead (no equivalence, direct BFS reasoning), the proof would be more complex but follow the same logical structure.

---

## Summary: theorem count (planned vs. implemented vs. M2 target)

| Layer | Originally planned | Currently implemented | M2 target (sorry elimination) | Description |
|---|---|---|---|---|
| Layer 0 (definitions) | 4 | 3 | 3 + 1 (lookupDeps) | Existing: `serviceEdge`, `serviceReachable`, `serviceNontrivialPath`. New: `lookupDeps` helper. |
| Layer 1 (structural) | 12 | 10 | 10 + 1 (serviceEdge_iff_lookupDeps) | Existing: 7 path + 3 frame lemmas. New: bridge lemma. |
| Layer 2 (BFS completeness) | 7 | 1 (sorry) | 8 (5 unfolding + 2 completeness + 1 fuel) | Replace `sorry` with: U1-U5, visited_reaches_frontier, go_complete_inner, go_complete_outer, serviceCountBounded. |
| Layer 3 (edge insertion) | 5 | 1 | 1 | `nontrivialPath_post_insert_cases` — no changes needed. |
| Layer 4 (final closure) | 3 | 1 | 1 (+ possible precondition update) | `serviceRegisterDependency_preserves_acyclicity` — may need `serviceCountBounded` hypothesis. |
| **Total** | **31** | **16** | **~25** | M2 adds ~9 new artifacts to eliminate the sorry |

The M2 plan focuses the Layer 2 effort on the completeness direction only (path → BFS `true`).
The extraction direction (B1-B3: BFS `true` → path) and derived soundness (B6-B7) are stretch goals
that follow from completeness but are not needed for sorry elimination.
