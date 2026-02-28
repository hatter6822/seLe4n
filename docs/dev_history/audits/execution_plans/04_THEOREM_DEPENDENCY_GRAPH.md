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

> **Revised plan.** The original B1–B7 scheme has been replaced with a targeted
> completeness-focused approach organized into four sub-documents. See
> [M2_BFS_SOUNDNESS.md](./milestones/M2_BFS_SOUNDNESS.md) and M2A–M2D.

### Layer 2 prerequisite: deps bridge

| ID | Name | Statement sketch | Depends on | Difficulty |
|---|---|---|---|---|
| LD | `lookupDeps` (definition) | `lookupDeps st node := match lookupService st node with some svc => svc.dependencies \| none => []` | — | Trivial |
| LB | `serviceEdge_iff_lookupDeps` | `serviceEdge st a b ↔ b ∈ lookupDeps st a` | LD, D1 | Easy |

### Layer 2A — Equational lemmas ([M2A](./milestones/M2A_EQUATIONAL_THEORY.md))

| ID | Name | Statement sketch | Depends on | Difficulty |
|---|---|---|---|---|
| EQ1 | `go_zero_eq_false` | `go frontier visited 0 = false` | — | Trivial |
| EQ2 | `go_nil_eq_false` | `go [] visited (fuel+1) = false` | — | Trivial |
| EQ3 | `go_cons_target` | `go (target :: rest) visited (fuel+1) = true` | — | Trivial |
| EQ4 | `go_cons_visited_skip` | `node ≠ target → node ∈ visited → go (node::rest) visited (f+1) = go rest visited (f+1)` | — | Easy |
| EQ5 | `go_cons_expand` | `node ≠ target → node ∉ visited → go (node::rest) visited (f+1) = go (rest ++ (lookupDeps st node).filter ...) (node::visited) f` | LD | Easy |

### Layer 2B — Closure and boundary ([M2B](./milestones/M2B_COMPLETENESS_INVARIANT.md))

| ID | Name | Statement sketch | Depends on | Difficulty |
|---|---|---|---|---|
| CD | `bfsClosed` (definition) | `∀ v ∈ visited, ∀ dep, serviceEdge st v dep → dep ∈ visited ∨ dep ∈ frontier` | D1 | Definition |
| CB1 | `reachable_frontier_boundary` | `v ∈ visited → serviceReachable st v target → target ∉ visited → bfsClosed → ∃ f ∈ frontier, serviceReachable st f target` | CD, D2 | Medium |
| CB2 | `closure_initial` | `bfsClosed st frontier []` | CD | Trivial |
| CB3 | `closure_preserved_by_skip` | `bfsClosed st (node::rest) visited → node ∈ visited → bfsClosed st rest visited` | CD | Easy |
| CB4 | `closure_preserved_by_expansion` | `bfsClosed st (node::rest) visited → node ∉ visited → bfsClosed st (rest ++ deps.filter ...) (node::visited)` | CD, LB | Medium |

### Layer 2C — Fuel adequacy ([M2C](./milestones/M2C_FUEL_ADEQUACY.md))

| ID | Name | Statement sketch | Depends on | Difficulty |
|---|---|---|---|---|
| FA1 | `serviceCountBounded` (definition) | `∃ allSids, allSids.Nodup ∧ (∀ sid, lookupService st sid ≠ none → sid ∈ allSids) ∧ allSids.length ≤ serviceBfsFuel st` | — | Definition |

### Layer 2D — Core completeness ([M2D](./milestones/M2D_COMPLETENESS_PROOF.md))

| ID | Name | Statement sketch | Depends on | Difficulty |
|---|---|---|---|---|
| CP1 | `go_complete_of_frontier_reachable` | `I1 ∧ I2 ∧ I3 ∧ I4 → go frontier visited fuel = true` | EQ1–5, CB1–4, FA1 | **Hard** |
| OW1 | `serviceHasPathTo_complete_of_reachable` | `serviceReachable st src target → src ≠ target → ... → serviceHasPathTo st src target fuel = true` | CP1, CB2 | Easy |
| OW2 | `bfs_complete_for_nontrivialPath` | `serviceNontrivialPath st a b → a ≠ b → serviceCountBounded st → serviceHasPathTo st a b (serviceBfsFuel st) = true` | OW1, L5 | Easy |

### Revised loop invariant

The invariant for `go frontier visited fuel` is:

```
BfsInvariant(st, target, frontier, visited, fuel) :=
  (I1) target ∉ visited
  (I2) bfsClosed st frontier visited (= ∀ v ∈ visited, ∀ dep, serviceEdge st v dep → dep ∈ visited ∨ dep ∈ frontier)
  (I3) ∃ node ∈ frontier, serviceReachable st node target
  (I4) fuel ≥ |unvisited registered services|  (via serviceCountBounded precondition)
```

The proof proceeds by well-founded induction on `(fuel, frontier.length)`:

- **fuel = 0:** Contradiction — I3 + I4 imply at least one unvisited registered node exists, but fuel = 0 means no expansion possible.
- **Frontier empty:** Contradiction with I3 (no frontier witness).
- **Node = target:** EQ3 returns true immediately.
- **Node ∈ visited (skip):** CB3 preserves I2. CB1 recovers I3 in `rest`. Same fuel, shorter frontier → lexicographic decrease on second component.
- **Node ∉ visited (expand):** CB4 preserves I2. CB1 recovers I3 in new frontier. Fuel decreases → lexicographic decrease on first component.

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

## Summary: theorem count (planned vs. implemented)

| Layer | Planned | Implemented | Description |
|---|---|---|---|
| Layer 0 (definitions) | 4 | 3 | `serviceEdge`, `serviceReachable`, `serviceNontrivialPath` (replaces D3+D4: `serviceDependencyAcyclic` redefined in-place) |
| Layer 1 (structural) | 12 | 10 | 7 path lemmas + 3 frame lemmas (naming adjusted; see Invariant.lean:413-508) |
| Layer 2 (BFS completeness) | 15 | 1 | Revised plan: LD, LB, EQ1–5, CD, CB1–4, FA1, CP1, OW1–2 targeting `bfs_complete_for_nontrivialPath` sorry (TPI-D07-BRIDGE); see M2A–M2D |
| Layer 3 (edge insertion) | 5 | 1 | `nontrivialPath_post_insert_cases` (combines E1-E3 logic into one inductive proof) |
| Layer 4 (final closure) | 3 | 1 | `serviceRegisterDependency_preserves_acyclicity` (sorry-free; EQ1/EQ2 unnecessary since `serviceDependencyAcyclic` was redefined declaratively) |
| **Total** | **31** | **16** | Proof completed with fewer artifacts by redefining the invariant declaratively |

The actual implementation was more efficient than the 31-theorem plan: redefining `serviceDependencyAcyclic` to use `serviceNontrivialPath` directly eliminated the need for equivalence theorems (EQ1, EQ2) and much of the original BFS bridge infrastructure (B1-B7). Layer 2 has been re-planned with a targeted completeness approach (15 artifacts: 1 helper definition + 1 bridge lemma + 5 equational lemmas + 1 closure definition + 4 closure/boundary lemmas + 1 fuel adequacy definition + 3 completeness theorems) documented across M2A–M2D. The remaining BFS bridge `sorry` is the sole target of this revised plan.
