# 04 — Theorem Dependency Graph

This document is the complete inventory of definitions and theorems required for TPI-D07 closure, ordered by dependency. Each theorem depends only on those above it in the same layer or prior layers.

> **Implementation status:** All layers (0-4) are fully implemented and proved without `sorry` in `SeLe4n/Kernel/Service/Invariant.lean`. Layer 2 (BFS soundness) includes the complete B1-B7 suite; `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE) is proved under the `serviceCountBounded` precondition. Naming evolved during implementation: planned `serviceHasNontrivialPath` (D3) became `serviceNontrivialPath` (inductive type rather than existential def); planned `serviceDependencyAcyclicDecl` (D4) was eliminated — `serviceDependencyAcyclic` itself was redefined declaratively.

---

## Layer 0 — New definitions

These introduce the declarative graph semantics. No proofs required — only well-formed definitions.

| ID | Name | Signature | File | Milestone |
|---|---|---|---|---|
| D1 | `serviceEdge` | `SystemState → ServiceId → ServiceId → Prop` | `Service/Invariant.lean` | M1 |
| D2 | `serviceReachable` | `SystemState → ServiceId → ServiceId → Prop` (inductive) | `Service/Invariant.lean` | M1 |
| D3 | `serviceNontrivialPath` | `SystemState → ServiceId → ServiceId → Prop` (inductive, at least one edge) | `Service/Invariant.lean` | M1 |
| D4 | `serviceDependencyAcyclic` | `SystemState → Prop` (declarative: `∀ sid, ¬ serviceNontrivialPath st sid sid`) | `Service/Invariant.lean` | M1 |

### Definition details

```lean
-- D1: Direct dependency edge (one hop)
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies

-- D2: Reflexive-transitive closure of serviceEdge
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl  : serviceReachable st a a
  | step  : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c

-- D3: Non-trivial path (at least one step, inductive)
inductive serviceNontrivialPath (st : SystemState) : ServiceId → ServiceId → Prop where
  | single : serviceEdge st a b → serviceNontrivialPath st a b
  | cons   : serviceEdge st a b → serviceNontrivialPath st b c → serviceNontrivialPath st a c

-- D4: Declarative acyclicity (no non-trivial self-loops)
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceNontrivialPath st sid sid
```

**Design rationale for D3:** `serviceReachable` includes `refl` (every node trivially reaches itself), so `¬ serviceReachable st sid sid` is always false. The acyclicity invariant must exclude trivial paths. `serviceHasNontrivialPath` captures "reachable via at least one edge."

---

## Layer 1 — Structural lemmas (M1)

These establish basic properties of the declarative path relation and its interaction with store operations.

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| L1 | `serviceReachable_trans` | `serviceReachable st a b → serviceReachable st b c → serviceReachable st a c` | D2 | Induction on first `serviceReachable` |
| L2 | `serviceReachable_of_edge` | `serviceEdge st a b → serviceReachable st a b` | D1, D2 | `exact .step h .refl` |
| L3 | `serviceReachable_of_nontrivialPath` | `serviceNontrivialPath st a b → serviceReachable st a b` | D3, L2 | Induction on nontrivial path |
| L4 | `serviceNontrivialPath_of_edge_reachable` | `serviceEdge st a b → serviceReachable st b c → serviceNontrivialPath st a c` | D1, D2, D3 | Match on reachable, construct nontrivial |
| L5 | `serviceNontrivialPath_of_reachable_ne` | `serviceReachable st a b → a ≠ b → serviceNontrivialPath st a b` | L4 | Cases on reachable, absurd on refl |
| L6 | `serviceNontrivialPath_trans` | `serviceNontrivialPath st a b → serviceNontrivialPath st b c → serviceNontrivialPath st a c` | D3 | Induction on first path |
| L7 | `serviceNontrivialPath_step_right` | `serviceNontrivialPath st a b → serviceEdge st b c → serviceNontrivialPath st a c` | D3 | Induction on path |

### Store-interaction lemmas

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| S1 | `serviceEdge_storeServiceState_ne` | `a ≠ svcId → (serviceEdge (storeServiceState svcId entry st) a b ↔ serviceEdge st a b)` | D1, `storeServiceState_lookup_ne` | Unfold, apply lookup_ne |
| S2 | `serviceEdge_storeServiceState_updated` | `serviceEdge (storeServiceState svcId entry st) svcId b ↔ b ∈ entry.dependencies` | D1, `storeServiceState_lookup_eq` | Unfold, apply lookup_eq |
| S3 | `serviceEdge_post_insert` | Edge characterization after appending `depId` to `svc.dependencies` | S1, S2 | by_cases on `a = svcId`, apply S1 or S2 |

---

## Layer 2 — BFS soundness infrastructure (M2)

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| B1 | `go_true_implies_exists_reachable` | If `go frontier visited fuel = true`, some frontier node reaches target | D2, L1 | Induction on `fuel` with inner induction on `frontier` |
| B2 | `serviceHasPathTo_true_implies_reachable` | `serviceHasPathTo st src target fuel = true → serviceReachable st src target` | B1, D2 | Apply B1 with initial frontier `[src]`, visited `[]` |
| B3 | `serviceHasPathTo_true_implies_nontrivial` | `src ≠ target → serviceHasPathTo st src target fuel = true → serviceNontrivialPath st src target` | B2, D3 | If src ≠ target, the BFS must take at least one edge step |
| B4 | `go_complete` | BFS go loop completeness: given witness in frontier, closure invariant, Nodup visited, and fuel budget, go returns true | D2, L1, `frontier_witness_of_reachable` | Induction on `fuel`, inner induction on `frontier` |
| B5 | `serviceHasPathTo_complete` | `serviceReachable st src target → serviceCountBounded st → serviceHasPathTo st src target (serviceBfsFuel st) = true` | B4, `serviceCountBounded` | Apply B4 with initial state: frontier `[src]`, visited `[]` |
| B6 | `bfs_complete_for_nontrivialPath` | `serviceNontrivialPath st a b → a ≠ b → serviceCountBounded st → serviceHasPathTo st a b (serviceBfsFuel st) = true` | B5, L2 | Extract reachability from nontrivial path, apply B5 |
| B7 | `serviceHasPathTo_false_implies_not_reachable` | `serviceCountBounded st → serviceHasPathTo ... = false → ¬ serviceReachable st src target` | B5 | Contrapositive of B5 |

**Note on B1 vs B4:** B1 proves the "easy direction" (BFS returns `true` → real path exists). B4 proves the "hard direction" setup (real path exists → BFS returns `true`). Both are needed: B1 for Option 1 completeness and for the edge-insertion proof, B4/B6 for soundness.

### Detailed loop invariant (B4)

The invariant for `go frontier visited fuel` is a conjunction:

```
INV(frontier, visited, fuel) :=
  -- (1) Every node in visited was expanded from the frontier
  -- (2) Every node reachable from a visited node via edges to non-visited nodes
  --     is either in the frontier or also visited
  -- (3) If serviceReachable st src target, then either:
  --     (a) target ∈ visited, or
  --     (b) ∃ mid ∈ frontier, serviceReachable st mid target, or
  --     (c) the function will return true
```

The key insight is that condition (3c) is the conclusion we want. The proof proceeds:

1. **Base case** (`fuel = 0`): if `go` returns `false` and fuel is exhausted, the invariant tells us that all reachable nodes must have been visited (by fuel adequacy). Since `target ∉ visited` (otherwise the BFS would have found it), this contradicts reachability.

2. **Inductive step** (`fuel + 1`):
   - **Frontier empty:** conditions (3a) and (3b) are vacuously exhausted, contradicting the assumed reachability.
   - **Node is target:** returns `true` — condition (3c) satisfied.
   - **Node ∈ visited:** frontier shrinks, `go rest visited (fuel + 1)` — invariant preserved with same fuel (visited node recycling).
   - **New node:** frontier evolves, `go (rest ++ deps.filter ...) (node :: visited) fuel` — invariant preserved with one less fuel (node expansion).

---

## Layer 3 — Edge-insertion decomposition (M3)

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| E1 | `nontrivialPath_post_insert_cases` | Post-state nontrivial path decomposes: `serviceNontrivialPath st' a b → serviceNontrivialPath st a b ∨ (serviceReachable st a svcId ∧ serviceReachable st depId b)` | S1, S2, S3, D2, D3 | Induction on `serviceNontrivialPath st' a b`, case-split each edge via `serviceEdge_post_insert` |

### Critical proof: E1 (post-state nontrivial path decomposition)

The proof proceeds by induction on `serviceNontrivialPath st' a b`:

**Case `single`:** A single post-state edge `serviceEdge st' a b`. Case-split via `serviceEdge_post_insert`:
- Old edge (pre-state) → left disjunct: `serviceNontrivialPath st a b` via `.single`.
- New edge (`a = svcId`, `b = depId`) → right disjunct: `serviceReachable st a svcId` (by `.refl`) and `serviceReachable st depId b` (by `.refl`).

**Case `cons`:** Edge `serviceEdge st' a mid` followed by `serviceNontrivialPath st' mid b`. By the IH on the tail, either the tail is a pre-state nontrivial path or uses the new edge. Case-split the head edge via `serviceEdge_post_insert` and compose with the IH to obtain either a full pre-state nontrivial path (left disjunct) or pre-state reachability through the new edge (right disjunct).

---

## Layer 4 — Final closure (M3)

| ID | Name | Statement sketch | Depends on | Tactic hint |
|---|---|---|---|---|
| F1 | `serviceRegisterDependency_preserves_acyclicity` | Acyclicity preserved after successful dependency registration (takes `serviceCountBounded`) | E1, B6, D4, L5 | Post-insertion path decomposition + BFS contradiction |

### Final proof sketch for F1

The actual proof is direct — no BFS/declarative equivalence translation needed since
`serviceDependencyAcyclic` was redefined declaratively:

```lean
-- After case-splitting serviceRegisterDependency to the success branch:
-- We have: hAcyc, hCycle (BFS returned false), hSvc, hSelf (svcId ≠ depId), hBound
-- Goal: serviceDependencyAcyclic st' (i.e., ∀ sid, ¬ serviceNontrivialPath st' sid sid)

intro sid hCycleSid
-- Decompose the post-state cycle via nontrivialPath_post_insert_cases (E1):
rcases nontrivialPath_post_insert_cases hSvc hCycleSid with hPre | ⟨hReach1, hReach2⟩
-- Case 1: cycle in pre-state → contradicts hAcyc
· exact hAcyc sid hPre
-- Case 2: cycle uses new edge → pre-state reachability depId →* svcId
· have hDepSvc := serviceReachable_trans hReach2 hReach1
  have hNontrivial := serviceNontrivialPath_of_reachable_ne hDepSvc (Ne.symm hSelf)
  -- BFS completeness (B6) + serviceCountBounded → BFS returns true
  have hBfsTrue := bfs_complete_for_nontrivialPath hNontrivial (Ne.symm hSelf) hBound
  -- Contradiction: BFS returned false
  exact absurd hBfsTrue hCycle
```

---

## Summary: theorem count (planned vs. implemented)

| Layer | Planned | Implemented | Description |
|---|---|---|---|
| Layer 0 (definitions) | 4 | 4 | `serviceEdge`, `serviceReachable`, `serviceNontrivialPath`, `serviceDependencyAcyclic` |
| Layer 1 (structural) | 12 | 10 | 7 path lemmas + 3 frame lemmas (see Invariant.lean:413-508) |
| Layer 2 (BFS soundness) | 7 | 7 | Full B1-B7 suite + `serviceCountBounded` + `frontier_witness_of_reachable` helper |
| Layer 3 (edge insertion) | 5 | 1 | `nontrivialPath_post_insert_cases` (combines planned E1-E3 logic into one inductive proof) |
| Layer 4 (final closure) | 3 | 1 | `serviceRegisterDependency_preserves_acyclicity` (EQ1/EQ2 unnecessary since `serviceDependencyAcyclic` was redefined declaratively) |
| **Total** | **31** | **23** | All theorems proved without `sorry`; TPI-D07-BRIDGE closed |

The actual implementation was more efficient than the 31-theorem plan: redefining `serviceDependencyAcyclic` to use `serviceNontrivialPath` directly eliminated the need for equivalence theorems (EQ1, EQ2). The full BFS soundness bridge (B1-B7) was implemented, proving BFS-declarative path equivalence under the `serviceCountBounded` precondition.
