# Milestone M2 — BFS Soundness Bridge

**Goal:** Eliminate the `sorry` on `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE,
`Invariant.lean:526-531`) by proving BFS completeness: if a declarative nontrivial path
exists between distinct services, the bounded BFS returns `true`.

**Dependency:** M1 (declarative path definitions, structural lemmas — COMPLETE)

**Blocking:** M3 preservation theorem uses `bfs_complete_for_nontrivialPath` at line 634.

**Risk level:** HIGH — technically hardest milestone. See [Risk R1](../05_RISK_REGISTER.md#risk-1)
(fuel adequacy) and [Risk R3](../05_RISK_REGISTER.md#risk-3) (BFS loop invariant).

**Status:** DEFERRED → IN PREPARATION (documentation expanded for implementation)

---

## 1. The sorry under attack

```lean
-- SeLe4n/Kernel/Service/Invariant.lean:526-531
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (_hPath : serviceNontrivialPath st a b)
    (_hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  sorry -- TPI-D07-BRIDGE: BFS completeness proof deferred
```

This is the sole remaining `sorry` in the TPI-D07 proof chain. The preservation
theorem (`serviceRegisterDependency_preserves_acyclicity`, line 591) is structurally
complete — it calls `bfs_complete_for_nontrivialPath` at line 634 to derive a
contradiction between the BFS cycle-detection check and the existence of a
declarative path.

### 1.1 Why the easy direction isn't enough

The M3 preservation proof needs the **completeness** direction (declarative path →
BFS true), not the soundness direction (BFS false → no path). The proof structure is:

1. Assume post-state cycle exists
2. Decompose into pre-state reachability (`nontrivialPath_post_insert_cases`)
3. Derive `serviceNontrivialPath st depId svcId` with `depId ≠ svcId`
4. **Apply `bfs_complete_for_nontrivialPath`** to conclude BFS returns `true`
5. Contradict the BFS check that returned `false` (`hCycle`)

So the hard direction IS the completeness direction: proving the BFS finds paths
that declaratively exist.

### 1.2 What makes this hard

Three interlocking challenges create the difficulty:

| Challenge | Core issue | Sub-document |
|---|---|---|
| **BFS non-standard recursion** | Fuel recycling on visited nodes; `(fuel, frontier.length)` lexicographic measure | [M2A](./M2A_EQUATIONAL_THEORY.md) |
| **Loop invariant formulation** | Visited-set closure, frontier reachability, boundary transitions | [M2B](./M2B_COMPLETENESS_INVARIANT.md) |
| **Fuel adequacy** | `services : ServiceId → Option ServiceGraphEntry` has infinite domain; `serviceBfsFuel` must bound reachable nodes | [M2C](./M2C_FUEL_ADEQUACY.md) |

The detailed proof walkthrough combining all three is in [M2D](./M2D_COMPLETENESS_PROOF.md).

---

## 2. Architecture of the proof

### 2.1 The BFS function under analysis

```lean
-- SeLe4n/Kernel/Service/Operations.lean:110-127
def serviceHasPathTo
    (st : SystemState) (src target : ServiceId) (fuel : Nat) : Bool :=
  go [src] [] fuel
where
  go (frontier visited : List ServiceId) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      match frontier with
      | [] => false
      | node :: rest =>
          if node = target then true
          else if node ∈ visited then go rest visited (fuel + 1)  -- ← fuel RECYCLED
          else
            let deps := match lookupService st node with
              | some svc => svc.dependencies
              | none => []
            let newFrontier := rest ++ deps.filter (· ∉ visited)
            go newFrontier (node :: visited) fuel              -- ← fuel CONSUMED
```

Key observations about `go`:

1. **Target check is first** — before visited check. If target is in the frontier,
   it WILL be detected regardless of visited status.
2. **Fuel recycled on skip** — `go rest visited (fuel + 1)` passes the same fuel
   as the input. Fuel is only consumed when expanding a genuinely new node.
3. **Frontier is FIFO** — new dependencies are appended via `rest ++ deps.filter ...`.
   This is BFS order, not DFS.
4. **Filter uses old visited** — `deps.filter (· ∉ visited)` checks against visited
   BEFORE adding the current node. The current node is added to visited in the
   recursive call.

### 2.2 Termination measure

Lean accepts `go` via well-founded recursion on the lexicographic measure
`(fuel, frontier.length)`:

| Branch | fuel | frontier.length | Measure change |
|---|---|---|---|
| `fuel + 1`, visited skip | `fuel + 1` (same) | decreases (rest < node::rest) | Second component ↓ |
| `fuel + 1`, expansion | `fuel` (decreases) | may increase | First component ↓ |
| `0` or `[]` | — | — | Base case |

This measure is critical — we must use the same measure in our induction proofs.

### 2.3 Lemma dependency graph

```
Layer 2A: BFS Equational Lemmas (5 lemmas)
    │
    ▼
Layer 2B: Closure & Boundary (4 lemmas)
    │
    ▼
Layer 2C: Fuel Adequacy (2 definitions + 1 lemma)
    │
    ▼
Layer 2D: Inner Completeness (1 core theorem)
    │
    ▼
Layer 2E: Outer Wrappers (2 theorems)
    │
    ▼
bfs_complete_for_nontrivialPath  ← eliminates sorry
```

### 2.4 Complete theorem inventory

| ID | Name | Layer | Difficulty | Status |
|---|---|---|---|---|
| EQ1 | `go_zero_eq_false` | 2A | Trivial | Planned |
| EQ2 | `go_nil_eq_false` | 2A | Trivial | Planned |
| EQ3 | `go_cons_target` | 2A | Trivial | Planned |
| EQ4 | `go_cons_visited_skip` | 2A | Easy | Planned |
| EQ5 | `go_cons_expand` | 2A | Easy | Planned |
| CB1 | `reachable_frontier_boundary` | 2B | Medium | Planned |
| CB2 | `closure_initial` | 2B | Trivial | Planned |
| CB3 | `closure_preserved_by_skip` | 2B | Easy | Planned |
| CB4 | `closure_preserved_by_expansion` | 2B | Medium | Planned |
| FA1 | `serviceFuelAdequate` (def) | 2C | — | Planned |
| FA2 | `freshCount_decreases_on_expansion` | 2C | Medium | Planned |
| FA3 | `serviceBfsFuel_sufficient_precondition` | 2C | Medium | Planned |
| CP1 | `go_complete_of_frontier_reachable` | 2D | **Hard** | Planned |
| OW1 | `serviceHasPathTo_complete_of_reachable` | 2E | Easy | Planned |
| OW2 | `bfs_complete_for_nontrivialPath` | 2E | Easy (wraps CP1) | Planned |

**Total: 13 lemmas + 2 definitions → eliminates 1 sorry**

---

## 3. Proof strategy decision: completeness via contrapositive

The completeness proof has two possible framings:

### Option A: Direct completeness (chosen)

> If `serviceNontrivialPath st a b` and `a ≠ b`, then `serviceHasPathTo st a b fuel = true`.

Prove by showing the BFS, when given enough fuel, discovers every reachable node.
This requires a loop invariant about the BFS state.

### Option B: Contrapositive soundness

> If `serviceHasPathTo st a b fuel = false`, then `¬ serviceNontrivialPath st a b`.

This is logically equivalent but requires reasoning about what "false" means —
that the BFS exhausted all possibilities. Surprisingly, this is NOT easier than
direct completeness; both require the same visited-set closure argument.

**Decision: Option A (direct completeness).** The proof works forward from a
known path and shows the BFS finds it, which aligns with the inductive structure
of `serviceNontrivialPath`.

---

## 4. Sub-document map

| Document | Contents | Why separate |
|---|---|---|
| [**M2A: Equational Theory**](./M2A_EQUATIONAL_THEORY.md) | 5 equational lemmas unfolding `go` for each branch; tactic patterns for accessing the `where`-defined function | These are mechanical and reusable; separating them prevents noise in the main proof |
| [**M2B: Completeness Invariant**](./M2B_COMPLETENESS_INVARIANT.md) | Loop invariant formulation; closure property; boundary lemma; invariant preservation across BFS steps | The conceptual core — understanding THIS is the key to understanding the proof |
| [**M2C: Fuel Adequacy**](./M2C_FUEL_ADEQUACY.md) | Fuel adequacy precondition design; analysis of `services` domain; discharge strategies; fresh-count measure | The architectural decision point — determines whether the theorem is unconditional or preconditioned |
| [**M2D: Completeness Proof**](./M2D_COMPLETENESS_PROOF.md) | Complete proof walkthrough combining 2A-2C; strong induction structure; case analysis; final wrappers | The implementation guide — follow this to write the Lean code |

---

## 5. Exit criteria

- [ ] All Layer 2A equational lemmas compile without `sorry`
- [ ] All Layer 2B closure/boundary lemmas compile without `sorry`
- [ ] Fuel adequacy approach chosen and formalized (preconditioned or unconditional)
- [ ] `go_complete_of_frontier_reachable` (CP1) compiles without `sorry`
- [ ] `bfs_complete_for_nontrivialPath` compiles without `sorry`
- [ ] `lake build` succeeds with zero `sorry` in `Invariant.lean`
- [ ] `./scripts/test_smoke.sh` passes
- [ ] M3 preservation theorem remains valid (no signature changes)

## 6. Validation

```bash
# Tier 0+1: build succeeds, no new sorry
./scripts/test_fast.sh

# Tier 0-2: traces and negative-state tests pass
./scripts/test_smoke.sh

# Verify sorry elimination
rg 'sorry' SeLe4n/Kernel/Service/Invariant.lean  # should return 0 matches

# Verify preservation theorem still compiles
lake build SeLe4n.Kernel.Service.Invariant
```
