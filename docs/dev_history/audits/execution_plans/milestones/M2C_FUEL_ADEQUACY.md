# M2C — Fuel Adequacy

**Parent:** [M2 BFS Soundness Bridge](./M2_BFS_SOUNDNESS.md)

**Purpose:** Resolve the fuel adequacy question — the most architecturally significant
decision in M2. This document analyzes the problem, presents approaches, and recommends
an implementation path.

---

## 1. The fuel adequacy problem

### 1.1 Background

The BFS function uses `serviceBfsFuel st` as the initial fuel:

```lean
-- SeLe4n/Kernel/Service/Operations.lean:96-97
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256
```

The completeness proof (CP1 in [M2D](./M2D_COMPLETENESS_PROOF.md)) requires:

> **Fuel adequacy:** `serviceBfsFuel st` is large enough that the BFS does not
> exhaust fuel before exploring all relevant nodes.

Concretely, the BFS consumes one fuel unit per expansion (new node → visited).
If the graph has *N* distinct registered services, the BFS expands at most *N*
nodes total (each visited at most once). So fuel ≥ *N* is sufficient.

### 1.2 The counting problem

The difficulty is that `services : ServiceId → Option ServiceGraphEntry` is an
opaque total function. We cannot enumerate its domain or count how many `ServiceId`
values map to `some`. There is no `services.keys` or `services.length`.

This means we cannot directly prove `serviceBfsFuel st ≥ |registered services|`
without additional structure.

---

## 2. Approach analysis

### 2.1 Approach A — Explicit bound hypothesis (recommended)

Add a precondition bounding the number of registered services:

```lean
/-- The total number of registered services is bounded by BFS fuel.
    This captures the assumption that serviceBfsFuel provides enough fuel
    to visit every registered service. -/
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ (allSids : List ServiceId),
    allSids.Nodup ∧
    (∀ sid, lookupService st sid ≠ none → sid ∈ allSids) ∧
    allSids.length ≤ serviceBfsFuel st
```

**Pros:**
- Clean Prop-level statement — no model changes.
- Decouples the completeness proof from model analysis.
- Every concrete `SystemState` in the test harness satisfies this (verifiable
  by `decide`).
- Can be discharged later (Approach B) or validated operationally.

**Cons:**
- Adds a precondition to `bfs_complete_for_nontrivialPath`, which propagates
  to the preservation theorem as a hypothesis.
- Must show `serviceCountBounded` is preserved across state mutations (or carry
  it at every call site).

### 2.2 Approach B — Model-level bound (future enhancement)

Add a `serviceIndex : List ServiceId` field to `SystemState` that tracks registered
service IDs, mirroring the existing `objectIndex` pattern:

```lean
structure SystemState where
  machine : SeLe4n.MachineState
  objects : SeLe4n.ObjId → Option KernelObject
  objectIndex : List SeLe4n.ObjId
  services : ServiceId → Option ServiceGraphEntry
  serviceIndex : List ServiceId        -- NEW
  scheduler : SchedulerState
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  lifecycle : LifecycleMetadata
```

**Pros:**
- Eliminates the precondition entirely — fuel adequacy becomes provable
  unconditionally from the model.
- Follows the established `objectIndex` pattern.
- Makes `countUnvisitedRegistered` computable.

**Cons:**
- Model change: requires updating `SystemState` default instance,
  `storeServiceState`, `BootstrapBuilder`, test fixtures, and all existing
  `storeServiceState` lemmas.
- Requires a soundness invariant (`serviceIndexSound`) relating the index
  to the `services` function.
- Medium-effort change with broad touch surface.

**Impact analysis for Approach B:**

| Area | Change required | Effort |
|------|-----------------|--------|
| `SystemState` default instance | Add `serviceIndex := []` | Trivial |
| `storeServiceState` | Add `sid` to `serviceIndex` if not present | Small |
| `serviceBfsFuel` | Redefine as `st.serviceIndex.length + 1` or keep current | Small |
| `BootstrapBuilder` / test fixtures | Include `serviceIndex` in construction | Small |
| Existing `storeServiceState` lemmas | Update for new field | Medium |
| `serviceEdge_*` frame lemmas | Unaffected (only use `services`) | None |

### 2.3 Approach C — Reachability-local bound (deferred)

Instead of bounding all services, bound only the reachable subgraph from `src`.
Since `serviceNontrivialPath st a b` has finite inductive structure, the reachable
subgraph from `a` is bounded. However, the BFS does not follow the shortest path
and may explore the entire connected component, making path-length bounds
insufficient for fuel adequacy.

**Verdict:** Elegant but requires connected-component size bounds. Defer.

---

## 3. Recommended approach: A then B

**Phase 1 (M2 closure):** Use Approach A. The `serviceCountBounded` precondition
is clean, pragmatic, and sufficient for sorry elimination.

**Phase 2 (post-M2):** Migrate to Approach B if the precondition becomes
burdensome. The `serviceIndex` field would make fuel adequacy unconditional.

---

## 4. Approach A implementation details

### 4.1 Core definition

```lean
/-- The total number of registered services is bounded by BFS fuel. -/
def serviceCountBounded (st : SystemState) : Prop :=
  ∃ (allSids : List ServiceId),
    allSids.Nodup ∧
    (∀ sid, lookupService st sid ≠ none → sid ∈ allSids) ∧
    allSids.length ≤ serviceBfsFuel st
```

### 4.2 Fuel adequacy arithmetic

The core completeness lemma (CP1 in M2D) tracks fuel consumption through invariant I4:

```
I4: fuel ≥ |{ sid | lookupService st sid ≠ none ∧ sid ∉ visited }|
```

When a new node is expanded:
- `fuel` decreases by 1 (BFS passes `fuel` where it received `fuel + 1`)
- The unvisited count decreases by 1 (expanded node joins visited)
- So `fuel - 1 ≥ unvisitedCount - 1` holds.

When a visited node is skipped:
- `fuel` is unchanged (BFS passes `fuel + 1` where it received `fuel + 1`)
- The unvisited count is unchanged
- So the inequality is preserved.

### 4.3 Connecting to the outer theorem

The sorry-carrying theorem gains a precondition:

```lean
theorem bfs_complete_for_nontrivialPath
    {st : SystemState} {a b : ServiceId}
    (hBound : serviceCountBounded st)   -- NEW precondition
    (hPath : serviceNontrivialPath st a b)
    (hNe : a ≠ b) :
    serviceHasPathTo st a b (serviceBfsFuel st) = true := by
  have hReach := serviceReachable_of_nontrivialPath hPath
  exact go_complete_outer st a b (serviceBfsFuel st) hReach hNe hBound
```

### 4.4 Impact on preservation theorem

The preservation theorem (`serviceRegisterDependency_preserves_acyclicity`)
uses `bfs_complete_for_nontrivialPath` in its proof. With the new precondition,
it would gain a `(hBound : serviceCountBounded st)` hypothesis.

This is acceptable because:
1. Every concrete `SystemState` constructed by the test harness satisfies
   `serviceCountBounded`.
2. The bound is preserved by `storeServiceState` (updating a service does not
   increase the count; adding a new service increases it by at most 1, absorbed
   by the +256 slack in `serviceBfsFuel`).

### 4.5 Preservation of `serviceCountBounded`

```lean
/-- storeServiceState preserves serviceCountBounded when the service
    is already registered (update, not insertion). -/
theorem serviceCountBounded_storeServiceState_update
    {st : SystemState} {sid : ServiceId} {entry : ServiceGraphEntry}
    (hBound : serviceCountBounded st)
    (hExists : lookupService st sid ≠ none) :
    serviceCountBounded (storeServiceState sid entry st)

/-- storeServiceState preserves serviceCountBounded when the service
    is new, provided the fuel slack absorbs the new entry. -/
theorem serviceCountBounded_storeServiceState_new
    {st : SystemState} {sid : ServiceId} {entry : ServiceGraphEntry}
    (hBound : serviceCountBounded st)
    (hSlack : serviceBfsFuel (storeServiceState sid entry st) ≥
              serviceBfsFuel st) :
    serviceCountBounded (storeServiceState sid entry st)
```

**Status:** These are NOT required for M2 completion (sorry elimination).
They are needed for composability in the preservation theorem chain and
can be addressed as follow-up work.

---

## 5. Induction measure

The completeness proof (CP1 in M2D) requires a well-founded induction measure.
The BFS `go` function has non-standard recursion:

| Branch | Fuel change | Frontier change |
|--------|-------------|-----------------|
| fuel = 0 | Base case | — |
| frontier = [] | Base case | — |
| node = target | Returns `true` | — |
| node ∈ visited | `fuel + 1 → fuel + 1` (unchanged!) | `node :: rest → rest` (shrinks) |
| node ∉ visited | `fuel + 1 → fuel` (decreases) | `node :: rest → rest ++ deps` (may grow) |

### 5.1 Recommended measure: `(fuel, frontier.length)` lexicographic

| BFS branch | First component | Second component | Lexicographic decrease |
|---|---|---|---|
| Visited skip | fuel unchanged | frontier.length decreases | ✓ (second decreases) |
| Expansion | fuel decreases | frontier.length irrelevant | ✓ (first decreases) |

**Implementation in Lean 4:**

```lean
-- Well-founded induction on fuel (outer), with inner case analysis
-- on frontier.length for the visited-skip case
theorem go_complete_of_frontier_reachable ... := by
  -- Use Nat.strongRecOn on fuel
  induction fuel using Nat.strongRecOn generalizing frontier visited with
  | ind fuel ih => ...
```

For the visited-skip case within a fixed fuel level, use an auxiliary argument
that frontier.length decreases (e.g., an inner induction or explicit bound).

### 5.2 Alternative measure: `(countUnvisited, frontier.length)`

An alternative is to induct on `(countUnvisitedRegistered st visited, frontier.length)`:

- **Visited skip:** first component unchanged, second decreases. ✓
- **Expansion:** first component decreases (node leaves unvisited set). ✓

This avoids reasoning about fuel entirely but requires defining
`countUnvisitedRegistered` and proving it decreases. Under Approach A
(preconditioned), this measure is abstract and harder to work with in Lean.

**Recommendation:** Use `(fuel, frontier.length)` for the proof. It's more
concrete, matches the actual recursion structure of `go`, and avoids the need
for a computable `countUnvisitedRegistered`.

---

## 6. Placement

The `serviceCountBounded` definition and fuel-related lemmas go in
`SeLe4n/Kernel/Service/Invariant.lean`, after the closure lemmas (M2B)
and before the core completeness theorem (M2D):

```
-- M2B: bfsClosed, CB1-CB4
-- NEW: serviceCountBounded definition
-- M2D: CP1, OW1, OW2
```
