# Milestone M1 — Declarative Graph-Path Semantics

**Goal:** Introduce a proof-friendly inductive path relation over the service dependency graph, independent of the BFS implementation. Prove structural lemmas and store-interaction lemmas.

**Dependency:** M0 (baseline lock, store lemma inventory)

**Estimated theorems added:** 16 (4 definitions + 7 structural lemmas + 5 store lemmas)

---

## 1. Definitions

### 1.1 Edge relation (D1)

```lean
/-- A direct dependency edge exists from `a` to `b` in the service graph of state `st`. -/
def serviceEdge (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies
```

**Design note:** This uses `lookupService` (the same accessor used by `serviceHasPathTo` at `Operations.lean:123`), ensuring the edge relation is semantically aligned with the BFS behavior.

### 1.2 Reachable relation (D2)

```lean
/-- Reflexive-transitive closure of `serviceEdge`. `serviceReachable st a b` holds when
    there exists a (possibly empty) sequence of dependency edges from `a` to `b`. -/
inductive serviceReachable (st : SystemState) : ServiceId → ServiceId → Prop where
  | refl  : serviceReachable st a a
  | step  : serviceEdge st a b → serviceReachable st b c → serviceReachable st a c
```

**Alternative considered:** Using `Relation.ReflTransGen` from Mathlib/Std. The custom inductive is preferred because:
1. The seLe4n project does not import Mathlib.
2. A custom definition avoids version coupling.
3. The step-left form (`step : edge a b → reach b c → reach a c`) is more natural for BFS proofs where we extend paths from the source.

### 1.3 Non-trivial path (D3)

```lean
/-- A non-trivial path (at least one edge) exists from `a` to `b`. -/
def serviceHasNontrivialPath (st : SystemState) (a b : ServiceId) : Prop :=
  ∃ mid, serviceEdge st a mid ∧ serviceReachable st mid b
```

**Why this definition:** `serviceReachable st a a` is trivially true (by `refl`), so acyclicity cannot be stated as `¬ serviceReachable st sid sid`. Instead, we need "no path of length ≥ 1 from `sid` to itself." The existential witness `mid` is the first hop, and `serviceReachable st mid b` is the remaining path (which can be empty).

### 1.4 Declarative acyclicity (D4)

```lean
/-- The service dependency graph is acyclic: no non-trivial path from any service to itself. -/
def serviceDependencyAcyclicDecl (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasNontrivialPath st sid sid
```

**Relationship to `serviceDependencyAcyclic`:** The BFS-based invariant (`serviceDependencyAcyclic`) and the declarative invariant (`serviceDependencyAcyclicDecl`) are equivalent under fuel adequacy. The equivalence is proved in M3 (Layer 4 theorems EQ1 and EQ2).

---

## 2. Structural lemmas

### 2.1 Definitional unfolding

```lean
/-- Unfold the edge relation to its definition. -/
theorem serviceEdge_iff_mem (st : SystemState) (a b : ServiceId) :
    serviceEdge st a b ↔ ∃ svc, lookupService st a = some svc ∧ b ∈ svc.dependencies := by
  rfl  -- or: simp [serviceEdge]
```

### 2.2 Path composition

```lean
/-- Reachability is transitive: paths compose by concatenation. -/
theorem serviceReachable_trans (st : SystemState) (a b c : ServiceId)
    (hab : serviceReachable st a b) (hbc : serviceReachable st b c) :
    serviceReachable st a c := by
  induction hab with
  | refl => exact hbc
  | step hedge _ ih => exact .step hedge (ih hbc)
```

**Tactic explanation:** Induction on the first reachability proof. The `refl` case is trivial. The `step` case prepends the edge to the composed path.

### 2.3 Single-edge and right-append

```lean
/-- A single edge is a reachable path. -/
theorem serviceReachable_of_edge (st : SystemState) (a b : ServiceId)
    (h : serviceEdge st a b) :
    serviceReachable st a b :=
  .step h .refl

/-- Append an edge to the right of a reachable path. -/
theorem serviceReachable_step_right (st : SystemState) (a b c : ServiceId)
    (hab : serviceReachable st a b) (hbc : serviceEdge st b c) :
    serviceReachable st a c :=
  serviceReachable_trans st a b c hab (serviceReachable_of_edge st b c hbc)
```

### 2.4 Non-trivial path constructors

```lean
/-- A single edge is a non-trivial path. -/
theorem serviceHasNontrivialPath_of_edge (st : SystemState) (a b : ServiceId)
    (h : serviceEdge st a b) :
    serviceHasNontrivialPath st a b :=
  ⟨b, h, .refl⟩

/-- Extend a non-trivial path with an edge on the right. -/
theorem serviceHasNontrivialPath_trans_edge (st : SystemState) (a b c : ServiceId)
    (hab : serviceHasNontrivialPath st a b) (hbc : serviceEdge st b c) :
    serviceHasNontrivialPath st a c := by
  rcases hab with ⟨mid, hedge, hreach⟩
  exact ⟨mid, hedge, serviceReachable_step_right st mid b c hreach hbc⟩

/-- Construct a non-trivial path from an edge followed by a reachable path. -/
theorem serviceHasNontrivialPath_of_edge_reachable (st : SystemState) (a b c : ServiceId)
    (hab : serviceEdge st a b) (hbc : serviceReachable st b c) :
    serviceHasNontrivialPath st a c :=
  ⟨b, hab, hbc⟩
```

---

## 3. Store-interaction lemmas

These lemmas characterize how `storeServiceState` affects edges and fuel. They wrap the existing `storeServiceState_lookup_eq` and `storeServiceState_lookup_ne` from `State.lean`.

### 3.1 Frame conditions

```lean
/-- storeServiceState does not modify objectIndex. -/
theorem storeServiceState_objectIndex_eq (st : SystemState) (sid : ServiceId)
    (entry : ServiceGraphEntry) :
    (storeServiceState sid entry st).objectIndex = st.objectIndex := by
  simp [storeServiceState]

/-- BFS fuel is unchanged after storeServiceState. -/
theorem serviceBfsFuel_storeServiceState_eq (st : SystemState) (sid : ServiceId)
    (entry : ServiceGraphEntry) :
    serviceBfsFuel (storeServiceState sid entry st) = serviceBfsFuel st := by
  simp [serviceBfsFuel, storeServiceState_objectIndex_eq]
```

### 3.2 Edge relation under store

```lean
/-- At the updated service, edges reflect the new dependency list. -/
theorem serviceEdge_storeServiceState_eq (st : SystemState) (svcId : ServiceId)
    (svc' : ServiceGraphEntry) (b : ServiceId) :
    serviceEdge (storeServiceState svcId svc' st) svcId b ↔ b ∈ svc'.dependencies := by
  simp [serviceEdge, storeServiceState_lookup_eq]

/-- At non-updated services, edges are unchanged. -/
theorem serviceEdge_storeServiceState_ne (st : SystemState) (svcId sid : ServiceId)
    (svc' : ServiceGraphEntry) (b : ServiceId) (hNe : sid ≠ svcId) :
    serviceEdge (storeServiceState svcId svc' st) sid b ↔ serviceEdge st sid b := by
  simp [serviceEdge, storeServiceState_lookup_ne st svcId sid svc' hNe]
```

### 3.3 Edge characterization after specific insertion

```lean
/-- After inserting depId into svcId's dependency list, edges from svcId are exactly
    the old dependencies plus depId. -/
theorem serviceEdge_post_insert (st : SystemState) (svcId depId : ServiceId)
    (svc : ServiceGraphEntry) (b : ServiceId) :
    serviceEdge (storeServiceState svcId { svc with dependencies := svc.dependencies ++ [depId] } st)
      svcId b ↔
    b ∈ svc.dependencies ∨ b = depId := by
  rw [serviceEdge_storeServiceState_eq]
  simp [List.mem_append, List.mem_singleton]
```

---

## 4. Placement guidance

All definitions and lemmas in this milestone should be placed in `SeLe4n/Kernel/Service/Invariant.lean`, in a new section between the existing proof infrastructure (line 340) and the acyclicity invariant definition (line 349):

```
Line 340: end of M5 proof package theorems
-- NEW: TPI-D07 Layer 0 definitions (D1–D4)
-- NEW: TPI-D07 Layer 1 structural lemmas (L1–L7)
-- NEW: TPI-D07 Layer 1 store-interaction lemmas (S1–S5)
Line 349: def serviceDependencyAcyclic ...
```

The store-interaction lemmas S1 and S2 (`storeServiceState_objectIndex_eq`, `serviceBfsFuel_storeServiceState_eq`) could alternatively be placed in `State.lean` alongside the existing store lemmas. Either location works; co-locating in `Invariant.lean` keeps the TPI-D07 proof infrastructure self-contained.

---

## 5. Exit criteria

- [x] `serviceEdge`, `serviceReachable`, `serviceNontrivialPath` defined; `serviceDependencyAcyclic` redefined declaratively (Invariant.lean:381-411)
- [x] 7 structural lemmas compile without `sorry` (Invariant.lean:417-463)
- [x] 3 frame lemmas compile without `sorry` (Invariant.lean:469-508)
- [x] `serviceReachable` supports induction and composition without BFS unfolding
- [x] `serviceEdge_storeServiceState_ne`, `serviceEdge_storeServiceState_updated`, `serviceEdge_post_insert` cover the store pattern
- [x] `lake build` succeeds

> **Implementation note:** Naming diverged from plan: `serviceHasNontrivialPath` → `serviceNontrivialPath` (inductive type); `serviceDependencyAcyclicDecl` not needed separately since `serviceDependencyAcyclic` was redefined in-place.

## Validation

```bash
./scripts/test_tier1_build.sh
```
