/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Registry.Invariant

/-!
# R4-E: Cross-Subsystem Invariant Definitions

Defines cross-subsystem invariants that bridge lifecycle, service registry,
and IPC subsystems. These predicates ensure coherence across kernel subsystem
boundaries when objects are retyped, services are revoked, or queues are
modified.

## Predicates

| Predicate | Description |
|-----------|-------------|
| `noStaleEndpointQueueReferences` | Every ThreadId in an endpoint head/tail has a live TCB |
| `registryDependencyConsistent` | Every dependency graph edge references a registered service |
| `crossSubsystemInvariant` | Composed bundle of all cross-subsystem predicates |
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- R4-E.1: No endpoint queue head/tail references a non-existent TCB.
    For every endpoint object, if its sendQ or receiveQ head or tail
    contains a ThreadId, then a TCB with that ThreadId must exist in
    the objects store. -/
def noStaleEndpointQueueReferences (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[oid]? = some (.endpoint ep) →
    (∀ tid, ep.sendQ.head = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, ep.sendQ.tail = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, ep.receiveQ.head = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, ep.receiveQ.tail = some tid → st.objects[tid.toObjId]? ≠ none)

/-- R4-E.1: Every dependency graph edge references services that are
    still registered in the service registry. -/
def registryDependencyConsistent (st : SystemState) : Prop :=
  ∀ (sid : ServiceId) (entry : ServiceGraphEntry),
    st.services[sid]? = some entry →
    ∀ dep, dep ∈ entry.dependencies →
      st.services[dep]? ≠ none

/-- R4-E.1: Cross-subsystem invariant composing registry endpoint validity,
    dependency consistency, and stale queue reference exclusion.
    Checked at every kernel entry/exit point via `proofLayerInvariantBundle`. -/
def crossSubsystemInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧
  registryDependencyConsistent st ∧
  noStaleEndpointQueueReferences st

/-- R4-E.1: The default state satisfies crossSubsystemInvariant. -/
theorem default_crossSubsystemInvariant :
    crossSubsystemInvariant (default : SystemState) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (default_registryInvariant).1
  · intro sid entry h
    simp only [RHTable_getElem?_eq_get?] at h
    have : (default : SystemState).services.get? sid = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) sid
    simp [this] at h
  · intro oid ep h
    simp only [RHTable_getElem?_eq_get?] at h
    have : (default : SystemState).objects.get? oid = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) oid
    simp [this] at h

-- ============================================================================
-- S3-J/U-M26: Parameterized cross-subsystem invariant composition
-- ============================================================================

/-- S3-J: List of cross-subsystem invariant predicates. Adding a new subsystem
    invariant requires only extending this list rather than editing a fixed
    conjunction. The `crossSubsystemInvariant` definition above remains the
    canonical form for backward compatibility; this list provides the
    parameterized composition used by extensibility checks. -/
def crossSubsystemPredicates : List (SystemState → Prop) :=
  [registryEndpointValid, registryDependencyConsistent, noStaleEndpointQueueReferences]

/-- S3-J: Folded composition — the cross-subsystem invariant is equivalent to
    every predicate in the list holding on the state. -/
def crossSubsystemInvariantFolded (st : SystemState) : Prop :=
  ∀ p, p ∈ crossSubsystemPredicates → p st

/-- S3-J: The folded composition is equivalent to the fixed conjunction.
    This theorem ensures backward compatibility: callers can use either form. -/
theorem crossSubsystemInvariant_iff_folded (st : SystemState) :
    crossSubsystemInvariant st ↔ crossSubsystemInvariantFolded st := by
  constructor
  · intro ⟨h₁, h₂, h₃⟩ p hMem
    simp [crossSubsystemPredicates] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  · intro hAll
    exact ⟨hAll _ (by simp [crossSubsystemPredicates]),
           hAll _ (by simp [crossSubsystemPredicates]),
           hAll _ (by simp [crossSubsystemPredicates])⟩

/-- S3-J: Predicate count witness — compile-time assertion that the predicate
    list has exactly 3 entries. If a new subsystem invariant is added to the list
    but not to `crossSubsystemInvariant`, the count check will fail. -/
theorem crossSubsystemPredicates_count :
    crossSubsystemPredicates.length = 3 := by rfl

end SeLe4n.Kernel
