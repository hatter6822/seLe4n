/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Registry.Invariant
import SeLe4n.Kernel.Service.Invariant.Acyclicity

/-!
# R4-E: Cross-Subsystem Invariant Definitions

Defines cross-subsystem invariants that bridge lifecycle, service registry,
and IPC subsystems. These predicates ensure coherence across kernel subsystem
boundaries when objects are retyped, services are revoked, or queues are
modified.

## Predicates

| Predicate | Description |
|-----------|-------------|
| `noStaleEndpointQueueReferences` | Every ThreadId in an endpoint queue (head/tail + interior) has a live TCB |
| `noStaleNotificationWaitReferences` | Every ThreadId in a notification wait list has a live TCB (T5-H) |
| `registryDependencyConsistent` | Every dependency graph edge references a registered service |
| `serviceGraphInvariant` | Service dependency acyclicity + count bound (U4-G) |
| `crossSubsystemInvariant` | Composed bundle of all cross-subsystem predicates |
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- T5-I helper: Collect all ThreadIds reachable via `queueNext` from a starting
    thread, with bounded fuel to ensure termination. Returns the list of valid
    ThreadIds encountered during traversal.
    Takes the objects table directly (not SystemState) to ensure the predicate
    is independent of non-object state fields (machine, scheduler, etc.). -/
private def collectQueueMembers
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (start : Option SeLe4n.ThreadId)
    (fuel : Nat) : List SeLe4n.ThreadId :=
  match fuel, start with
  | 0, _ => []
  | _, none => []
  | fuel + 1, some tid =>
    match objects[tid.toObjId]? with
    | some (.tcb tcb) => tid :: collectQueueMembers objects tcb.queueNext fuel
    | _ => [tid]  -- tid exists but not a TCB (should not happen in well-formed state)

/-- R4-E.1 + T5-I (M-CS-1): No endpoint queue references a non-existent TCB.
    For every endpoint object, every ThreadId reachable via the intrusive
    `queueNext` chain from the queue head must reference an existing TCB
    in the objects store. This extends the original head/tail-only check
    to cover interior queue members as well.

    The traversal is bounded by `st.objects.size` (the maximum number of
    distinct TCBs), ensuring termination. -/
def noStaleEndpointQueueReferences (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[oid]? = some (.endpoint ep) →
    -- Head/tail validity (original R4-E.1)
    (∀ tid, ep.sendQ.head = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, ep.sendQ.tail = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, ep.receiveQ.head = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, ep.receiveQ.tail = some tid → st.objects[tid.toObjId]? ≠ none) ∧
    -- T5-I: Interior member validity
    (∀ tid, tid ∈ collectQueueMembers st.objects ep.sendQ.head st.objects.size →
      st.objects[tid.toObjId]? ≠ none) ∧
    (∀ tid, tid ∈ collectQueueMembers st.objects ep.receiveQ.head st.objects.size →
      st.objects[tid.toObjId]? ≠ none)

/-- T5-H (L-NEW-3): No notification waiting list references a non-existent TCB.
    For every notification object, every `ThreadId` in `waitingThreads`
    must reference an existing TCB in the objects store. This prevents
    deleted TCB IDs from persisting in notification wait lists. -/
def noStaleNotificationWaitReferences (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (notif : Notification),
    st.objects[oid]? = some (.notification notif) →
    ∀ tid, tid ∈ notif.waitingThreads →
      st.objects[tid.toObjId]? ≠ none

/-- R4-E.1: Every dependency graph edge references services that are
    still registered in the service registry. -/
def registryDependencyConsistent (st : SystemState) : Prop :=
  ∀ (sid : ServiceId) (entry : ServiceGraphEntry),
    st.services[sid]? = some entry →
    ∀ dep, dep ∈ entry.dependencies →
      st.services[dep]? ≠ none

/-- R4-E.1 + T5-J + U4-G: Cross-subsystem invariant composing registry endpoint
    validity, dependency consistency, stale queue reference exclusion,
    notification wait-list reference validity, and service graph acyclicity.
    Checked at every kernel entry/exit point via `proofLayerInvariantBundle`.

    U6-L (U-M14): **Cross-subsystem invariant composition gap**. This
    invariant is the conjunction of 5 subsystem predicates. The conjunction
    may not be the strongest composite invariant — there may exist cross-
    subsystem interference properties that are not captured by the individual
    predicates. For example:

    - An IPC operation that modifies an endpoint queue may affect service
      registry consistency if the endpoint is a service's bound endpoint.
    - A capability revocation that removes a CNode slot may invalidate a
      service's registered endpoint capability.

    Currently, each subsystem's preservation proofs discharge their own
    invariant independently. Cross-subsystem interference is handled by
    ensuring that operations in one subsystem do not modify fields read by
    another subsystem's invariant predicates (field-disjointness argument).

    Future work (WS-V): Formally verify that the conjunction is tight —
    either prove that no cross-subsystem interference exists beyond what
    the individual predicates capture, or strengthen the conjunction with
    additional cross-cutting properties. -/
def crossSubsystemInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧
  registryDependencyConsistent st ∧
  noStaleEndpointQueueReferences st ∧
  noStaleNotificationWaitReferences st ∧
  serviceGraphInvariant st

/-- R4-E.1 + T5-J + U4-G: The default state satisfies crossSubsystemInvariant. -/
theorem default_crossSubsystemInvariant :
    crossSubsystemInvariant (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · -- T5-H: noStaleNotificationWaitReferences — vacuously true for empty objects
    intro oid notif h
    simp only [RHTable_getElem?_eq_get?] at h
    have : (default : SystemState).objects.get? oid = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) oid
    simp [this] at h
  · -- U4-G: serviceGraphInvariant — default state has empty services
    exact default_serviceGraphInvariant

-- ============================================================================
-- S3-J/U-M26: Parameterized cross-subsystem invariant composition
-- ============================================================================

/-- S3-J: List of cross-subsystem invariant predicates. Adding a new subsystem
    invariant requires only extending this list rather than editing a fixed
    conjunction. The `crossSubsystemInvariant` definition above remains the
    canonical form for backward compatibility; this list provides the
    parameterized composition used by extensibility checks. -/
def crossSubsystemPredicates : List (SystemState → Prop) :=
  [registryEndpointValid, registryDependencyConsistent, noStaleEndpointQueueReferences,
   noStaleNotificationWaitReferences, serviceGraphInvariant]

/-- S3-J: Folded composition — the cross-subsystem invariant is equivalent to
    every predicate in the list holding on the state. -/
def crossSubsystemInvariantFolded (st : SystemState) : Prop :=
  ∀ p, p ∈ crossSubsystemPredicates → p st

/-- S3-J: The folded composition is equivalent to the fixed conjunction.
    This theorem ensures backward compatibility: callers can use either form. -/
theorem crossSubsystemInvariant_iff_folded (st : SystemState) :
    crossSubsystemInvariant st ↔ crossSubsystemInvariantFolded st := by
  constructor
  · intro ⟨h₁, h₂, h₃, h₄, h₅⟩ p hMem
    simp [crossSubsystemPredicates] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
    · exact h₅
  · intro hAll
    exact ⟨hAll _ (by simp [crossSubsystemPredicates]),
           hAll _ (by simp [crossSubsystemPredicates]),
           hAll _ (by simp [crossSubsystemPredicates]),
           hAll _ (by simp [crossSubsystemPredicates]),
           hAll _ (by simp [crossSubsystemPredicates])⟩

/-- S3-J + T5-J + U4-G: Predicate count witness — compile-time assertion that the
    predicate list has exactly 5 entries (extended from 4 by U4-G serviceGraphInvariant).
    If a new subsystem invariant is added to the list but not to
    `crossSubsystemInvariant`, the count check will fail. -/
theorem crossSubsystemPredicates_count :
    crossSubsystemPredicates.length = 5 := by rfl

end SeLe4n.Kernel
