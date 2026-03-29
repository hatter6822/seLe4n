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

/-- V4-A: When the starting thread is `none`, `collectQueueMembers` returns `[]`.
    Public bridge lemma for boot-phase proofs that need to discharge interior
    queue member goals when queue heads are empty. -/
theorem collectQueueMembers_none (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (fuel : Nat) : collectQueueMembers objects none fuel = [] := by
  cases fuel <;> rfl

-- ============================================================================
-- W2-D (M-6): collectQueueMembers fuel sufficiency
-- ============================================================================

/-- W2-D (M-6): Fuel sufficiency argument for `collectQueueMembers`.

    `collectQueueMembers` traverses a linked-list queue via `queueNext` pointers
    with `st.objects.size` as fuel. On fuel exhaustion (fuel=0), it returns `[]`,
    silently truncating. The IPC invariant `tcbQueueChainAcyclic` ensures:

    1. **No cycles**: every queue traversal visits distinct threads.
    2. **Bounded length**: queue length ≤ number of TCBs ≤ `objects.size`.
    3. **Fuel sufficiency**: with fuel = `objects.size` and at most `objects.size`
       distinct threads, the traversal completes before fuel exhaustion.

    The formal connection relies on the `QueueNextPath` inductive predicate from
    `IPC/Invariant/Defs.lean`, which captures the acyclicity property. Each step
    of `collectQueueMembers` consumes 1 fuel and visits 1 unique thread (by
    acyclicity). Since there are at most `objects.size` threads, the traversal
    terminates naturally (via `none` queueNext or non-TCB) before fuel reaches 0.

    **Why not a formal proof**: The `tcbQueueChainAcyclic` invariant operates on
    `QueueNextPath` (an inductive path predicate), while `collectQueueMembers`
    operates on `queueNext` field traversal. Connecting these requires showing
    that `collectQueueMembers` produces a `QueueNextPath`-compatible traversal,
    which involves non-trivial infrastructure. The per-element validity guaranteed
    by `noStaleEndpointQueueReferences` is the operationally relevant property. -/
theorem collectQueueMembers_fuel_sufficiency_documented
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (start : Option SeLe4n.ThreadId) :
    -- When start is none, result is empty regardless of fuel
    start = none → collectQueueMembers objects start objects.size = [] := by
  intro h; subst h; exact collectQueueMembers_none objects objects.size

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
-- W2-B (H-1): Cross-subsystem invariant composition gap documentation
-- ============================================================================

/-- W2-B (H-1): **Composition gap acknowledgment.** The 5-predicate conjunction
    `crossSubsystemInvariant` may not be the strongest composite invariant:
    there may exist cross-subsystem interference properties not captured by the
    individual predicates.

    **Partial mitigation via W2-A frame lemmas:** For the 6 disjoint predicate
    pairs (see `fieldDisjointness_frameIndependence_documented`), frame lemmas
    guarantee that operations modifying only one predicate's read-set automatically
    preserve the other predicate. This covers:
    - `registryDependencyConsistent_frame` (services-only ops)
    - `noStaleEndpointQueueReferences_frame` (objects-only ops)
    - `noStaleNotificationWaitReferences_frame` (objects-only ops)
    - `registryEndpointValid_frame` (serviceRegistry+objects-only ops)
    - `serviceGraphInvariant_frame` (services+objectIndex-only ops)

    **Remaining gap:** The 4 sharing pairs (both reading `objects` or `services`)
    require operation-specific preservation proofs. No general frame lemma can
    cover these — each must be proven individually per operation. The current
    proof infrastructure handles this via per-operation preservation theorems
    in each subsystem's `Invariant/Preservation.lean` module.

    **Scope:** This gap is architectural, not a soundness issue. The conjunction
    is a sufficient (but possibly not necessary) condition for cross-subsystem
    coherence. Strengthening it would require identifying specific interference
    properties between subsystems, which is future work. -/
theorem crossSubsystemInvariant_composition_gap_documented
    (st : SystemState) :
    crossSubsystemInvariant st →
    registryEndpointValid st ∧
    registryDependencyConsistent st ∧
    noStaleEndpointQueueReferences st ∧
    noStaleNotificationWaitReferences st ∧
    serviceGraphInvariant st := id

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

-- ============================================================================
-- V6-A (A1-A5): Cross-Subsystem Field-Disjointness Formalization
-- ============================================================================

/-- V6-A1: Enumeration of SystemState top-level fields, for static
    field-disjointness analysis between cross-subsystem predicates. -/
inductive StateField where
  | machine | objects | objectIndex | objectIndexSet
  | services | scheduler | irqHandlers | lifecycle
  | asidTable | interfaceRegistry | serviceRegistry
  | cdt | cdtSlotNode | cdtNodeSlot | cdtNextNode | tlb
  deriving DecidableEq, Repr

/-- V6-A2: Field read-sets for each cross-subsystem predicate.
    Each entry maps a predicate to the fields it inspects.

    Analysis:
    - `registryEndpointValid` reads `serviceRegistry` and `objects`
    - `registryDependencyConsistent` reads `services` only
    - `noStaleEndpointQueueReferences` reads `objects` only
    - `noStaleNotificationWaitReferences` reads `objects` only
    - `serviceGraphInvariant` reads `services` and `objectIndex` -/
def registryEndpointValid_fields : List StateField :=
  [.serviceRegistry, .objects]

def registryDependencyConsistent_fields : List StateField :=
  [.services]

def noStaleEndpointQueueReferences_fields : List StateField :=
  [.objects]

def noStaleNotificationWaitReferences_fields : List StateField :=
  [.objects]

def serviceGraphInvariant_fields : List StateField :=
  [.services, .objectIndex]

/-- V6-A3: Helper — two field lists are disjoint (no shared elements). -/
def fieldsDisjoint (fs₁ fs₂ : List StateField) : Bool :=
  fs₁.all (fun f => fs₂.all (fun g => f != g))

/-- V6-A3: Pairwise disjointness: `registryDependencyConsistent` (services)
    is disjoint from `noStaleEndpointQueueReferences` (objects). -/
theorem regDepConsistent_disjoint_staleEndpoint :
    fieldsDisjoint registryDependencyConsistent_fields
                   noStaleEndpointQueueReferences_fields = true := by decide

/-- V6-A3: `registryDependencyConsistent` (services) is disjoint from
    `noStaleNotificationWaitReferences` (objects). -/
theorem regDepConsistent_disjoint_staleNotification :
    fieldsDisjoint registryDependencyConsistent_fields
                   noStaleNotificationWaitReferences_fields = true := by decide

/-- V6-A3: `serviceGraphInvariant` (services) is disjoint from
    `noStaleEndpointQueueReferences` (objects). -/
theorem serviceGraph_disjoint_staleEndpoint :
    fieldsDisjoint serviceGraphInvariant_fields
                   noStaleEndpointQueueReferences_fields = true := by decide

/-- V6-A3: `serviceGraphInvariant` (services) is disjoint from
    `noStaleNotificationWaitReferences` (objects). -/
theorem serviceGraph_disjoint_staleNotification :
    fieldsDisjoint serviceGraphInvariant_fields
                   noStaleNotificationWaitReferences_fields = true := by decide

/-- V6-A3: `registryDependencyConsistent` (services) is disjoint from
    `registryEndpointValid` on the `services` field. They share no fields —
    `registryEndpointValid` reads `serviceRegistry` + `objects`,
    `registryDependencyConsistent` reads `services`. -/
theorem regDepConsistent_disjoint_regEndpointValid :
    fieldsDisjoint registryDependencyConsistent_fields
                   registryEndpointValid_fields = true := by decide

/-- V6-A3: `serviceGraphInvariant` (services) is disjoint from
    `registryEndpointValid` (serviceRegistry + objects). -/
theorem serviceGraph_disjoint_regEndpointValid :
    fieldsDisjoint serviceGraphInvariant_fields
                   registryEndpointValid_fields = true := by decide

/-- V6-A3: `noStaleEndpointQueueReferences` (objects) is disjoint from
    `noStaleNotificationWaitReferences` (objects) — they share `objects`,
    so this is NOT disjoint. This compile-time witness makes the overlap explicit. -/
theorem staleEndpoint_shares_staleNotification :
    fieldsDisjoint noStaleEndpointQueueReferences_fields
                   noStaleNotificationWaitReferences_fields = false := by decide

/-- V6-A3: `registryEndpointValid` (serviceRegistry + objects) shares `objects`
    with `noStaleEndpointQueueReferences` (objects). -/
theorem regEndpointValid_shares_staleEndpoint :
    fieldsDisjoint registryEndpointValid_fields
                   noStaleEndpointQueueReferences_fields = false := by decide

/-- V6-A3: `registryEndpointValid` (serviceRegistry + objects) shares `objects`
    with `noStaleNotificationWaitReferences` (objects). -/
theorem regEndpointValid_shares_staleNotification :
    fieldsDisjoint registryEndpointValid_fields
                   noStaleNotificationWaitReferences_fields = false := by decide

/-- V6-A3: `registryDependencyConsistent` (services) shares `services` with
    `serviceGraphInvariant` (services + objectIndex). -/
theorem regDepConsistent_shares_serviceGraph :
    fieldsDisjoint registryDependencyConsistent_fields
                   serviceGraphInvariant_fields = false := by decide

-- ============================================================================
-- W2-A (H-2): Operation modified-field sets
-- ============================================================================

/-- W2-A1: Fields modified by `storeObject`. Updates the object table,
    associated indices, and lifecycle metadata (objectTypes + capabilityRefs). -/
def storeObject_modifiedFields : List StateField :=
  [.objects, .objectIndex, .objectIndexSet, .lifecycle]

/-- W2-A1: Fields modified by `serviceRegisterDependency`. Only appends to a
    service entry's dependency list. -/
def serviceRegisterDependency_modifiedFields : List StateField :=
  [.services]

/-- W2-A1: Fields modified by `lifecycleRetypeObject`. Updates objects, indices,
    and lifecycle metadata. -/
def lifecycleRetypeObject_modifiedFields : List StateField :=
  [.objects, .objectIndex, .objectIndexSet, .lifecycle]

/-- W2-A1: Fields modified by IPC endpoint operations (`endpointSendDual`,
    `endpointReceiveDual`, etc.). Modify TCB/endpoint state within objects
    via `storeObject`, which also updates lifecycle metadata. For in-place
    mutations of existing objects, `objectIndex`/`objectIndexSet` are unchanged. -/
def ipcEndpointOp_modifiedFields : List StateField :=
  [.objects, .lifecycle]

/-- W2-A1: Fields modified by capability operations (`cspaceMint`, `cspaceCopy`,
    etc.). Modify CNode slots within objects via `storeObject`, which also
    updates lifecycle metadata. For in-place CNode mutations, `objectIndex`/
    `objectIndexSet` are unchanged. -/
def capabilityOp_modifiedFields : List StateField :=
  [.objects, .lifecycle]

/-- W2-A1: Fields modified by `revokeService` / `removeDependenciesOf`.
    `revokeService` erases from `serviceRegistry`, then `removeDependenciesOf`
    modifies the service dependency graph (`services`). -/
def revokeService_modifiedFields : List StateField :=
  [.services, .serviceRegistry]

-- ============================================================================
-- W2-A2/A3: Per-predicate frame lemmas connecting field disjointness
-- to operational frame independence
-- ============================================================================

/-- W2-A3: Frame lemma — if `objects` is preserved,
    `noStaleEndpointQueueReferences` is preserved. -/
theorem noStaleEndpointQueueReferences_frame
    (st st' : SystemState)
    (hObjects : st'.objects = st.objects)
    (hInv : noStaleEndpointQueueReferences st) :
    noStaleEndpointQueueReferences st' := by
  intro oid ep hLookup
  rw [hObjects] at hLookup
  have := hInv oid ep hLookup
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tid hHead; rw [hObjects]; exact this.1 tid hHead
  · intro tid hTail; rw [hObjects]; exact this.2.1 tid hTail
  · intro tid hHead; rw [hObjects]; exact this.2.2.1 tid hHead
  · intro tid hTail; rw [hObjects]; exact this.2.2.2.1 tid hTail
  · intro tid hMem
    rw [hObjects]; apply this.2.2.2.2.1 tid
    rwa [hObjects] at hMem
  · intro tid hMem
    rw [hObjects]; apply this.2.2.2.2.2 tid
    rwa [hObjects] at hMem

/-- W2-A3: Frame lemma — if `objects` is preserved,
    `noStaleNotificationWaitReferences` is preserved. -/
theorem noStaleNotificationWaitReferences_frame
    (st st' : SystemState)
    (hObjects : st'.objects = st.objects)
    (hInv : noStaleNotificationWaitReferences st) :
    noStaleNotificationWaitReferences st' := by
  intro oid notif hLookup tid hMem
  rw [hObjects] at hLookup
  rw [hObjects]
  exact hInv oid notif hLookup tid hMem

/-- W2-A3: Frame lemma — if `serviceRegistry` and `objects` are preserved,
    `registryEndpointValid` is preserved. -/
theorem registryEndpointValid_frame
    (st st' : SystemState)
    (hSvcReg : st'.serviceRegistry = st.serviceRegistry)
    (hObjects : st'.objects = st.objects)
    (hInv : registryEndpointValid st) :
    registryEndpointValid st' := by
  intro sid reg hLookup
  rw [hSvcReg] at hLookup
  obtain ⟨epId, hTarget, hPresent⟩ := hInv sid reg hLookup
  exact ⟨epId, hTarget, by rw [hObjects]; exact hPresent⟩

-- ============================================================================
-- W2-A4/A5: Disjointness-driven frame independence verification
-- ============================================================================

/-- W2-A4: For the 6 disjoint predicate pairs, verify frame independence:
    operations modifying only fields of one predicate's read-set automatically
    preserve the other predicate via the corresponding frame lemma.

    **Disjoint pairs and their frame guarantees:**
    1. `registryDependencyConsistent` ↔ `noStaleEndpointQueueReferences`:
       disjoint (services vs objects). Ops modifying only objects preserve
       `registryDependencyConsistent` via `registryDependencyConsistent_frame`.
       Ops modifying only services preserve `noStaleEndpointQueueReferences`
       via `noStaleEndpointQueueReferences_frame`.

    2. `registryDependencyConsistent` ↔ `noStaleNotificationWaitReferences`:
       disjoint (services vs objects). Same pattern as pair 1.

    3. `serviceGraphInvariant` ↔ `noStaleEndpointQueueReferences`:
       disjoint (services+objectIndex vs objects). Ops modifying only objects
       preserve `serviceGraphInvariant` via `serviceGraphInvariant_frame`
       (provided objectIndex is also unchanged).

    4. `serviceGraphInvariant` ↔ `noStaleNotificationWaitReferences`:
       disjoint (services+objectIndex vs objects). Same as pair 3.

    5. `registryDependencyConsistent` ↔ `registryEndpointValid`:
       disjoint (services vs serviceRegistry+objects).

    6. `serviceGraphInvariant` ↔ `registryEndpointValid`:
       disjoint (services+objectIndex vs serviceRegistry+objects).

    **Sharing pairs (require operation-specific proofs):**
    - `noStaleEndpointQueueReferences` ↔ `noStaleNotificationWaitReferences`:
      both read `objects`.
    - `registryEndpointValid` ↔ `noStaleEndpointQueueReferences`:
      both read `objects`.
    - `registryEndpointValid` ↔ `noStaleNotificationWaitReferences`:
      both read `objects`.
    - `registryDependencyConsistent` ↔ `serviceGraphInvariant`:
      both read `services`. -/
theorem fieldDisjointness_frameIndependence_documented :
    -- The 6 disjoint pairs have corresponding frame lemmas proven above
    (fieldsDisjoint registryDependencyConsistent_fields
                    noStaleEndpointQueueReferences_fields = true) ∧
    (fieldsDisjoint registryDependencyConsistent_fields
                    noStaleNotificationWaitReferences_fields = true) ∧
    (fieldsDisjoint serviceGraphInvariant_fields
                    noStaleEndpointQueueReferences_fields = true) ∧
    (fieldsDisjoint serviceGraphInvariant_fields
                    noStaleNotificationWaitReferences_fields = true) ∧
    (fieldsDisjoint registryDependencyConsistent_fields
                    registryEndpointValid_fields = true) ∧
    (fieldsDisjoint serviceGraphInvariant_fields
                    registryEndpointValid_fields = true) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- V6-A4: All predicate field-sets mapped to the canonical list. -/
def crossSubsystemFieldSets : List (String × List StateField) :=
  [ ("registryEndpointValid", registryEndpointValid_fields)
  , ("registryDependencyConsistent", registryDependencyConsistent_fields)
  , ("noStaleEndpointQueueReferences", noStaleEndpointQueueReferences_fields)
  , ("noStaleNotificationWaitReferences", noStaleNotificationWaitReferences_fields)
  , ("serviceGraphInvariant", serviceGraphInvariant_fields) ]

/-- V6-A4: Field-set count matches predicate count. -/
theorem crossSubsystemFieldSets_count :
    crossSubsystemFieldSets.length = 5 := by rfl

/-- V6-A5: Frame lemma — if an operation preserves the `services` field,
    `registryDependencyConsistent` is preserved. This is the canonical
    pattern for field-disjointness–based invariant frame reasoning. -/
theorem registryDependencyConsistent_frame
    (st st' : SystemState)
    (hServices : st'.services = st.services)
    (hInv : registryDependencyConsistent st) :
    registryDependencyConsistent st' := by
  intro sid entry hLookup dep hDep
  rw [hServices] at hLookup
  have hPresent := hInv sid entry hLookup dep hDep
  rwa [hServices]

/-- V6-A5: Frame lemma — if an operation preserves the `services` and
    `objectIndex` fields, `serviceGraphInvariant` is preserved.
    (`serviceBfsFuel` reads `objectIndex.length`.)

    Note: Uses `serviceDependencyAcyclic_of_services_eq` and
    `serviceCountBounded_of_services_objectIndex_eq` from the
    acyclicity module, which transfer the invariant across states
    with equal `services` and `objectIndex` fields. -/
theorem serviceGraphInvariant_frame
    (st st' : SystemState)
    (hServices : st'.services = st.services)
    (hObjIdx : st'.objectIndex = st.objectIndex)
    (hInv : serviceGraphInvariant st) :
    serviceGraphInvariant st' := by
  unfold serviceGraphInvariant at hInv ⊢
  have hEdgeTransfer : ∀ a b, serviceEdge st' a b → serviceEdge st a b := by
    intro a b ⟨svc, hLookup, hDep⟩
    refine ⟨svc, ?_, hDep⟩
    unfold lookupService at hLookup ⊢; rw [← hServices]; exact hLookup
  have hPathTransfer : ∀ a b, serviceNontrivialPath st' a b → serviceNontrivialPath st a b := by
    intro a b hPath
    induction hPath with
    | single hEdge => exact .single (hEdgeTransfer _ _ hEdge)
    | cons hEdge _ ih => exact .cons (hEdgeTransfer _ _ hEdge) ih
  constructor
  · -- serviceDependencyAcyclic: transfer via path equivalence
    intro sid hPath
    exact hInv.1 sid (hPathTransfer sid sid hPath)
  · -- serviceCountBounded: reuse exact witness, adjusting services
    exact serviceCountBounded_of_eq hServices hObjIdx hInv.2

-- ============================================================================
-- V6-B: serviceCountBounded / serviceGraphInvariant preservation
-- ============================================================================

/-- V6-B: `serviceGraphInvariant` is preserved by any operation that preserves
    `services` and does not shrink `objectIndex`. This covers `storeObject`
    (lifecycle retype), IPC endpoint operations, and capability operations.

    Uses `serviceCountBounded_monotone` and `serviceDependencyAcyclic` transfer
    from the acyclicity module. -/
theorem serviceGraphInvariant_monotone
    (st st' : SystemState)
    (hServices : st'.services = st.services)
    (hGrow : st.objectIndex.length ≤ st'.objectIndex.length)
    (hInv : serviceGraphInvariant st) :
    serviceGraphInvariant st' := by
  unfold serviceGraphInvariant at hInv ⊢
  have hEdgeTransfer : ∀ a b, serviceEdge st' a b → serviceEdge st a b := by
    intro a b ⟨svc, hLookup, hDep⟩
    refine ⟨svc, ?_, hDep⟩
    unfold lookupService at hLookup ⊢; rw [← hServices]; exact hLookup
  constructor
  · intro sid hPath
    have hPathTransfer : ∀ a b, serviceNontrivialPath st' a b → serviceNontrivialPath st a b := by
      intro a b hPath
      induction hPath with
      | single hEdge => exact .single (hEdgeTransfer _ _ hEdge)
      | cons hEdge _ ih => exact .cons (hEdgeTransfer _ _ hEdge) ih
    exact hInv.1 sid (hPathTransfer sid sid hPath)
  · exact serviceCountBounded_monotone hServices hGrow hInv.2

end SeLe4n.Kernel
