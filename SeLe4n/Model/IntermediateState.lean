/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# Q3-A: IntermediateState — Builder-Phase State with Invariant Witnesses

`IntermediateState` wraps `SystemState` and carries machine-checked proofs that
all Robin Hood hash tables satisfy the extended invariant (`invExt`), per-object
structural invariants hold (CNode `slotsUnique`, VSpaceRoot `mappings.invExt`),
and lifecycle metadata is consistent.

This is the formal foundation for the two-phase boot model: builder operations
construct an `IntermediateState` from `IntermediateState.empty` via a sequence
of `Builder.*` calls, each of which preserves all four invariant witnesses.

## Design

`IntermediateState` is a **wrapper**, not a new state type. All kernel
operations continue to work on `SystemState`; the builder wrappers simply carry
the proofs forward. This avoids duplicating kernel transition logic and ensures
that the frozen execution phase (Q5) can extract the inner `SystemState`.
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

/-- Q3-A: Per-object CNode slot invariant: every CNode in the object store
satisfies `slotsUnique`. -/
def perObjectSlotsInvariant (st : SystemState) : Prop :=
  ∀ (id : SeLe4n.ObjId) (cn : CNode),
    st.objects[id]? = some (KernelObject.cnode cn) → cn.slotsUnique

/-- Q3-A: Per-object VSpaceRoot mapping invariant: every VSpaceRoot in the
object store has `mappings.invExt`. -/
def perObjectMappingsInvariant (st : SystemState) : Prop :=
  ∀ (id : SeLe4n.ObjId) (vs : VSpaceRoot),
    st.objects[id]? = some (KernelObject.vspaceRoot vs) → vs.mappings.invExt

/-- Q3-A: Builder-phase state: all maps verified, all invariants carried.

The four proof fields guarantee:
1. **`hAllTables`** — every RHTable/RHSet in `SystemState` satisfies `invExt`
   (WF ∧ distCorrect ∧ noDupKeys ∧ probeChainDominant).
2. **`hPerObjectSlots`** — for every CNode in the object store, its `slots`
   RHTable satisfies `slotsUnique` (invExt ∧ size < capacity ∧ 4 ≤ capacity).
3. **`hPerObjectMappings`** — for every VSpaceRoot in the object store, its
   `mappings` RHTable satisfies `invExt`.
4. **`hLifecycleConsistent`** — lifecycle metadata (objectTypes, capabilityRefs)
   is mutually consistent with the object store. -/
structure IntermediateState where
  state : SystemState
  hAllTables : state.allTablesInvExt
  hPerObjectSlots : perObjectSlotsInvariant state
  hPerObjectMappings : perObjectMappingsInvariant state
  hLifecycleConsistent : SystemState.lifecycleMetadataConsistent state

/-- Q3-A: The empty object store satisfies the per-object CNode slots invariant
(vacuously — no objects exist). -/
theorem perObjectSlotsInvariant_default :
    perObjectSlotsInvariant (default : SystemState) := by
  unfold perObjectSlotsInvariant
  intro id cn h
  have hEmpty : (default : SystemState).objects[id]? = none :=
    RHTable.getElem?_empty _ _ _
  rw [hEmpty] at h; cases h

/-- Q3-A: The empty object store satisfies the per-object VSpaceRoot mappings
invariant (vacuously — no objects exist). -/
theorem perObjectMappingsInvariant_default :
    perObjectMappingsInvariant (default : SystemState) := by
  unfold perObjectMappingsInvariant
  intro id vs h
  have hEmpty : (default : SystemState).objects[id]? = none :=
    RHTable.getElem?_empty _ _ _
  rw [hEmpty] at h; cases h

/-- Q3-A: The default (empty) SystemState yields a valid IntermediateState. -/
def mkEmptyIntermediateState : IntermediateState where
  state := default
  hAllTables := default_allTablesInvExt
  hPerObjectSlots := perObjectSlotsInvariant_default
  hPerObjectMappings := perObjectMappingsInvariant_default
  hLifecycleConsistent := default_systemState_lifecycleConsistent

/-- Q3-A: `mkEmptyIntermediateState` is well-formed. -/
theorem mkEmptyIntermediateState_valid :
    let e := mkEmptyIntermediateState
    e.state.allTablesInvExt ∧
    perObjectSlotsInvariant e.state ∧
    perObjectMappingsInvariant e.state ∧
    SystemState.lifecycleMetadataConsistent e.state :=
  ⟨mkEmptyIntermediateState.hAllTables,
   mkEmptyIntermediateState.hPerObjectSlots,
   mkEmptyIntermediateState.hPerObjectMappings,
   mkEmptyIntermediateState.hLifecycleConsistent⟩

end SeLe4n.Model
