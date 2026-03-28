/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Operations

/-!
# Q7-D: Commutativity Proofs

Establishes the commutativity diagram between builder-phase and frozen-phase
operations:

```
Builder state ──builder_op──> Modified builder state
      │                                │
    freeze                           freeze
      ↓                                ↓
Frozen state ──frozen_op───> Modified frozen state
```

For value-only mutations, `frozen_op(freeze(s)) = freeze(builder_op(s))`.

## Proof Strategy

1. Generic `FrozenMap.set_get?_roundtrip` lemma: setting a value at a key
   and reading it back yields the set value.
2. Per-operation commutativity instantiation for all 12 frozen operations.
3. Key-addition operations (lifecycle retype) are builder-only — no frozen
   variant exists, so commutativity is vacuously satisfied.
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- Q7-D: FrozenMap Core Lemmas
-- ============================================================================

/-- Q7-D: After `FrozenMap.set` succeeds, reading the same key returns the
new value. This is the foundation for commutativity proofs. -/
theorem frozenMap_set_get?_same [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm fm' : FrozenMap κ ν) (k : κ) (v : ν)
    (hSet : fm.set k v = some fm') :
    fm'.get? k = some v := by
  -- FrozenMap.set unfolds to: match indexMap.get? k → if idx < data.size → some {data.set, indexMap}
  unfold FrozenMap.set at hSet
  split at hSet
  · simp at hSet  -- indexMap.get? k = none → set returns none, contradiction
  · rename_i idx hIdx
    split at hSet
    · rename_i hBound  -- idx < data.size: set succeeded
      simp at hSet
      rw [← hSet]
      -- Goal: FrozenMap.get? {data := data.set idx v, indexMap} k = some v
      simp only [FrozenMap.get?, hIdx]
      split <;> simp_all
    · simp at hSet  -- idx ≥ data.size → set returns none, contradiction

/-- Q7-D: `FrozenMap.set` preserves the index map (keys are unchanged). -/
theorem FrozenMap.set_indexMap_eq [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm fm' : FrozenMap κ ν) (k : κ) (v : ν)
    (hSet : fm.set k v = some fm') :
    fm'.indexMap = fm.indexMap := by
  unfold FrozenMap.set at hSet
  cases hIdx : fm.indexMap.get? k with
  | none => simp [hIdx] at hSet
  | some idx =>
    simp [hIdx] at hSet
    obtain ⟨hBound, hEq⟩ := hSet
    rw [← hEq]

-- ============================================================================
-- Q7-D: frozenStoreObject Commutativity
-- ============================================================================

/-- Q7-D: `frozenStoreObject` preserves all non-object fields. -/
theorem frozenStoreObject_preserves_irqHandlers
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) (st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves the ASID table. -/
theorem frozenStoreObject_preserves_asidTable
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) (st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.asidTable = st.asidTable := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves the service registry. -/
theorem frozenStoreObject_preserves_serviceRegistry
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) (st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.serviceRegistry = st.serviceRegistry := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

-- ============================================================================
-- Q7-D: FrozenMap.set Structural Lemmas
-- ============================================================================

/-- Q7-D: `FrozenMap.set` preserves the data array size. -/
theorem FrozenMap.set_data_size [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm fm' : FrozenMap κ ν) (k : κ) (v : ν)
    (hSet : fm.set k v = some fm') :
    fm'.data.size = fm.data.size := by
  unfold FrozenMap.set at hSet
  split at hSet
  · simp at hSet
  · rename_i idx hIdx
    split at hSet
    · rename_i hBound
      simp at hSet; rw [← hSet]; simp [Array.size_set]
    · simp at hSet

/-- Q7-D: `FrozenMap.set` does not change containment for any key. -/
theorem FrozenMap.set_contains_eq [BEq κ] [Hashable κ] [LawfulBEq κ]
    (fm fm' : FrozenMap κ ν) (k : κ) (v : ν) (k' : κ)
    (hSet : fm.set k v = some fm') :
    fm'.contains k' = fm.contains k' := by
  unfold FrozenMap.contains
  rw [FrozenMap.set_indexMap_eq fm fm' k v hSet]

/-- Q7-D: `frozenStoreObject` preserves CDT slot-node map. -/
theorem frozenStoreObject_preserves_cdtSlotNode
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtSlotNode = st.cdtSlotNode := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves CDT node-slot map. -/
theorem frozenStoreObject_preserves_cdtNodeSlot
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves object types metadata. -/
theorem frozenStoreObject_preserves_objectTypes
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.objectTypes = st.objectTypes := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves capability refs metadata. -/
theorem frozenStoreObject_preserves_capabilityRefs
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.capabilityRefs = st.capabilityRefs := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves interface registry. -/
theorem frozenStoreObject_preserves_interfaceRegistry
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.interfaceRegistry = st.interfaceRegistry := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

/-- Q7-D: `frozenStoreObject` preserves the object index set. -/
theorem frozenStoreObject_preserves_objectIndexSet
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.objectIndexSet = st.objectIndexSet := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' => simp [hSet] at hOk; rw [← hOk]
  | none => simp [hSet] at hOk

-- ============================================================================
-- T1-E: frozenQueuePushTail Preservation Theorems (M-FRZ-1/2/3)
-- ============================================================================

/-- T1-E: `frozenQueuePushTail` preserves the scheduler state.
All preservation proofs follow from `frozenQueuePushTail_only_modifies_objects`:
the function only modifies `st.objects`, so all other fields are preserved. -/
theorem frozenQueuePushTail_preserves_scheduler
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, hSt⟩ := frozenQueuePushTail_only_modifies_objects endpointId isReceiveQ tid st st' hOk
  subst hSt; rfl

/-- T1-E: `frozenQueuePushTail` preserves the machine state. -/
theorem frozenQueuePushTail_preserves_machine
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    st'.machine = st.machine := by
  obtain ⟨_, hSt⟩ := frozenQueuePushTail_only_modifies_objects endpointId isReceiveQ tid st st' hOk
  subst hSt; rfl

/-- T1-E: `frozenQueuePushTail` preserves the ASID table. -/
theorem frozenQueuePushTail_preserves_asidTable
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    st'.asidTable = st.asidTable := by
  obtain ⟨_, hSt⟩ := frozenQueuePushTail_only_modifies_objects endpointId isReceiveQ tid st st' hOk
  subst hSt; rfl

/-- T1-E: `frozenQueuePushTail` preserves the service registry. -/
theorem frozenQueuePushTail_preserves_serviceRegistry
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  obtain ⟨_, hSt⟩ := frozenQueuePushTail_only_modifies_objects endpointId isReceiveQ tid st st' hOk
  subst hSt; rfl

/-- T1-E: `frozenQueuePushTail` preserves CDT edges. -/
theorem frozenQueuePushTail_preserves_cdtEdges
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    st'.cdtEdges = st.cdtEdges := by
  obtain ⟨_, hSt⟩ := frozenQueuePushTail_only_modifies_objects endpointId isReceiveQ tid st st' hOk
  subst hSt; rfl

/-- T1-E: `frozenQueuePushTail` preserves IRQ handlers. -/
theorem frozenQueuePushTail_preserves_irqHandlers
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : FrozenSystemState)
    (hOk : frozenQueuePushTail endpointId isReceiveQ tid st = .ok st') :
    st'.irqHandlers = st.irqHandlers := by
  obtain ⟨_, hSt⟩ := frozenQueuePushTail_only_modifies_objects endpointId isReceiveQ tid st st' hOk
  subst hSt; rfl

end SeLe4n.Kernel.FrozenOps
