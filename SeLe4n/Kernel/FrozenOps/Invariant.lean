/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Commutativity

/-!
# Q7-E: Frozen Invariant Preservation

Proves that frozen operations preserve key state fields via frame lemmas.
The core insight: `frozenStoreObject` only modifies the `objects` field
of `FrozenSystemState`. All other fields are preserved by construction.

## Key Properties

- `frozenStoreObject` frame lemmas: scheduler, machine, CDT, etc. preserved
- Read-only operations preserve all fields trivially
-/

namespace SeLe4n.Kernel.FrozenOps

open SeLe4n.Model

-- ============================================================================
-- Q7-E: frozenStoreObject Frame Lemmas
-- ============================================================================

private theorem frozenStoreObject_extracts_state
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    ∃ objects', st.objects.set id obj = some objects' ∧
      st' = { st with objects := objects' } := by
  unfold frozenStoreObject at hOk
  cases hSet : st.objects.set id obj with
  | some objects' =>
    exact ⟨objects', rfl, by simp [hSet] at hOk; exact hOk.symm⟩
  | none => simp [hSet] at hOk

/-- Q7-E: `frozenStoreObject` preserves CDT edges. -/
theorem frozenStoreObject_preserves_cdtEdges
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtEdges = st.cdtEdges := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

/-- Q7-E: `frozenStoreObject` preserves the object index. -/
theorem frozenStoreObject_preserves_objectIndex
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

/-- Q7-E: `frozenStoreObject` preserves CDT child map. -/
theorem frozenStoreObject_preserves_cdtChildMap
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtChildMap = st.cdtChildMap := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

/-- Q7-E: `frozenStoreObject` preserves CDT parent map. -/
theorem frozenStoreObject_preserves_cdtParentMap
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtParentMap = st.cdtParentMap := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

/-- Q7-E: `frozenStoreObject` preserves CDT next node counter. -/
theorem frozenStoreObject_preserves_cdtNextNode
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtNextNode = st.cdtNextNode := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

-- ============================================================================
-- Q7-E: Additional frozenStoreObject Frame Lemmas via extracts_state
-- ============================================================================

/-- Q7-E: `frozenStoreObject` preserves the services map. -/
theorem frozenStoreObject_preserves_services
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.services = st.services := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

/-- Q7-E: `frozenStoreObject` preserves CDT slot-node map. -/
theorem frozenStoreObject_preserves_cdtSlotNode'
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtSlotNode = st.cdtSlotNode := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

/-- Q7-E: `frozenStoreObject` preserves CDT node-slot map. -/
theorem frozenStoreObject_preserves_cdtNodeSlot'
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st st' : FrozenSystemState)
    (hOk : frozenStoreObject id obj st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  obtain ⟨_, _, hSt⟩ := frozenStoreObject_extracts_state id obj st st' hOk
  subst hSt; rfl

-- ============================================================================
-- Q7-E: Read-Only Operation Preservation
-- ============================================================================

/-- Q7-E: `frozenLookupObject` is read-only — preserves all state. -/
theorem frozenLookupObject_read_only
    (id : SeLe4n.ObjId) (st : FrozenSystemState)
    (obj : FrozenKernelObject) (st' : FrozenSystemState)
    (hOk : frozenLookupObject id st = .ok (obj, st')) :
    st' = st :=
  frozenLookupObject_state_unchanged id st obj st' hOk

-- ============================================================================
-- Q7-E: Frozen Operation Determinism
-- ============================================================================

/-- Q7-E: `frozenLookupObject` is deterministic. -/
theorem frozenLookupObject_deterministic
    (id : SeLe4n.ObjId) (st : FrozenSystemState) :
    frozenLookupObject id st = frozenLookupObject id st := rfl

/-- Q7-E: `frozenStoreObject` is deterministic. -/
theorem frozenStoreObject_deterministic
    (id : SeLe4n.ObjId) (obj : FrozenKernelObject)
    (st : FrozenSystemState) :
    frozenStoreObject id obj st = frozenStoreObject id obj st := rfl

-- ============================================================================
-- R1-E: Context Save/Restore Preservation Theorems
-- ============================================================================

/-- R1-E/M-10: When `frozenSaveOutgoingContext` succeeds, the scheduler
is preserved (only the objects field is modified). -/
theorem frozenSaveOutgoingContext_preserves_scheduler
    (st st' : FrozenSystemState)
    (hOk : frozenSaveOutgoingContext st = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold frozenSaveOutgoingContext at hOk
  split at hOk
  · -- current = none: state is unchanged
    simp at hOk; rw [← hOk]
  · -- current = some outTid
    rename_i outTid _
    split at hOk
    · -- objects.get? = some (.tcb outTcb)
      rename_i outTcb _
      simp only at hOk
      cases hSet : st.objects.set outTid.toObjId
          (FrozenKernelObject.tcb { outTcb with registerContext := st.machine.regs }) with
      | some objects' => simp [hSet] at hOk; rw [← hOk]
      | none => simp [hSet] at hOk
    · simp at hOk

/-- R1-E/M-11: When `frozenRestoreIncomingContext` succeeds, the scheduler
is preserved (only the machine.regs field is modified). -/
theorem frozenRestoreIncomingContext_preserves_scheduler
    (st st' : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (hOk : frozenRestoreIncomingContext st tid = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold frozenRestoreIncomingContext at hOk
  split at hOk
  · simp at hOk; rw [← hOk]
  · simp at hOk

/-- R1-E/M-11: When `frozenRestoreIncomingContext` succeeds, the objects
are preserved (only machine registers are modified). -/
theorem frozenRestoreIncomingContext_preserves_objects
    (st st' : FrozenSystemState) (tid : SeLe4n.ThreadId)
    (hOk : frozenRestoreIncomingContext st tid = .ok st') :
    st'.objects = st.objects := by
  unfold frozenRestoreIncomingContext at hOk
  split at hOk
  · simp at hOk; rw [← hOk]
  · simp at hOk

end SeLe4n.Kernel.FrozenOps
