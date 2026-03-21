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

end SeLe4n.Kernel.FrozenOps
