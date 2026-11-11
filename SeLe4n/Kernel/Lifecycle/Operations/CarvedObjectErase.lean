-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.Architecture.PageTeardown
import SeLe4n.Kernel.Architecture.PageTableInstall

/-!
# Erasing a carved object from the store

The store's one erase of a carved memory object — a frame, an untyped, an
address-space root or a page table (`retireCarvedObject`) — with its index row,
its index-set entry, its object-type metadata and, for a root, its ASID-table
entry and the ASID's invalidation.  The final-delete retire runs it on the
object whose last capability a delete or revoke destroyed
(`retireRecordedObject`, `Capability/FinalRetire.lean`), as seL4's `finaliseCap`
frees an object with its last capability; it is the identity on any other kind.

The compiled form erases one table at a time, each write out of line over the
state it is handed (`retireCarvedObject_eq_impl`), so every table is written in
place.  `retireCarvedObject_frame` is what the retire's proofs read: every key
holds what it held, or a carved object that is now absent.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================

/-- **Is the object at `oid` one a carve makes** — a frame, an untyped, since
slice 4b a VSpace root, and since `v0.36.12` a page table? -/
def carvedAt (st : SystemState) (oid : SeLe4n.ObjId) : Prop :=
  (∃ f, st.objects[oid]? = some (KernelObject.frame f)) ∨
    (∃ u, st.objects[oid]? = some (KernelObject.untyped u)) ∨
    (∃ r, st.objects[oid]? = some (KernelObject.vspaceRoot r)) ∨
    (∃ p, st.objects[oid]? = some (KernelObject.pageTable p))

/-- **Erase a carved object — a frame, an untyped, a VSpace root or a page table
— from the object store**, with its index row, its index-set entry and its
object-type metadata.  A no-op at a key holding anything else, so no other kind
of object can be erased through it.  The final-delete retire runs it once the
object's last capability is gone and its finalisation has unmapped and detached
what it held (`retireRecordedObject`): a frame or an untyped is then named only
by its recorder's child list, which the retire updates; a VSpace root is named
besides by its ASID-table entry, which is erased here with its invalidation
recorded, so the root's ASID is free for the next carve; a page table by the
root it was installed in, from which the finalisation detached it. -/
def retireCarvedObject (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  if (st.getFrame? id).isSome || (st.getUntyped? id).isSome ||
      (st.getVSpaceRoot? id).isSome || (st.getPageTable? id).isSome then
    { st with
        objects := st.objects.erase id
        objectIndexGhost := st.objectIndexGhost.map (·.filter (· != id))
        objectIndexSetGhost := st.objectIndexSetGhost.map (·.erase id)
        lifecycle := { objectTypesGhost := st.lifecycle.objectTypesGhost.map (·.erase id) }
        asidTable :=
          match st.getVSpaceRoot? id with
          | some root => st.asidTable.erase root.asid
          | none => st.asidTable
        -- WS-BP BP7.2: a released ASID's translations are invalidated before
        -- the next carve can hand it to a new address space.
        physicalWrites :=
          match st.getVSpaceRoot? id with
          | some root => st.physicalWrites.pushAfter st.physicalWritesDrained
              (SeLe4n.Kernel.Architecture.PhysicalWrite.invalidateAsid root.asid)
          | none => st.physicalWrites
        physicalWritesDrained :=
          match st.getVSpaceRoot? id with
          | some _ => false
          | none => st.physicalWritesDrained }
  else st

/-- The object at `id` erased, with its ghost bookkeeping — its index row, its
index-set entry and its type — out of line, so the state is handed over and its
table written in place.  WS-UC UC2: the bookkeeping is ghost state, so its
writes compute nothing and the table erase is the whole of the compiled work. -/
@[noinline] def withObjectErased (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  { st with
      objects := st.objects.erase id
      objectIndexGhost := st.objectIndexGhost.map (·.filter (· != id))
      objectIndexSetGhost := st.objectIndexSetGhost.map (·.erase id)
      lifecycle := { objectTypesGhost := st.lifecycle.objectTypesGhost.map (·.erase id) } }

open SeLe4n.Kernel.RobinHood in
/-- WS-UC UC2: **the erase keeps the bookkeeping in agreement**: the key leaves
the object table, the index, the index set and the type table together. -/
theorem withObjectErased_preserves_bookkeepingAgrees (st : SystemState) (id : SeLe4n.ObjId)
    (h : st.bookkeepingAgrees) (hInv : st.objects.invExt)
    (hSz : st.objects.size < st.objects.capacity) :
    (withObjectErased st id).bookkeepingAgrees := by
  have hObj : ∀ k, (withObjectErased st id).objects[k]? =
      if id = k then none else st.objects[k]? := by
    intro k
    show (st.objects.erase id)[k]? = _
    simp only [RHTable_getElem?_eq_get?]
    split
    · next e => subst e; exact RHTable.getElem?_erase_self _ _ hInv
    · next e => exact RHTable.getElem?_erase_ne _ _ _ (fun hb => e (eq_of_beq hb)) hInv hSz
  have hI : (withObjectErased st id).objectIndex = st.objectIndex.filter (· != id) := by
    simp [withObjectErased]
  have hS : (withObjectErased st id).objectIndexSet = st.objectIndexSet.erase id := by
    simp [withObjectErased]
  have hT : (withObjectErased st id).lifecycle.objectTypes = st.lifecycle.objectTypes.erase id := by
    simp [withObjectErased]
  refine ⟨fun k => ?_, ?_, fun k => ?_, fun k => ?_, ?_, ?_, ?_⟩
  · rw [hI, hObj k, List.mem_filter, h.index k]
    by_cases e : id = k
    · subst e; simp
    · simp [e, Ne.symm e]
  · rw [hI]; exact h.nodup.filter _
  · rw [hS, hObj k]
    by_cases e : id = k
    · subst e; simp [RHSet.contains_erase_self _ _ h.indexSetInv.1]
    · rw [RHSet.contains_erase_ne_K _ _ _ (fun hb => e (eq_of_beq hb)) h.indexSetInv, h.indexSet k,
        if_neg e]
  · unfold SystemState.lookupObjectTypeMeta
    rw [hT, hObj k]
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_erase_K _ _ h.typesInv k]
    by_cases e : id = k
    · subst e; simp
    · have hb : (id == k) = false := by simpa using e
      rw [hb, if_neg e]
      have := h.types k
      unfold SystemState.lookupObjectTypeMeta at this
      simpa only [RHTable_getElem?_eq_get?] using this
  · rw [hS]; exact RHSet.erase_preserves_invExtK _ _ h.indexSetInv
  · rw [hT]; exact RHTable_erase_preserves_invExtK _ _ h.typesInv
  · exact ⟨by simpa [withObjectErased] using h.presized.objects, h.presized.asid⟩

/-- WS-UC UC1: `asid` erased from the ASID table, out of line, so the state is
handed over and the table written in place. -/
@[noinline] def withAsidErased (st : SystemState) (asid : SeLe4n.ASID) : SystemState :=
  { st with asidTable := st.asidTable.erase asid }

/-- WS-UC UC1: a VSpace root's ASID released — erased from the ASID table and its
invalidation recorded after the writes still owed (`recordPhysicalWrite`, whose
compiled form writes the ledger in place), so the ASID is free for the next
carve only once its translations are invalidated. -/
@[inline] def withAsidReleased (st : SystemState) (asid : SeLe4n.ASID) : SystemState :=
  (withAsidErased st asid).recordPhysicalWrite
    (SeLe4n.Kernel.Architecture.PhysicalWrite.invalidateAsid asid)

/-- **`retireCarvedObject` as compiled**: a frame, an untyped, a page table or a
VSpace root is erased from the object table out of line over the state it is
handed (`withObjectErased`, whose bookkeeping writes are ghost), so the table is
written in place and the state record reused; a
VSpace root's ASID then leaves the ASID table with its invalidation recorded
(`withAsidReleased`).  WS-UC UC1: the root took the specification's body before,
whose every field read the one state, so each table it erased was shared and was
copied whole (1810 heap cells per root deleted, at the exerciser's object count).
`retireCarvedObject_eq_impl` is the equality. -/
def retireCarvedObjectImpl (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  match st.getObjectType? id with
  | some .frame | some .untyped | some .pageTable =>
    withObjectErased st id
  | some .vspaceRoot =>
    match st.getVSpaceRoot? id with
    | some root =>
      withAsidReleased (withObjectErased st id) root.asid
    | none => st
  | _ => st

private theorem retireCarvedObject_of_nonRoot {st : SystemState} {id : SeLe4n.ObjId}
    (hG : ((st.getFrame? id).isSome || (st.getUntyped? id).isSome ||
      (st.getVSpaceRoot? id).isSome || (st.getPageTable? id).isSome) = true)
    (hR : st.getVSpaceRoot? id = none) :
    retireCarvedObject st id = withObjectErased st id := by
  unfold retireCarvedObject withObjectErased
  rw [if_pos hG, hR]

private theorem retireCarvedObject_of_root {st : SystemState} {id : SeLe4n.ObjId}
    {r : VSpaceRoot} (hR : st.getVSpaceRoot? id = some r) :
    retireCarvedObject st id = withAsidReleased (withObjectErased st id) r.asid := by
  unfold retireCarvedObject
  simp only [hR, Option.isSome_some, Bool.or_true, Bool.true_or, if_true]
  cases st
  simp only [withAsidReleased, withAsidErased, SystemState.recordPhysicalWrite,
    withObjectErased]

@[csimp] theorem retireCarvedObject_eq_impl : @retireCarvedObject = @retireCarvedObjectImpl := by
  funext st id
  unfold retireCarvedObjectImpl
  have hGuard : ∀ o, st.objects[id]? = some o →
      ((st.getFrame? id).isSome || (st.getUntyped? id).isSome ||
        (st.getVSpaceRoot? id).isSome || (st.getPageTable? id).isSome) =
      (match o with
       | .frame _ | .untyped _ | .vspaceRoot _ | .pageTable _ => true
       | _ => false) := by
    intro o hO
    simp only [SystemState.getFrame?, SystemState.getUntyped?, SystemState.getPageTable?,
      SystemState.getVSpaceRoot?, hO]
    cases o <;> rfl
  cases hO : st.objects[id]? with
  | none =>
    rw [show st.getObjectType? id = none by simp [SystemState.getObjectType?, hO]]
    unfold retireCarvedObject
    rw [if_neg]
    simp [SystemState.getFrame?, SystemState.getUntyped?, SystemState.getPageTable?,
      SystemState.getVSpaceRoot?, hO]
  | some o =>
    have hG := hGuard o hO
    rw [show st.getObjectType? id = some o.objectType by simp [SystemState.getObjectType?, hO]]
    cases o with
    | frame f => exact retireCarvedObject_of_nonRoot hG (by unfold SystemState.getVSpaceRoot?; rw [hO])
    | untyped u => exact retireCarvedObject_of_nonRoot hG (by unfold SystemState.getVSpaceRoot?; rw [hO])
    | pageTable p => exact retireCarvedObject_of_nonRoot hG (by unfold SystemState.getVSpaceRoot?; rw [hO])
    | vspaceRoot r =>
      have hR : st.getVSpaceRoot? id = some r := by unfold SystemState.getVSpaceRoot?; rw [hO]
      simp only [hR]
      exact retireCarvedObject_of_root hR
    | _ =>
      unfold retireCarvedObject
      rw [if_neg (by rw [hG]; simp)]
      rfl

/-- The retire's guard, read back: it fires exactly at a carved object. -/
theorem retireCarvedObject_guard_iff (st : SystemState) (id : SeLe4n.ObjId) :
    ((st.getFrame? id).isSome || (st.getUntyped? id).isSome ||
      (st.getVSpaceRoot? id).isSome || (st.getPageTable? id).isSome) = true ↔ carvedAt st id := by
  constructor
  · intro h
    rcases Bool.or_eq_true_iff.mp h with h'' | hP
    · rcases Bool.or_eq_true_iff.mp h'' with h' | hR
      · rcases Bool.or_eq_true_iff.mp h' with hF | hU
        · cases hG : st.getFrame? id with
          | none => rw [hG] at hF; cases hF
          | some f => exact Or.inl ⟨f, (SystemState.getFrame?_eq_some_iff st id f).mp hG⟩
        · cases hG : st.getUntyped? id with
          | none => rw [hG] at hU; cases hU
          | some u =>
            exact Or.inr (Or.inl ⟨u, (SystemState.getUntyped?_eq_some_iff st id u).mp hG⟩)
      · cases hG : st.getVSpaceRoot? id with
        | none => rw [hG] at hR; cases hR
        | some r =>
          exact Or.inr (Or.inr (Or.inl ⟨r, (SystemState.getVSpaceRoot?_eq_some_iff st id r).mp hG⟩))
    · cases hG : st.getPageTable? id with
      | none => rw [hG] at hP; cases hP
      | some p =>
        exact Or.inr (Or.inr (Or.inr ⟨p, (SystemState.getPageTable?_eq_some_iff st id p).mp hG⟩))
  · rintro (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩)
    · simp [(SystemState.getFrame?_eq_some_iff st id f).mpr hf]
    · simp [(SystemState.getUntyped?_eq_some_iff st id u).mpr hu]
    · simp [(SystemState.getVSpaceRoot?_eq_some_iff st id r).mpr hr]
    · simp [(SystemState.getPageTable?_eq_some_iff st id p).mpr hp]

/-- **Retiring one carved object**: the key erased held a carved object; every
other key is unchanged.  Stated with the headroom an erase needs
(`size < capacity`), which the final-delete retire reads before it erases and
which an erase preserves. -/
theorem retireCarvedObject_frame (st : SystemState) (id : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) (hSize : st.objects.size < st.objects.capacity) :
    (retireCarvedObject st id).objects.invExt ∧
    (retireCarvedObject st id).objects.size < (retireCarvedObject st id).objects.capacity ∧
    (retireCarvedObject st id).scheduler = st.scheduler ∧
    (∀ oid : SeLe4n.ObjId, (retireCarvedObject st id).objects[oid]? = st.objects[oid]? ∨
      (carvedAt st oid ∧ (retireCarvedObject st id).objects[oid]? = none)) ∧
    (st.objects[id]? = none ∨ carvedAt st id → (retireCarvedObject st id).objects[id]? = none) := by
  unfold retireCarvedObject
  by_cases hC : ((st.getFrame? id).isSome || (st.getUntyped? id).isSome ||
      (st.getVSpaceRoot? id).isSome || (st.getPageTable? id).isSome) = true
  · rw [if_pos hC]
    have hAt := (retireCarvedObject_guard_iff st id).mp hC
    have hSelf : (st.objects.erase id)[id]? = none :=
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self st.objects id hObjInv
    refine ⟨SeLe4n.Kernel.RobinHood.RHTable.erase_preserves_invExt st.objects id hObjInv hSize,
      SeLe4n.Kernel.RobinHood.RHTable.erase_size_lt_capacity st.objects id hSize, rfl,
      fun oid => ?_, fun _ => hSelf⟩
    by_cases hK : oid = id
    · subst hK; exact Or.inr ⟨hAt, hSelf⟩
    · have hNe : ¬(id == oid) = true := by
        intro h; exact hK (eq_of_beq h).symm
      exact Or.inl (SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne st.objects id oid hNe
        hObjInv hSize)
  · rw [if_neg hC]
    refine ⟨hObjInv, hSize, rfl, fun _ => Or.inl rfl, ?_⟩
    rintro (h | hAt)
    · exact h
    · exact absurd ((retireCarvedObject_guard_iff st id).mpr hAt) hC

/-- **The object kinds the erase of a carved object can touch**: an absent key,
a frame, an untyped, an address-space root or a page table.  None is a CNode or
a TCB, and none is a kind the IPC bundle or the scheduler reads. -/
def memoryKindOrAbsent : Option KernelObject → Prop
  | none => True
  | some (.vspaceRoot _) => True
  | some (.frame _) => True
  | some (.untyped _) => True
  | some (.pageTable _) => True
  | _ => False

end SeLe4n.Kernel
