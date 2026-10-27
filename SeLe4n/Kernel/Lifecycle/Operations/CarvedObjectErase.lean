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
        objectIndex := st.objectIndex.filter (· != id)
        objectIndexSet := st.objectIndexSet.erase id
        lifecycle := { objectTypes := st.lifecycle.objectTypes.erase id }
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

/-- `id` dropped from an object-index list: `List.filter`, written as a
tail-recursive walk whose kept cells are consed onto `acc` and reversed back,
so an exclusively owned index is rewritten cell for cell in place
(`objIdListDrop_eq_filter`). -/
def objIdListDrop (id : SeLe4n.ObjId) : List SeLe4n.ObjId → List SeLe4n.ObjId → List SeLe4n.ObjId
  | [], acc => acc.reverse
  | a :: rest, acc => if a == id then objIdListDrop id rest acc else objIdListDrop id rest (a :: acc)

theorem objIdListDrop_eq_filter (id : SeLe4n.ObjId) :
    ∀ (l acc : List SeLe4n.ObjId), objIdListDrop id l acc = acc.reverse ++ l.filter (· != id)
  | [], acc => by simp [objIdListDrop]
  | a :: rest, acc => by
    unfold objIdListDrop
    by_cases h : a = id
    · subst h; simp [objIdListDrop_eq_filter a rest acc]
    · have hb : (a == id) = false := by simpa using h
      rw [if_neg (by simp [hb]), objIdListDrop_eq_filter id rest (a :: acc)]
      simp [h]

/-- The object table with `id` erased, out of line, so the state is handed over
and its table written in place. -/
@[noinline] def withObjectErased (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  { st with objects := st.objects.erase id }

/-- `id` dropped from the object index, out of line. -/
@[noinline] def withObjectUnindexed (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  { st with objectIndex := objIdListDrop id st.objectIndex [] }

/-- `id` erased from the index set, out of line. -/
@[noinline] def withObjectIndexSetErased (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  { st with objectIndexSet := st.objectIndexSet.erase id }

/-- `id`'s type erased, the lifecycle record updated rather than rebuilt. -/
@[noinline] def withObjectTypeErased (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  { st with lifecycle := { st.lifecycle with objectTypes := st.lifecycle.objectTypes.erase id } }

/-- **`retireCarvedObject` as compiled**: a frame, an untyped or a page table is
erased one table at a time, each write out of line over the state it is handed,
so every table is written in place and the state record reused; a VSpace root,
whose ASID leaves the table with it, takes the specification's body
(`retireCarvedObject_eq_impl`). -/
def retireCarvedObjectImpl (st : SystemState) (id : SeLe4n.ObjId) : SystemState :=
  match st.getObjectType? id with
  | some .frame | some .untyped | some .pageTable =>
    withObjectTypeErased (withObjectIndexSetErased (withObjectUnindexed (withObjectErased st id) id) id) id
  | some .vspaceRoot => retireCarvedObject st id
  | _ => st

private theorem retireCarvedObject_of_nonRoot {st : SystemState} {id : SeLe4n.ObjId}
    (hG : ((st.getFrame? id).isSome || (st.getUntyped? id).isSome ||
      (st.getVSpaceRoot? id).isSome || (st.getPageTable? id).isSome) = true)
    (hR : st.getVSpaceRoot? id = none) :
    retireCarvedObject st id =
      withObjectTypeErased (withObjectIndexSetErased (withObjectUnindexed (withObjectErased st id) id) id) id := by
  unfold retireCarvedObject withObjectTypeErased withObjectIndexSetErased withObjectUnindexed
    withObjectErased
  rw [if_pos hG, hR, objIdListDrop_eq_filter]
  simp

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
    | vspaceRoot r => rfl
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
