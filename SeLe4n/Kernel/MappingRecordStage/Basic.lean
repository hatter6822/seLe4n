-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordPreservation

/-! # A step that keeps the live mappings recorded

`SystemState.liveMappingsRecorded` (`Model/MappingRecords.lean`) reads the
objects alone: every root's ASID, translations and epochs, every frame's base and
every slot's capability.  A `MappingStage` is a step that, from a state whose
object store keeps its table invariant, reaches one that keeps it too, keeps
the mappings recorded and keeps the bookkeeping ghosts in agreement with the
objects (`SystemState.bookkeepingAgrees`, WS-UC UC2).  Stages compose
(`MappingStage.trans`), so a kernel entry's proof is the composition of its
steps' stages.

Most steps keep every object's kind and mapping facts and every thread's slots,
write no CNode and move no ghost (`kindPreservingWrite`); their stage is
`MappingStage.of_kindPreservingWrite`.  A step that writes no object states
that it moves no ghost (`ghostsKept`, closed by `ghosts_kept` for a record
update that leaves the three fields alone).  The steps that write a slot or a mapping
are proven in `Kernel/MappingRecordPreservation.lean` and
`Capability/Invariant/Preservation/MappingRecords.lean`.
-/

namespace SeLe4n.Model.SystemState

/-- **A step that keeps the live mappings recorded**: from a state whose object
store keeps its table invariant, it reaches one that keeps it too, the mappings
stay recorded, and the bookkeeping stays in agreement with the objects. -/
def MappingStage (st st' : SystemState) : Prop :=
  st.objects.invExt → st'.objects.invExt ∧ (st.liveMappingsRecorded → st'.liveMappingsRecorded) ∧
    (st.bookkeepingAgrees → st'.bookkeepingAgrees)

namespace MappingStage

variable {st st' st'' : SystemState}

theorem refl (st : SystemState) : MappingStage st st := fun h => ⟨h, id, id⟩

theorem trans (h1 : MappingStage st st') (h2 : MappingStage st' st'') : MappingStage st st'' :=
  fun hI =>
    let ⟨hI', hL', hB'⟩ := h1 hI
    let ⟨hI'', hL'', hB''⟩ := h2 hI'
    ⟨hI'', hL'' ∘ hL', hB'' ∘ hB'⟩

/-- **A stage keeps the mappings recorded.** -/
theorem preserves (h : MappingStage st st') (hI : st.objects.invExt)
    (hL : st.liveMappingsRecorded) : st'.liveMappingsRecorded :=
  (h hI).2.1 hL

/-- WS-UC UC2: **a stage keeps the bookkeeping in agreement with the objects.** -/
theorem bookkeeping (h : MappingStage st st') (hI : st.objects.invExt)
    (hB : st.bookkeepingAgrees) : st'.bookkeepingAgrees :=
  (h hI).2.2 hB

/-- A stage keeps the store's table invariant. -/
theorem invExt (h : MappingStage st st') (hI : st.objects.invExt) : st'.objects.invExt :=
  (h hI).1

/-- A step that keeps the store's table invariant and every object's kind and
mapping facts, and moves no bookkeeping ghost. -/
theorem of_kindPreservingWrite (hI : st.objects.invExt → st'.objects.invExt)
    (hK : st.objects.invExt → kindPreservingWrite st st') : MappingStage st st' :=
  fun h => ⟨hI h, fun hL => hL.of_kindPreservingWrite (hK h),
    fun hB => hB.of_kept (.of_kindPreserving (hK h))⟩

/-- A step that writes no object, and none of the bookkeeping ghosts. -/
theorem of_objects_eq (hO : st'.objects = st.objects)
    (hG : ghostsKept st' st := by ghosts_kept) : MappingStage st st' :=
  fun h => ⟨hO ▸ h, fun hL => hL.of_objects_eq hO,
    fun hB => hB.of_kept (.of_objects_eq hO hG.index hG.indexSet hG.types hG.asidCapacity)⟩

/-- A stage from a state with the same objects and ghosts is a stage from this
one: the relation reads the objects and the ghosts alone. -/
theorem of_objects_eq_left {st0 : SystemState} (hO : st0.objects = st.objects)
    (h : MappingStage st0 st') (hG : ghostsKept st0 st := by ghosts_kept) : MappingStage st st' :=
  fun hI => let ⟨hI', hL, hB⟩ := h (hO ▸ hI)
    ⟨hI', fun hL0 => hL (hL0.of_objects_eq hO),
      fun hB0 => hB (hB0.of_kept (.of_objects_eq hO hG.index hG.indexSet hG.types
        hG.asidCapacity))⟩

/-- A step whose objects agree with the pre-state's off the threads' run-queue
links. -/
theorem of_objectsAgreeOffRunLinks (hI : st.objects.invExt → st'.objects.invExt)
    (hA : objectsAgreeOffRunLinks st' st) (hG : ghostsKept st' st := by ghosts_kept) :
    MappingStage st st' :=
  of_kindPreservingWrite hI fun _ => hA.kindPreserving hG

/-- A step whose objects agree with the pre-state's off the scheduler links —
the run-queue links and the contexts' release-queue fields. -/
theorem of_objectsAgreeOffSchedulerLinks (hI : st.objects.invExt → st'.objects.invExt)
    (hA : objectsAgreeOffSchedulerLinks st' st) (hG : ghostsKept st' st := by ghosts_kept) :
    MappingStage st st' :=
  of_kindPreservingWrite hI fun _ => hA.kindPreserving hG

/-- A step that keeps the store's table invariant and every object's mapping
facts (`SystemState.mappingFactsKept`), and moves no bookkeeping ghost: a write
that may also move binding codes, untyped records or table back-links. -/
theorem of_mappingFactsKept (hI : st.objects.invExt → st'.objects.invExt)
    (hK : st.objects.invExt → st.mappingFactsKept st')
    (hG : ghostsKept st' st := by ghosts_kept) : MappingStage st st' :=
  fun h => ⟨hI h, fun hL => hL.of_mappingFactsKept (hK h), fun hB => hB.of_kept
    ⟨hG.index, hG.indexSet, hG.types, fun x => by
      rcases hK h x with e | ⟨pre, post, hp, hq, ht, -⟩
      · rw [e]
      · rw [hp, hq]; simp [ht], hG.objectsCapacity, hG.asidCapacity⟩⟩

/-- WS-ZA ZA5.11: a step whose store agrees with the pre-state's off the taint
words — the taint step. -/
theorem of_objectsAgreeOffTaint (hI : st.objects.invExt → st'.objects.invExt)
    (hA : st.objectsAgreeOffTaint st') (hG : ghostsKept st' st := by ghosts_kept) :
    MappingStage st st' :=
  of_mappingFactsKept hI (fun _ => .of_objectsAgreeOffTaint hA) hG

/-- One store of an object of the kind it replaces, not a CNode, with the
replaced object's thread slots and mapping facts. -/
theorem storeObject {k : SeLe4n.ObjId} {obj pre : KernelObject}
    (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st')) (hPre : st.objects[k]? = some pre)
    (hKind : obj.objectType = pre.objectType)
    (hNotCnode : obj.objectType ≠ KernelObjectType.cnode)
    (hSlots : obj.tcbSlots = pre.tcbSlots := by rfl)
    (hMapping : obj.mappingView = pre.mappingView := by rfl) : MappingStage st st' :=
  of_mappingFactsKept (fun h => storeObject_preserves_objects_invExt _ _ _ _ h hS)
    (fun h => mappingFactsKept_storeObject h hS hPre hKind hNotCnode hSlots hMapping)
    (.storeObject_sameKind hS hPre hKind.symm)

/-- One raw insert of an object of the kind it replaces, not a CNode, with the
replaced object's thread slots and mapping facts. -/
theorem insert {k : SeLe4n.ObjId} {obj pre : KernelObject}
    (hO : st'.objects = st.objects.insert k obj) (hPre : st.objects[k]? = some pre)
    (hKind : obj.objectType = pre.objectType)
    (hNotCnode : obj.objectType ≠ KernelObjectType.cnode)
    (hSlots : obj.tcbSlots = pre.tcbSlots := by rfl)
    (hMapping : obj.mappingView = pre.mappingView := by rfl)
    (hG : ghostsKept st' st := by ghosts_kept) : MappingStage st st' :=
  of_mappingFactsKept (fun h => hO ▸ RHTable_insert_preserves_invExt st.objects k obj h)
    (fun h j => by
      rw [hO]; simp only [RHTable_getElem?_eq_get?]
      by_cases hj : k = j
      · subst hj
        refine .inr ⟨pre, obj, ?_, SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects k obj h,
          hKind, hNotCnode, hSlots, hMapping⟩
        rw [← RHTable_getElem?_eq_get?]; exact hPre
      · exact .inl (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects k j obj
          (fun hb => hj (eq_of_beq hb)) h)) hG

/-- A witnessed in-place rewrite (`rewriteObject`: same kind, never a CNode)
keeping the object's thread slots and mapping facts. -/
theorem rewriteObject (id : SeLe4n.ObjId) (new : KernelObject) (hA : st.rewriteAdmissible id new)
    (hSlots : ∀ old, st.objects[id]? = some old → new.tcbSlots = old.tcbSlots)
    (hMapping : ∀ old, st.objects[id]? = some old →
      new.mappingView = old.mappingView := by intro old _; cases old <;> rfl) :
    MappingStage st (st.rewriteObject id new hA) := by
  obtain ⟨pre, hPre, hKind, hNeutral⟩ := hA
  refine insert (pre := pre) rfl hPre hKind.symm ?_ (hSlots pre hPre) (hMapping pre hPre)
  intro hCn
  rw [hCn] at hNeutral
  exact absurd hNeutral (by simp [KernelObjectType.rewriteNeutral])

/-- A thread rewritten in place, keeping its two space slots. -/
theorem rewriteObject_tcb {tid : SeLe4n.ThreadId} {t : TCB} (h : st.getTcb? tid = some t)
    (t' : TCB) (hS : t'.spaceCells = t.spaceCells ∧ t'.spaceLinks = t.spaceLinks := by exact ⟨rfl, rfl⟩)
    (hA : st.rewriteAdmissible tid.toObjId (.tcb t') := rewriteAdmissible_tcb h t') :
    MappingStage st (st.rewriteObject tid.toObjId (.tcb t') hA) :=
  rewriteObject _ _ hA (fun old hOld => by
    rw [(getTcb?_eq_some_iff st tid t).mp h] at hOld; cases hOld
    simp only [KernelObject.tcbSlots, hS.1, hS.2]) fun old hOld => by
    rw [(getTcb?_eq_some_iff st tid t).mp h] at hOld; cases hOld; rfl

/-- A stage that holds from a pre-state whose store keeps its table invariant. -/
theorem of_invExt (H : st.objects.invExt → MappingStage st st') : MappingStage st st' :=
  fun h => H h h

theorem of_eq (h : st' = st) : MappingStage st st' := by subst h; exact refl _

/-- A stage to a pair's state is a stage to whatever state the pair is matched
against. -/
theorem of_fst_eq {α : Type} {p : SystemState × α} {r : α} (s : MappingStage st p.1)
    (h : p = (st', r)) : MappingStage st st' := by
  subst h; exact s

/-- A step keeping the store's table invariant whose preservation holds on such
a state. -/
theorem of_preserves (hI : st.objects.invExt → st'.objects.invExt)
    (h : st.objects.invExt → st.liveMappingsRecorded → st'.liveMappingsRecorded)
    (hB : st.objects.invExt → st.bookkeepingAgrees → st'.bookkeepingAgrees) :
    MappingStage st st' :=
  fun hI0 => ⟨hI hI0, h hI0, hB hI0⟩

end MappingStage

end SeLe4n.Model.SystemState
