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
object store keeps its table invariant, reaches one that keeps it too and keeps
the mappings recorded.  Stages compose (`MappingStage.trans`), so a kernel
entry's proof is the composition of its steps' stages.

Most steps keep every object's kind and mapping facts and every thread's slots,
and write no CNode (`kindPreservingWrite`); their stage is
`MappingStage.of_kindPreservingWrite`.  The steps that write a slot or a mapping
are proven in `Kernel/MappingRecordPreservation.lean` and
`Capability/Invariant/Preservation/MappingRecords.lean`.
-/

namespace SeLe4n.Model.SystemState

/-- **A step that keeps the live mappings recorded**: from a state whose object
store keeps its table invariant, it reaches one that keeps it too, and the
mappings stay recorded. -/
def MappingStage (st st' : SystemState) : Prop :=
  st.objects.invExt → st'.objects.invExt ∧ (st.liveMappingsRecorded → st'.liveMappingsRecorded)

namespace MappingStage

variable {st st' st'' : SystemState}

theorem refl (st : SystemState) : MappingStage st st := fun h => ⟨h, id⟩

theorem trans (h1 : MappingStage st st') (h2 : MappingStage st' st'') : MappingStage st st'' :=
  fun hI =>
    let ⟨hI', hL'⟩ := h1 hI
    let ⟨hI'', hL''⟩ := h2 hI'
    ⟨hI'', hL'' ∘ hL'⟩

/-- **A stage keeps the mappings recorded.** -/
theorem preserves (h : MappingStage st st') (hI : st.objects.invExt)
    (hL : st.liveMappingsRecorded) : st'.liveMappingsRecorded :=
  (h hI).2 hL

/-- A stage keeps the store's table invariant. -/
theorem invExt (h : MappingStage st st') (hI : st.objects.invExt) : st'.objects.invExt :=
  (h hI).1

/-- A step that keeps the store's table invariant and every object's kind and
mapping facts. -/
theorem of_kindPreservingWrite (hI : st.objects.invExt → st'.objects.invExt)
    (hK : st.objects.invExt → kindPreservingWrite st st') : MappingStage st st' :=
  fun h => ⟨hI h, fun hL => hL.of_kindPreservingWrite (hK h)⟩

/-- A step that writes no object. -/
theorem of_objects_eq (hO : st'.objects = st.objects) : MappingStage st st' :=
  fun h => ⟨hO ▸ h, fun hL => hL.of_objects_eq hO⟩

/-- A stage from a state with the same objects is a stage from this one: the
relation reads the objects alone. -/
theorem of_objects_eq_left {st0 : SystemState} (hO : st0.objects = st.objects)
    (h : MappingStage st0 st') : MappingStage st st' :=
  fun hI => let ⟨hI', hL⟩ := h (hO ▸ hI); ⟨hI', fun hL0 => hL (hL0.of_objects_eq hO)⟩

/-- A step whose objects agree with the pre-state's off the threads' run-queue
links. -/
theorem of_objectsAgreeOffRunLinks (hI : st.objects.invExt → st'.objects.invExt)
    (hA : objectsAgreeOffRunLinks st' st) : MappingStage st st' :=
  of_kindPreservingWrite hI fun _ => hA.kindPreserving

/-- A step that keeps the store's table invariant and every object's mapping
facts (`SystemState.mappingFactsKept`): a write that may also move binding
codes, untyped records or table back-links. -/
theorem of_mappingFactsKept (hI : st.objects.invExt → st'.objects.invExt)
    (hK : st.objects.invExt → st.mappingFactsKept st') : MappingStage st st' :=
  fun h => ⟨hI h, fun hL => hL.of_mappingFactsKept (hK h)⟩

/-- WS-ZA ZA5.11: a step whose store agrees with the pre-state's off the taint
words — the taint step. -/
theorem of_objectsAgreeOffTaint (hI : st.objects.invExt → st'.objects.invExt)
    (hA : st.objectsAgreeOffTaint st') : MappingStage st st' :=
  of_mappingFactsKept hI fun _ => .of_objectsAgreeOffTaint hA

/-- One store of an object of the kind it replaces, not a CNode, with the
replaced object's thread slots and mapping facts. -/
theorem storeObject {k : SeLe4n.ObjId} {obj pre : KernelObject}
    (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st')) (hPre : st.objects[k]? = some pre)
    (hKind : obj.objectType = pre.objectType)
    (hNotCnode : obj.objectType ≠ KernelObjectType.cnode)
    (hSlots : obj.tcbSlots = pre.tcbSlots := by rfl)
    (hMapping : obj.mappingView = pre.mappingView := by rfl) : MappingStage st st' :=
  of_mappingFactsKept (fun h => storeObject_preserves_objects_invExt _ _ _ _ h hS)
    fun h => mappingFactsKept_storeObject h hS hPre hKind hNotCnode hSlots hMapping

/-- One raw insert of an object of the kind it replaces, not a CNode, with the
replaced object's thread slots and mapping facts. -/
theorem insert {k : SeLe4n.ObjId} {obj pre : KernelObject}
    (hO : st'.objects = st.objects.insert k obj) (hPre : st.objects[k]? = some pre)
    (hKind : obj.objectType = pre.objectType)
    (hNotCnode : obj.objectType ≠ KernelObjectType.cnode)
    (hSlots : obj.tcbSlots = pre.tcbSlots := by rfl)
    (hMapping : obj.mappingView = pre.mappingView := by rfl) : MappingStage st st' :=
  of_mappingFactsKept (fun h => hO ▸ RHTable_insert_preserves_invExt st.objects k obj h)
    fun h j => by
      rw [hO]; simp only [RHTable_getElem?_eq_get?]
      by_cases hj : k = j
      · subst hj
        refine .inr ⟨pre, obj, ?_, SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects k obj h,
          hKind, hNotCnode, hSlots, hMapping⟩
        rw [← RHTable_getElem?_eq_get?]; exact hPre
      · exact .inl (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects k j obj
          (fun hb => hj (eq_of_beq hb)) h)

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
    (h : st.objects.invExt → st.liveMappingsRecorded → st'.liveMappingsRecorded) :
    MappingStage st st' :=
  fun hI0 => ⟨hI hI0, h hI0⟩

end MappingStage

end SeLe4n.Model.SystemState
