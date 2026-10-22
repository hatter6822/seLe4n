-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.SlotLinks

/-!
# The shape of the derivation tree over the slots

seL4 keeps every non-null capability in its mapping database, one list in
derivation order.  This module states the two facts the seLe4n tree owes that
list (WS-ZA ZA5.4 part 16), over the state's slots and its tree:

* **every slot holding a capability is in the tree** (`slotsInTree`), the
  converse of `cdtCompleteness`, so an insert's source is always a slot the tree
  names and the new child lands right after it in the preorder;
* **the tree has a preorder** (`CapDerivationTree.TreeOrder`), seL4's list.

`CapTreeShape` bundles them.  Each tree write keeps it by one lemma here: a
step that keeps the tree and every slot (`SlotTreeFrame`), an insert that
records its edge (`CapTreeShape.addChild`), a delete's splice
(`CapTreeShape.splice`), a move's rename (`CapTreeShape.move`) and an in-place
rewrite of an occupied slot (`CapTreeShape.rewrite`).
-/

namespace SeLe4n.Model

namespace SystemState

/-- **Every slot holding a capability is in the derivation tree**, as every
non-null capability is in seL4's mapping database. -/
def slotsInTree (st : SystemState) : Prop :=
  ∀ r, st.slotCapAt r ≠ none → st.cdt.mentions r

/-- **What a step keeps of the tree's shape**: the tree and every slot's
capability. -/
structure SlotTreeFrame (st st' : SystemState) : Prop where
  cdt : st'.cdt = st.cdt
  slotCapAt : ∀ r, st'.slotCapAt r = st.slotCapAt r

theorem SlotTreeFrame.refl (st : SystemState) : SlotTreeFrame st st := ⟨rfl, fun _ => rfl⟩

theorem SlotTreeFrame.trans {st₁ st₂ st₃ : SystemState} (h₁ : SlotTreeFrame st₁ st₂)
    (h₂ : SlotTreeFrame st₂ st₃) : SlotTreeFrame st₁ st₃ :=
  ⟨h₂.cdt.trans h₁.cdt, fun r => (h₂.slotCapAt r).trans (h₁.slotCapAt r)⟩

/-- Link writes keep every slot's capability. -/
theorem SlotTreeFrame.of_agree {st st' : SystemState} (hA : objectsAgreeOffDerivationLinks st' st)
    (hCdt : st'.cdt = st.cdt) : SlotTreeFrame st st' :=
  ⟨hCdt, hA.slotCapAt⟩

/-- A run of link writes keeps every slot's capability. -/
theorem SlotTreeFrame.of_linkReach {st₀ st : SystemState} (hR : linkReach st₀ st)
    (hInv : st₀.objects.invExt) : SlotTreeFrame st₀ st :=
  .of_agree (hR.agree hInv) hR.cdt

/-- The slot reader is the object's slot read, bound through the store. -/
theorem slotCapAt_eq_bind (st : SystemState) (r : SlotRef) :
    st.slotCapAt r = (st.objects[r.cnode]?).bind fun o => o.slotCap r.slot := by
  unfold slotCapAt getObject?
  cases st.objects[r.cnode]? <;> rfl

/-- **A store's slot reads**: the stored object's at its key, the pre-state's
elsewhere. -/
theorem slotCapAt_storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o' : KernelObject}
    (hInv : st.objects.invExt) (hStore : storeObject k o' st = .ok ((), st')) (r : SlotRef) :
    st'.slotCapAt r = if r.cnode = k then o'.slotCap r.slot else st.slotCapAt r := by
  rw [slotCapAt_eq_bind, slotCapAt_eq_bind]
  split
  · next h => rw [h, storeObject_objects_eq st st' k o' hInv hStore]; rfl
  · next h => rw [storeObject_objects_ne st st' k r.cnode o' h hInv hStore]

/-- A store at `k` of an object whose slots read as the old one's but at `s`
keeps every other slot's capability. -/
theorem slotCapAt_storeObject_ne {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some o)
    (hStore : storeObject k o' st = .ok ((), st')) {s : SeLe4n.Slot}
    (hO : ∀ s', s' ≠ s → o'.slotCap s' = o.slotCap s') (r : SlotRef) (hr : r ≠ ⟨k, s⟩) :
    st'.slotCapAt r = st.slotCapAt r := by
  rw [slotCapAt_storeObject hInv hStore]
  split
  · next h =>
    have hs : r.slot ≠ s := fun e => hr (by cases r; simp_all)
    rw [hO _ hs, slotCapAt_eq_bind, h, hPre]; rfl
  · rfl

/-- A step that keeps the tree, every CNode and every thread's slots, key by
key, keeps every slot's capability. -/
theorem SlotTreeFrame.of_slots {st st' : SystemState} (hCdt : st'.cdt = st.cdt)
    (hCn : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      st'.objects[oid]? = some (.cnode cn) ↔ st.objects[oid]? = some (.cnode cn))
    (hTcb : ∀ oid : SeLe4n.ObjId,
      (st'.objects[oid]?).bind KernelObject.tcbSlots = (st.objects[oid]?).bind KernelObject.tcbSlots) :
    SlotTreeFrame st st' :=
  ⟨hCdt, fun r => by
    rw [slotCapAt_eq_bind, slotCapAt_eq_bind]
    exact (KernelObject.optSlots_eq_of_cnode_iff (hCn r.cnode) (hTcb r.cnode)).1 r.slot⟩

/-- **The shape of a derivation tree over a slot reading**: every slot holding a
capability is in it, and it has a preorder.  Stated over the tree and the slot
reader rather than the state, so a step that rewrites neither (a scheduler or
machine write) keeps it definitionally. -/
structure TreeShapeOver (cdt : CapDerivationTree) (cap : SlotRef → Option Capability) : Prop where
  inTree : ∀ r, cap r ≠ none → cdt.mentions r
  ordered : ∃ P, cdt.TreeOrder P

/-- **The shape of the derivation tree over the slots**: every slot holding a
capability is in it (`slotsInTree`), and it has a preorder. -/
abbrev CapTreeShape (st : SystemState) : Prop := TreeShapeOver st.cdt st.slotCapAt

namespace CapTreeShape

variable {st st' : SystemState}

/-- A slot holding a capability is in the preorder. -/
theorem mem_order (h : CapTreeShape st) {P : List SlotRef} (hP : st.cdt.TreeOrder P)
    {r : SlotRef} (hr : st.slotCapAt r ≠ none) : r ∈ P :=
  (hP.mem_iff r).mpr (h.inTree r hr)

/-- **A step that keeps the tree and every slot keeps the shape.** -/
theorem of_frame (h : CapTreeShape st) (hF : SlotTreeFrame st st') : CapTreeShape st' where
  inTree := fun r hr => by rw [hF.cdt]; exact h.inTree r (by rw [← hF.slotCapAt]; exact hr)
  ordered := by rw [hF.cdt]; exact h.ordered

/-- **Emptying slots keeps the shape**: the tree is unchanged and no slot gains
a capability. -/
theorem of_empties (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt)
    (hS : ∀ r, st'.slotCapAt r ≠ none → st.slotCapAt r ≠ none) : CapTreeShape st' where
  inTree := fun r hr => by rw [hCdt]; exact h.inTree r (hS r hr)
  ordered := by rw [hCdt]; exact h.ordered

/-- **An in-place rewrite of an occupied slot keeps the shape.** -/
theorem rewrite (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt) {a : SlotRef}
    (ha : st.slotCapAt a ≠ none)
    (hS : ∀ r, r ≠ a → st'.slotCapAt r = st.slotCapAt r) : CapTreeShape st' :=
  h.of_empties hCdt fun r hr => by
    by_cases e : r = a
    · subst e; exact ha
    · rw [← hS r e]; exact hr

/-- **An insert that records its derivation keeps the shape**: `dst`, empty and
outside the tree, receives a capability and becomes the first child of `src`,
which holds one, so the tree names both and the new child lands right after its
source in the preorder (`TreeOrder.addEdge`). -/
theorem addChild (h : CapTreeShape st) {src dst : SlotRef} (op : DerivationOp)
    (hSrc : st.slotCapAt src ≠ none) (hDst : ¬ st.cdt.mentions dst)
    (hCdt : st'.cdt = st.cdt.addEdge src dst op)
    (hS : ∀ r, r ≠ dst → st'.slotCapAt r = st.slotCapAt r) : CapTreeShape st' where
  inTree := fun r hr => by
    rw [hCdt, CapDerivationTree.mentions_addEdge]
    by_cases e : r = dst
    · exact .inr (.inr e)
    · exact .inl (h.inTree r (by rw [← hS r e]; exact hr))
  ordered := by
    obtain ⟨P, hP⟩ := h.ordered
    rw [hCdt]
    exact ⟨_, hP.addEdge (h.inTree src hSrc) hDst op⟩

/-- **A delete's splice keeps the shape**: the deleted slot `n` is empty and
leaves the tree, and every other slot keeps its capability and its place in the
preorder (`TreeOrder.spliceNode`). -/
theorem splice (h : CapTreeShape st) {n : SlotRef} (hU : st.cdt.childrenUnique)
    (hR : st.cdt.rootsParentless) (hs : st.cdt.parentOf n ≠ some n)
    (hCdt : st'.cdt = st.cdt.spliceNode n) (hn : st'.slotCapAt n = none)
    (hS : ∀ r, r ≠ n → st'.slotCapAt r = st.slotCapAt r) : CapTreeShape st' := by
  obtain ⟨P, hP⟩ := h.ordered
  have hP' := hP.spliceNode hU hR hs
  refine ⟨fun r hr => ?_, by rw [hCdt]; exact ⟨_, hP'⟩⟩
  have hrn : r ≠ n := fun e => hr (e ▸ hn)
  rw [hCdt]
  refine (hP'.mem_iff r).mp (List.mem_filter.mpr ⟨h.mem_order hP ?_, by simp [hrn]⟩)
  rw [← hS r hrn]; exact hr

/-- **A move keeps the shape**: the source's capability goes to `new`, empty
and outside the tree, which takes the source's place in the preorder
(`TreeOrder.moveNode`); every other slot keeps its capability. -/
theorem move (h : CapTreeShape st) {old new : SlotRef} (hon : old ≠ new)
    (hOld : st.slotCapAt old ≠ none) (hNew : ¬ st.cdt.mentions new)
    (hCdt : st'.cdt = st.cdt.moveNode old new) (hOld' : st'.slotCapAt old = none)
    (hS : ∀ r, r ≠ old → r ≠ new → st'.slotCapAt r = st.slotCapAt r) : CapTreeShape st' := by
  obtain ⟨P, hP⟩ := h.ordered
  have hP' := hP.moveNode hNew hon
  refine ⟨fun r hr => ?_, by rw [hCdt]; exact ⟨_, hP'⟩⟩
  rw [hCdt]
  refine (hP'.mem_iff r).mp (List.mem_map.mpr ?_)
  by_cases e : r = new
  · exact ⟨old, h.mem_order hP hOld, by simp [CapDerivationTree.renameSlot, e]⟩
  · have hro : r ≠ old := fun e' => hr (e' ▸ hOld')
    exact ⟨r, h.mem_order hP (by rw [← hS r hro e]; exact hr),
      by simp [CapDerivationTree.renameSlot, hro]⟩

end CapTreeShape

end SystemState

end SeLe4n.Model
