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

WS-ZA ZA5.4 part 18 adds the two facts finality reads that need only the store's
presence, read through a presence reader beside the slot reader:

* **every capability names a live object** (`TreeShapeOver.live`): the object a
  capability names (`Capability.namedObject`, seL4's `sameObjectAs` by object
  id, untyped included) is in the store;
* **a child naming another object than its parent lies, with every slot naming
  that object, strictly below its parent** (`TreeShapeOver.below`): the slots
  naming an object a derivation changed to sit under the slot it was derived
  from, as a carve's child sits under its untyped capability.

`CapTreeShape` bundles them.  Each tree write keeps it by one lemma here: a
step that keeps the tree and every slot and no object leaves the store
(`SlotTreeFrame`), an insert that records its edge (`CapTreeShape.addChild`), a
delete's splice (`CapTreeShape.splice`), a move's rename (`CapTreeShape.move`)
and an in-place rewrite of an occupied slot that keeps its object
(`CapTreeShape.rewrite`).  Each takes the presence reader's monotonicity: no
object a capability may name leaves the store.
-/

namespace SeLe4n.Model

/-- **The object a capability names**, seL4's `sameObjectAs` by object id,
untyped included: `.object o` names `o`, a reply capability its reply, a CNode
slot capability its CNode, and the audit-trail capability nothing, so it is the
same object as no other capability. -/
def Capability.namedObject (c : Capability) : Option SeLe4n.ObjId :=
  match c.target with
  | .object o => some o
  | .cnodeSlot cn _ => some cn
  | .replyCap r => some r.toObjId
  | .auditTrail => none

/-- A capability's object is read from its target alone. -/
theorem Capability.namedObject_of_target {c c' : Capability} (h : c'.target = c.target) :
    c'.namedObject = c.namedObject := by
  unfold Capability.namedObject; rw [h]

namespace SystemState

/-- **Slot `r` holds a capability naming object `o`**, over a slot reader. -/
def namesAt (cap : SlotRef → Option Capability) (r : SlotRef) (o : SeLe4n.ObjId) : Prop :=
  ∃ c, cap r = some c ∧ c.namedObject = some o

theorem namesAt_of_eq {cap cap' : SlotRef → Option Capability} {r r' : SlotRef} {o : SeLe4n.ObjId}
    (h : cap' r' = cap r) : namesAt cap' r' o ↔ namesAt cap r o := by
  unfold namesAt; rw [h]

theorem namesAt_occupied {cap : SlotRef → Option Capability} {r : SlotRef} {o : SeLe4n.ObjId}
    (h : namesAt cap r o) : cap r ≠ none := by
  obtain ⟨c, hc, -⟩ := h; rw [hc]; exact Option.some_ne_none _

/-- **Object `o` is in the store.** -/
abbrev objectPresent (st : SystemState) (o : SeLe4n.ObjId) : Prop := st.objects[o]? ≠ none

/-- **Every slot holding a capability is in the derivation tree**, as every
non-null capability is in seL4's mapping database. -/
def slotsInTree (st : SystemState) : Prop :=
  ∀ r, st.slotCapAt r ≠ none → st.cdt.mentions r

/-- **What a step keeps of the tree's shape**: the tree and every slot's
capability. -/
structure SlotTreeFrame (st st' : SystemState) : Prop where
  cdt : st'.cdt = st.cdt
  slotCapAt : ∀ r, st'.slotCapAt r = st.slotCapAt r
  present : ∀ o, st.objectPresent o → st'.objectPresent o

theorem SlotTreeFrame.refl (st : SystemState) : SlotTreeFrame st st :=
  ⟨rfl, fun _ => rfl, fun _ h => h⟩

theorem SlotTreeFrame.trans {st₁ st₂ st₃ : SystemState} (h₁ : SlotTreeFrame st₁ st₂)
    (h₂ : SlotTreeFrame st₂ st₃) : SlotTreeFrame st₁ st₃ :=
  ⟨h₂.cdt.trans h₁.cdt, fun r => (h₂.slotCapAt r).trans (h₁.slotCapAt r),
    fun o h => h₂.present o (h₁.present o h)⟩

/-- Link writes keep every object in the store. -/
theorem objectsAgreeOffDerivationLinks.present {st st' : SystemState}
    (hA : objectsAgreeOffDerivationLinks st' st) (o : SeLe4n.ObjId) (h : st.objectPresent o) :
    st'.objectPresent o := by
  have e := hA.objectType o
  intro h0; rw [h0] at e
  cases h1 : st.objects[o]? with
  | none => exact h h1
  | some _ => rw [h1] at e; cases e

/-- A kind-preserving write keeps every object in the store. -/
theorem kindPreservingWrite.present {st st' : SystemState} (h : kindPreservingWrite st st')
    (o : SeLe4n.ObjId) (hp : st.objectPresent o) : st'.objectPresent o := by
  rcases h o with e | ⟨_, _, _, hq, _⟩
  · rw [objectPresent, e]; exact hp
  · rw [objectPresent, hq]; exact Option.some_ne_none _

/-- Link writes keep every slot's capability. -/
theorem SlotTreeFrame.of_agree {st st' : SystemState} (hA : objectsAgreeOffDerivationLinks st' st)
    (hCdt : st'.cdt = st.cdt) : SlotTreeFrame st st' :=
  ⟨hCdt, hA.slotCapAt, hA.present⟩

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

/-- A store keeps every object in the store. -/
theorem objectPresent_storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o' : KernelObject}
    (hInv : st.objects.invExt) (hStore : storeObject k o' st = .ok ((), st')) (o : SeLe4n.ObjId)
    (hp : st.objectPresent o) : st'.objectPresent o := by
  by_cases e : o = k
  · subst e; rw [objectPresent, storeObject_objects_eq st st' o o' hInv hStore]
    exact Option.some_ne_none _
  · rw [objectPresent, storeObject_objects_ne st st' k o o' e hInv hStore]; exact hp

/-- A capability `lookupSlotCap` reads is the slot's. -/
theorem slotCapAt_of_lookupSlotCap {st : SystemState} {r : SlotRef} {c : Capability}
    (h : st.lookupSlotCap r = some c) : st.slotCapAt r = some c := by
  obtain ⟨cn, hO, hL⟩ := lookupSlotCap_cnode h
  rw [slotCapAt_of_object hO]; exact hL

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

/-- **An in-place rewrite of a CNode slot that keeps its object keeps what every
slot names.** -/
theorem namesAt_storeObject_insert {st st' : SystemState} {a : SlotRef} {cn : CNode}
    {c c' : Capability} (hInv : st.objects.invExt) (hPre : st.objects[a.cnode]? = some (.cnode cn))
    (hLk : cn.lookup a.slot = some c) (hObj : c'.namedObject = c.namedObject)
    (hStore : storeObject a.cnode (.cnode (cn.insert a.slot c')) st = .ok ((), st'))
    (r : SlotRef) (o : SeLe4n.ObjId) : namesAt st'.slotCapAt r o ↔ namesAt st.slotCapAt r o := by
  by_cases e : r = a
  · subst e
    have h1 : st'.slotCapAt r = some c' := by
      rw [slotCapAt_of_object (storeObject_objects_eq _ _ _ _ hInv hStore)]
      exact CNode.lookup_insert_eq cn r.slot _ (CNode.slotsUnique_holds _)
        (CNode.slotAddressable_of_lookup _ _ _ hLk)
    have h0 : st.slotCapAt r = some c := (slotCapAt_of_object hPre).trans hLk
    unfold namesAt; rw [h1, h0]; simp [hObj]
  · exact namesAt_of_eq (slotCapAt_storeObject_ne hInv hPre hStore
      (fun s' hs => CNode.lookup_insert_ne cn a.slot s' _ (Ne.symm hs) (CNode.slotsUnique_holds _))
      r e)

/-- A step that keeps the tree, every CNode and every thread's slots, key by
key, keeps every slot's capability. -/
theorem SlotTreeFrame.of_slots {st st' : SystemState} (hCdt : st'.cdt = st.cdt)
    (hCn : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      st'.objects[oid]? = some (.cnode cn) ↔ st.objects[oid]? = some (.cnode cn))
    (hTcb : ∀ oid : SeLe4n.ObjId,
      (st'.objects[oid]?).bind KernelObject.tcbSlots = (st.objects[oid]?).bind KernelObject.tcbSlots)
    (hPresent : ∀ o, st.objectPresent o → st'.objectPresent o) :
    SlotTreeFrame st st' :=
  ⟨hCdt, fun r => by
    rw [slotCapAt_eq_bind, slotCapAt_eq_bind]
    exact (KernelObject.optSlots_eq_of_cnode_iff (hCn r.cnode) (hTcb r.cnode)).1 r.slot, hPresent⟩

end SystemState

namespace CapDerivationTree

/-- The ends of a child link are slots the tree names. -/
theorem mentions_of_mem_childrenOf {cdt : CapDerivationTree} {p c : SlotRef}
    (h : c ∈ cdt.childrenOf p) : cdt.mentions p ∧ cdt.mentions c := by
  obtain ⟨e, he, hp, hc⟩ := childrenOf_to_edge cdt p c h
  exact ⟨mentions_of_edge he (.inl hp), mentions_of_edge he (.inr hc)⟩

/-- **An added edge keeps every descent**: `addEdge` only adds a child. -/
theorem CdtChildReachable.addEdge {cdt : CapDerivationTree} {a b : SlotRef}
    (h : CdtChildReachable cdt a b) (p c : SlotRef) (op : DerivationOp) :
    CdtChildReachable (cdt.addEdge p c op) a b := by
  have hm : ∀ {q x}, x ∈ cdt.childrenOf q → x ∈ (cdt.addEdge p c op).childrenOf q := by
    intro q x hx; rw [childrenOf_addEdge]; split
    · exact List.mem_cons_of_mem _ hx
    · exact hx
  induction h with
  | child hc => exact .child (hm hc)
  | trans _ hc ih => exact .trans ih (hm hc)

/-- **A splice keeps every descent between the slots it keeps**: a path through
the spliced slot `n` runs from `n`'s parent straight to `n`'s child. -/
theorem CdtChildReachable.spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    {n : SlotRef} (hs : cdt.parentOf n ≠ some n) {a b : SlotRef}
    (h : CdtChildReachable cdt a b) (ha : a ≠ n) (hb : b ≠ n) :
    CdtChildReachable (cdt.spliceNode n) a b := by
  have hnn := not_mem_childrenOf_self hU hs
  have hch : ∀ {q x}, q ≠ n → x ∈ cdt.childrenOf q →
      (x ≠ n → x ∈ (cdt.spliceNode n).childrenOf q) ∧
      (x = n → ∀ y ∈ cdt.childrenOf n, y ∈ (cdt.spliceNode n).childrenOf q) := by
    intro q x hq hx
    rw [childrenOf_spliceNode hU hs, if_neg hq]
    exact ⟨fun hxn => mem_replaceSlot.mpr (.inl ⟨hx, hxn⟩),
      fun hxn y hy => mem_replaceSlot.mpr (.inr ⟨hxn ▸ hx, hy⟩)⟩
  suffices H : (b ≠ n → CdtChildReachable (cdt.spliceNode n) a b) ∧
      (b = n → ∀ y ∈ cdt.childrenOf n, CdtChildReachable (cdt.spliceNode n) a y) from H.1 hb
  clear hb
  induction h with
  | child hc =>
    exact ⟨fun hb => .child ((hch ha hc).1 hb), fun hb y hy => .child ((hch ha hc).2 hb y hy)⟩
  | @trans mid c _ hc ih =>
    by_cases hmid : mid = n
    · subst hmid
      have hcn : c ≠ mid := fun e => hnn (by rw [e] at hc; exact hc)
      exact ⟨fun _ => ih.2 rfl c hc, fun e => absurd e hcn⟩
    · have hr := ih.1 hmid
      exact ⟨fun hb => .trans hr ((hch hmid hc).1 hb),
        fun hb y hy => .trans hr ((hch hmid hc).2 hb y hy)⟩

/-- **A move renames every descent**: the moved tree is the old one with `old`
renamed `new`. -/
theorem CdtChildReachable.moveNode {cdt : CapDerivationTree} {old new : SlotRef}
    (hnew : ¬ cdt.mentions new) (hon : old ≠ new) {a b : SlotRef}
    (h : CdtChildReachable cdt a b) :
    CdtChildReachable (cdt.moveNode old new) (renameSlot old new a) (renameSlot old new b) := by
  have hch : ∀ {q x}, x ∈ cdt.childrenOf q →
      renameSlot old new x ∈ (cdt.moveNode old new).childrenOf (renameSlot old new q) := by
    intro q x hx
    have hq : q ≠ new := fun e => hnew (e ▸ (mentions_of_mem_childrenOf hx).1)
    have hqo : renameSlot old new q ≠ old := by
      unfold renameSlot; split
      · exact Ne.symm hon
      · assumption
    rw [childrenOf_moveNode hnew hon, if_neg hqo, renameSlot_back hq]
    exact List.mem_map_of_mem hx
  induction h with
  | child hc => exact .child (hch hc)
  | trans _ hc ih => exact .trans ih (hch hc)

end CapDerivationTree

namespace SystemState

/-- **The shape of a derivation tree over a slot reading and a presence
reading**: every slot holding a capability is in the tree, the tree has a
preorder, every capability names a present object (`live`), and a child naming
another object than its occupied parent lies, with every slot naming that
object, strictly below that parent (`below`).  Stated over the tree and the two
readers rather than the state, so a step that rewrites none of them (a scheduler
or machine write) keeps it definitionally. -/
structure TreeShapeOver (cdt : CapDerivationTree) (cap : SlotRef → Option Capability)
    (present : SeLe4n.ObjId → Prop) : Prop where
  inTree : ∀ r, cap r ≠ none → cdt.mentions r
  ordered : ∃ P, cdt.TreeOrder P
  live : ∀ r o, namesAt cap r o → present o
  below : ∀ p c o, c ∈ cdt.childrenOf p → namesAt cap c o → cap p ≠ none → ¬ namesAt cap p o →
    ∀ r, namesAt cap r o → CapDerivationTree.CdtChildReachable cdt p r

/-- **The shape of the derivation tree over the slots and the store**: every slot
holding a capability is in the tree (`slotsInTree`), the tree has a preorder,
every capability names an object in the store, and the slots naming an object a
derivation changed lie below the slot it was derived from. -/
abbrev CapTreeShape (st : SystemState) : Prop :=
  TreeShapeOver st.cdt st.slotCapAt st.objectPresent

/-- Descent is transitive. -/
theorem _root_.SeLe4n.Model.CapDerivationTree.CdtChildReachable.trans' {cdt : CapDerivationTree}
    {a b c : SlotRef} (h₁ : CapDerivationTree.CdtChildReachable cdt a b)
    (h₂ : CapDerivationTree.CdtChildReachable cdt b c) :
    CapDerivationTree.CdtChildReachable cdt a c := by
  induction h₂ with
  | child hc => exact .trans h₁ hc
  | trans _ hc ih => exact .trans ih hc

namespace TreeShapeOver

variable {cdt : CapDerivationTree} {cap cap' : SlotRef → Option Capability}
  {present present' : SeLe4n.ObjId → Prop}

/-- **A reading whose every occupied slot holds the old reading's capability
keeps the shape** when no object leaves the store: emptying slots only drops
obligations. -/
theorem of_sub (h : TreeShapeOver cdt cap present)
    (hS : ∀ r, cap' r ≠ none → cap' r = cap r) (hP : ∀ o, present o → present' o) :
    TreeShapeOver cdt cap' present' := by
  have hN : ∀ {r o}, namesAt cap' r o → namesAt cap r o := fun hr =>
    (namesAt_of_eq (hS _ (namesAt_occupied hr))).mp hr
  refine ⟨fun r hr => h.inTree r (by rw [← hS r hr]; exact hr), h.ordered,
    fun r o hr => hP o (h.live r o (hN hr)), fun p c o hc hcO hp hpO r hr => ?_⟩
  exact h.below p c o hc (hN hcO) (by rw [← hS p hp]; exact hp)
    (fun e => hpO ((namesAt_of_eq (hS p hp)).mpr e)) r (hN hr)

/-- **A splice keeps the shape** (the reading-level statement of
`CapTreeShape.splice`): the spliced slot `n` reads empty and leaves the tree,
every other occupied slot reads as before, and a slot with children held a
capability, so a child of `n` naming another object than `n`'s parent lay below
`n`'s parent already. -/
theorem splice (h : TreeShapeOver cdt cap present) {n : SlotRef} {cdt' : CapDerivationTree}
    (hU : cdt.childrenUnique) (hR : cdt.rootsParentless) (hs : cdt.parentOf n ≠ some n)
    (hCdt : cdt' = cdt.spliceNode n) (hn : cap' n = none)
    (hS : ∀ r, r ≠ n → cap' r ≠ none → cap' r = cap r)
    (hP : ∀ o, present o → present' o)
    (hnOcc : cdt.childrenOf n ≠ [] → cap n ≠ none) : TreeShapeOver cdt' cap' present' := by
  subst hCdt
  obtain ⟨P, hPo⟩ := h.ordered
  have hP' := hPo.spliceNode hU hR hs
  have hnn := CapDerivationTree.not_mem_childrenOf_self hU hs
  have hrn : ∀ {r o}, namesAt cap' r o → r ≠ n := fun hr e =>
    namesAt_occupied hr (e ▸ hn)
  have hN : ∀ {r o}, namesAt cap' r o → namesAt cap r o := fun hr =>
    (namesAt_of_eq (hS _ (hrn hr) (namesAt_occupied hr))).mp hr
  refine ⟨fun r hr => ?_, ⟨_, hP'⟩, fun r o hr => hP o (h.live r o (hN hr)),
    fun p c o hc hcO hp hpO r hr => ?_⟩
  · have hrn' : r ≠ n := fun e => hr (e ▸ hn)
    refine (hP'.mem_iff r).mp (List.mem_filter.mpr ⟨(hPo.mem_iff r).mpr (h.inTree r ?_),
      by simp [hrn']⟩)
    rw [← hS r hrn' hr]; exact hr
  · rw [CapDerivationTree.childrenOf_spliceNode hU hs] at hc
    have hpn : p ≠ n := fun e => by rw [if_pos e] at hc; cases hc
    rw [if_neg hpn] at hc
    have hp' : cap p ≠ none := by rw [← hS p hpn hp]; exact hp
    have hpO' : ¬ namesAt cap p o := fun e => hpO ((namesAt_of_eq (hS p hpn hp)).mpr e)
    have hr' := hN hr
    have hOld : CapDerivationTree.CdtChildReachable cdt p r := by
      rcases CapDerivationTree.mem_replaceSlot.mp hc with ⟨hcp, -⟩ | ⟨hnp, hcn⟩
      · exact h.below p c o hcp (hN hcO) hp' hpO' r hr'
      · by_cases hnO : namesAt cap n o
        · exact h.below p n o hnp hnO hp' hpO' r hr'
        · exact (CapDerivationTree.CdtChildReachable.child hnp).trans'
            (h.below n c o hcn (hN hcO)
              (hnOcc fun e => by rw [e] at hcn; cases hcn) hnO r hr')
    exact hOld.spliceNode hU hs hpn (hrn hr)

end TreeShapeOver

namespace CapTreeShape

variable {st st' : SystemState}

/-- A slot holding a capability is in the preorder. -/
theorem mem_order (h : CapTreeShape st) {P : List SlotRef} (hP : st.cdt.TreeOrder P)
    {r : SlotRef} (hr : st.slotCapAt r ≠ none) : r ∈ P :=
  (hP.mem_iff r).mpr (h.inTree r hr)

/-- **A step that keeps the tree, and whose every occupied slot holds the
pre-state's capability, keeps the shape** when no object leaves the store:
emptying slots only drops obligations. -/
theorem of_sub (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt)
    (hS : ∀ r, st'.slotCapAt r ≠ none → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o) : CapTreeShape st' := by
  unfold CapTreeShape; rw [hCdt]; exact TreeShapeOver.of_sub h hS hP

/-- **A step that keeps the tree and every slot keeps the shape** when no object
leaves the store. -/
theorem of_frame (h : CapTreeShape st) (hF : SlotTreeFrame st st') : CapTreeShape st' :=
  h.of_sub hF.cdt (fun r _ => hF.slotCapAt r) hF.present

/-- **Emptying slots keeps the shape**: the tree is unchanged, every slot still
occupied holds what it held, and no object leaves the store. -/
theorem of_empties (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt)
    (hS : ∀ r, st'.slotCapAt r ≠ none → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o) : CapTreeShape st' :=
  h.of_sub hCdt hS hP

/-- **An in-place rewrite of an occupied slot that keeps its object keeps the
shape**, when no object leaves the store. -/
theorem rewrite (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt) {a : SlotRef}
    {c c' : Capability} (ha : st.slotCapAt a = some c) (ha' : st'.slotCapAt a = some c')
    (hObj : c'.namedObject = c.namedObject)
    (hS : ∀ r, r ≠ a → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o) : CapTreeShape st' := by
  have hOcc : ∀ r, st'.slotCapAt r ≠ none ↔ st.slotCapAt r ≠ none := fun r => by
    by_cases e : r = a
    · subst e; rw [ha, ha']; simp
    · rw [hS r e]
  have hN : ∀ r o, namesAt st'.slotCapAt r o ↔ namesAt st.slotCapAt r o := fun r o => by
    by_cases e : r = a
    · subst e; unfold namesAt; rw [ha, ha']; simp [hObj]
    · exact namesAt_of_eq (hS r e)
  refine ⟨fun r hr => ?_, by rw [hCdt]; exact h.ordered,
    fun r o hr => hP o (h.live r o ((hN r o).mp hr)), fun p c₀ o hc hcO hp hpO r hr => ?_⟩
  · rw [hCdt]; exact h.inTree r ((hOcc r).mp hr)
  · rw [hCdt] at hc ⊢
    exact h.below p c₀ o hc ((hN _ _).mp hcO) ((hOcc p).mp hp)
      (fun e => hpO ((hN _ _).mpr e)) r ((hN _ _).mp hr)

/-- **An insert that records its derivation keeps the shape**: `dst`, empty and
outside the tree, receives a capability and becomes the first child of `src`,
which holds one, so the tree names both and the new child lands right after its
source in the preorder (`TreeOrder.addEdge`).  The new capability names what
the source names (a copy, a mint, a transfer), or an object present after the
step that no slot named before (a carve's), so it names a live object and a
child naming another object than its source is the only slot naming it. -/
theorem addChild (h : CapTreeShape st) {src dst : SlotRef} (op : DerivationOp)
    (hSrc : st.slotCapAt src ≠ none) (hDst : ¬ st.cdt.mentions dst)
    (hCdt : st'.cdt = st.cdt.addEdge src dst op)
    (hS : ∀ r, r ≠ dst → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hNew : ∀ o, namesAt st'.slotCapAt dst o →
      namesAt st.slotCapAt src o ∨ ((∀ r, ¬ namesAt st.slotCapAt r o) ∧ st'.objectPresent o)) :
    CapTreeShape st' := by
  have hsd : src ≠ dst := fun e => hDst (e ▸ h.inTree src hSrc)
  have hN : ∀ {r o}, r ≠ dst → (namesAt st'.slotCapAt r o ↔ namesAt st.slotCapAt r o) :=
    fun hr => namesAt_of_eq (hS _ hr)
  have hDstCh : dst ∈ st'.cdt.childrenOf src := by
    rw [hCdt, CapDerivationTree.childrenOf_addEdge, if_pos rfl]; exact List.mem_cons_self ..
  refine ⟨fun r hr => ?_, ?_, fun r o hr => ?_, fun p c o hc hcO hp hpO r hr => ?_⟩
  · rw [hCdt, CapDerivationTree.mentions_addEdge]
    by_cases e : r = dst
    · exact .inr (.inr e)
    · exact .inl (h.inTree r (by rw [← hS r e]; exact hr))
  · obtain ⟨P, hPo⟩ := h.ordered
    rw [hCdt]
    exact ⟨_, hPo.addEdge (h.inTree src hSrc) hDst op⟩
  · by_cases e : r = dst
    · subst e
      rcases hNew o hr with hs | ⟨-, hl⟩
      · exact hP o (h.live src o hs)
      · exact hl
    · exact hP o (h.live r o ((hN e).mp hr))
  · have hcases : (p = src ∧ c = dst) ∨ c ∈ st.cdt.childrenOf p := by
      rw [hCdt, CapDerivationTree.childrenOf_addEdge] at hc
      split at hc
      · next e => rcases List.mem_cons.mp hc with e' | e'
                  · exact .inl ⟨e, e'⟩
                  · exact .inr e'
      · exact .inr hc
    rcases hcases with ⟨rfl, rfl⟩ | hcOld
    · rcases hNew o hcO with hs | ⟨hno, -⟩
      · exact absurd ((hN hsd).mpr hs) hpO
      · by_cases e : r = c
        · rw [e]; exact .child hDstCh
        · exact absurd ((hN e).mp hr) (hno r)
    · have hm := CapDerivationTree.mentions_of_mem_childrenOf hcOld
      have hcd : c ≠ dst := fun e => hDst (e ▸ hm.2)
      have hpd : p ≠ dst := fun e => hDst (e ▸ hm.1)
      have hcO' := (hN hcd).mp hcO
      have key := h.below p c o hcOld hcO' (by rw [← hS p hpd]; exact hp)
        (fun e => hpO ((hN hpd).mpr e))
      by_cases e : r = dst
      · rw [e] at hr ⊢
        rcases hNew o hr with hs | ⟨hno, -⟩
        · exact (by rw [hCdt]; exact (key src hs).addEdge src dst op :
            CapDerivationTree.CdtChildReachable st'.cdt p src).trans' (.child hDstCh)
        · exact absurd hcO' (hno c)
      · rw [hCdt]; exact (key r ((hN e).mp hr)).addEdge src dst op

/-- **A delete's splice keeps the shape**: the deleted slot `n` is empty and
leaves the tree, and every other slot keeps its capability and its place in the
preorder (`TreeOrder.spliceNode`); a slot with children held a capability, so a
child of `n` naming another object than `n`'s parent lay below `n`'s parent
already (`TreeShapeOver.splice`). -/
theorem splice (h : CapTreeShape st) {n : SlotRef} (hU : st.cdt.childrenUnique)
    (hR : st.cdt.rootsParentless) (hs : st.cdt.parentOf n ≠ some n)
    (hCdt : st'.cdt = st.cdt.spliceNode n) (hn : st'.slotCapAt n = none)
    (hS : ∀ r, r ≠ n → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hnOcc : st.cdt.childrenOf n ≠ [] → st.slotCapAt n ≠ none) : CapTreeShape st' :=
  TreeShapeOver.splice h hU hR hs hCdt hn (fun r hr _ => hS r hr) hP hnOcc

/-- **A move keeps the shape**: the source's capability goes to `new`, empty
and outside the tree, which takes the source's place in the preorder
(`TreeOrder.moveNode`); every other slot keeps its capability, and every descent
is renamed with the slot. -/
theorem move (h : CapTreeShape st) {old new : SlotRef} (hon : old ≠ new)
    (hOld : st.slotCapAt old ≠ none) (hNew : ¬ st.cdt.mentions new)
    (hCdt : st'.cdt = st.cdt.moveNode old new) (hOld' : st'.slotCapAt old = none)
    (hMoved : st'.slotCapAt new = st.slotCapAt old)
    (hS : ∀ r, r ≠ old → r ≠ new → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o) : CapTreeShape st' := by
  obtain ⟨P, hPo⟩ := h.ordered
  have hP' := hPo.moveNode hNew hon
  -- every slot but `old` reads the pre-state's slot it was renamed from
  have hBack : ∀ y, y ≠ old →
      st'.slotCapAt y = st.slotCapAt (CapDerivationTree.renameSlot new old y) := by
    intro y hy
    by_cases e : y = new
    · subst e; simp [CapDerivationTree.renameSlot, hMoved]
    · rw [hS y hy e]; simp [CapDerivationTree.renameSlot, e]
  have hForth : ∀ y, y ≠ old → CapDerivationTree.renameSlot old new
      (CapDerivationTree.renameSlot new old y) = y := by
    intro y hy
    by_cases e : y = new
    · subst e; simp [CapDerivationTree.renameSlot]
    · simp [CapDerivationTree.renameSlot, e, hy]
  have hro : ∀ {r o}, namesAt st'.slotCapAt r o → r ≠ old := fun hr e =>
    namesAt_occupied hr (e ▸ hOld')
  have hN : ∀ {r o}, r ≠ old → (namesAt st'.slotCapAt r o ↔
      namesAt st.slotCapAt (CapDerivationTree.renameSlot new old r) o) :=
    fun hr => namesAt_of_eq (hBack _ hr)
  refine ⟨fun r hr => ?_, by rw [hCdt]; exact ⟨_, hP'⟩,
    fun r o hr => hP o (h.live _ o ((hN (hro hr)).mp hr)), fun p c o hc hcO hp hpO r hr => ?_⟩
  · rw [hCdt]
    refine (hP'.mem_iff r).mp (List.mem_map.mpr ?_)
    by_cases e : r = new
    · exact ⟨old, h.mem_order hPo hOld, by simp [CapDerivationTree.renameSlot, e]⟩
    · have hro' : r ≠ old := fun e' => hr (e' ▸ hOld')
      exact ⟨r, h.mem_order hPo (by rw [← hS r hro' e]; exact hr),
        by simp [CapDerivationTree.renameSlot, hro']⟩
  · rw [hCdt, CapDerivationTree.childrenOf_moveNode hNew hon] at hc
    have hpo : p ≠ old := fun e => by rw [if_pos e] at hc; cases hc
    rw [if_neg hpo] at hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    have hxn : x ≠ new := fun e => hNew (e ▸ (CapDerivationTree.mentions_of_mem_childrenOf hx).2)
    have hcO' := (hN (hro hcO)).mp hcO
    rw [CapDerivationTree.renameSlot_back hxn] at hcO'
    have key := h.below _ x o hx hcO' (by rw [← hBack p hpo]; exact hp)
      (fun e => hpO ((hN hpo).mpr e)) _ ((hN (hro hr)).mp hr)
    have := key.moveNode hNew hon
    rw [hForth p hpo, hForth r (hro hr)] at this
    rw [hCdt]; exact this

end CapTreeShape

end SystemState

end SeLe4n.Model
