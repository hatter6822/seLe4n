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

WS-ZA ZA5.4 part 19 adds seL4's untyped facts, read through a third reader, the
store's untyped records (`SystemState.getUntyped?`):

* **(a) the slots naming one untyped form one contiguous vertical first-child
  chain** (`TreeShapeOver.chainLinear`, `TreeShapeOver.chainFirst`);
* **(b) an untyped capability that is not full has no strict descendant naming
  its untyped** (`TreeShapeOver.notFullLeaf`), owed everywhere but at the slots
  an `off` predicate names: the middle state of a copy, mint or transfer of an
  untyped capability is off (b) at its source (`CapTreeShapeOff`) until the
  source is set full;
* **every capability naming memory carved from an untyped lies strictly below
  every capability to it** (`TreeShapeOver.carvedBelow`, seL4's `untyped_mdb`),
  "carved from" being the transitive closure of the child lists (`CarvedFrom`);
* **every child an untyped records is live, and an object is recorded by at most
  one untyped** (`TreeShapeOver.childLive`, `TreeShapeOver.childUnique`, seL4's
  `untyped_inc`).

`CapTreeShape` bundles them.  Each tree write keeps it by one lemma here: a
step that keeps the tree, every slot and every untyped and no object leaves the
store (`SlotTreeFrame`), an insert that records its edge
(`TreeShapeOver.addChild`, off (b) at the source; `TreeShapeOver.addChild_fresh`
for a carve's fresh object), a delete's splice (`CapTreeShape.splice`), a move's
rename (`CapTreeShape.move`), an in-place rewrite of an occupied slot that keeps
its target and does not lower its free index (`CapTreeShape.rewrite`), and a
carve's record of its child (`TreeShapeOver.carveRecord`).  Each takes the
presence reader's monotonicity: no object a capability may name leaves the
store.
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

/-- **Slot `r` holds an untyped capability to `u`**, over a slot reader and an
untyped reader: its capability's target is the object `u`, and `u` is an
untyped.  seL4's untyped capability. -/
def untypedCapAt (cap : SlotRef → Option Capability) (ut : SeLe4n.ObjId → Option UntypedObject)
    (r : SlotRef) (u : SeLe4n.ObjId) : Prop :=
  ∃ c, cap r = some c ∧ c.target = .object u ∧ ut u ≠ none

theorem untypedCapAt.namesAt {cap : SlotRef → Option Capability}
    {ut : SeLe4n.ObjId → Option UntypedObject} {r : SlotRef} {u : SeLe4n.ObjId}
    (h : untypedCapAt cap ut r u) : namesAt cap r u := by
  obtain ⟨c, hc, ht, -⟩ := h
  exact ⟨c, hc, by simp [Capability.namedObject, ht]⟩

theorem untypedCapAt.occupied {cap : SlotRef → Option Capability}
    {ut : SeLe4n.ObjId → Option UntypedObject} {r : SlotRef} {u : SeLe4n.ObjId}
    (h : untypedCapAt cap ut r u) : cap r ≠ none :=
  namesAt_occupied h.namesAt

theorem untypedCapAt_of_eq {cap cap' : SlotRef → Option Capability}
    {ut : SeLe4n.ObjId → Option UntypedObject} {r r' : SlotRef} {u : SeLe4n.ObjId}
    (h : cap' r' = cap r) : untypedCapAt cap' ut r' u ↔ untypedCapAt cap ut r u := by
  unfold untypedCapAt; rw [h]

/-- Two slots whose capabilities have one target hold an untyped capability to
the same untyped together. -/
theorem untypedCapAt_of_target {cap cap' : SlotRef → Option Capability}
    {ut : SeLe4n.ObjId → Option UntypedObject} {r r' : SlotRef} {u : SeLe4n.ObjId}
    {c c' : Capability} (h : cap r = some c) (h' : cap' r' = some c') (hT : c'.target = c.target) :
    untypedCapAt cap' ut r' u ↔ untypedCapAt cap ut r u := by
  unfold untypedCapAt; rw [h, h']; simp [hT]

/-- **Untyped `u` records `x` among the objects carved from it.** -/
def recordsChild (ut : SeLe4n.ObjId → Option UntypedObject) (u x : SeLe4n.ObjId) : Prop :=
  ∃ U, ut u = some U ∧ ∃ ch ∈ U.children, ch.objId = x

/-- **`x` is memory carved from untyped `u`**: the transitive closure of the
untyped's child-list relation, seL4's `untyped_mdb` "carved from". -/
inductive CarvedFrom (ut : SeLe4n.ObjId → Option UntypedObject) : SeLe4n.ObjId → SeLe4n.ObjId → Prop
  | child {u x : SeLe4n.ObjId} : recordsChild ut u x → CarvedFrom ut u x
  | trans {u v x : SeLe4n.ObjId} : CarvedFrom ut u v → recordsChild ut v x → CarvedFrom ut u x

/-- Memory is carved from an untyped only if the untyped records a child. -/
theorem CarvedFrom.first {ut : SeLe4n.ObjId → Option UntypedObject} {u x : SeLe4n.ObjId}
    (h : CarvedFrom ut u x) : ∃ v, recordsChild ut u v := by
  induction h with
  | child h => exact ⟨_, h⟩
  | trans _ _ ih => exact ih

/-- An untyped recording no child has nothing carved from it. -/
theorem CarvedFrom.not_of_childless {ut : SeLe4n.ObjId → Option UntypedObject} {u x : SeLe4n.ObjId}
    (hU : ∀ U, ut u = some U → U.children = []) : ¬ CarvedFrom ut u x := fun h => by
  obtain ⟨v, U, hu, ch, hch, -⟩ := h.first
  rw [hU U hu] at hch; cases hch

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
  /-- Every untyped record, its region and its children, is kept. -/
  untyped : st'.getUntyped? = st.getUntyped?

theorem SlotTreeFrame.refl (st : SystemState) : SlotTreeFrame st st :=
  ⟨rfl, fun _ => rfl, fun _ h => h, rfl⟩

theorem SlotTreeFrame.trans {st₁ st₂ st₃ : SystemState} (h₁ : SlotTreeFrame st₁ st₂)
    (h₂ : SlotTreeFrame st₂ st₃) : SlotTreeFrame st₁ st₃ :=
  ⟨h₂.cdt.trans h₁.cdt, fun r => (h₂.slotCapAt r).trans (h₁.slotCapAt r),
    fun o h => h₂.present o (h₁.present o h), h₂.untyped.trans h₁.untyped⟩

/-- Link writes keep every untyped record: an untyped holds no link. -/
theorem objectsAgreeOffDerivationLinks.getUntyped? {st st' : SystemState}
    (hA : objectsAgreeOffDerivationLinks st' st) : st'.getUntyped? = st.getUntyped? := by
  funext o
  rw [getUntyped?_eq_bind, getUntyped?_eq_bind]
  have hB : ∀ x : Option KernelObject,
      x.bind KernelObject.untyped? = (x.map KernelObject.withoutLinks).bind KernelObject.untyped? := by
    intro x; cases x <;> simp
  rw [hB, (hA o).map_withoutLinks, ← hB]

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
  ⟨hCdt, hA.slotCapAt, hA.present, hA.getUntyped?⟩

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
    (hPresent : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hUntyped : st'.getUntyped? = st.getUntyped?) :
    SlotTreeFrame st st' :=
  ⟨hCdt, fun r => by
    rw [slotCapAt_eq_bind, slotCapAt_eq_bind]
    exact (KernelObject.optSlots_eq_of_cnode_iff (hCn r.cnode) (hTcb r.cnode)).1 r.slot, hPresent,
    hUntyped⟩

/-- A store whose object's untyped record is the one it replaces keeps every
untyped record. -/
theorem getUntyped?_storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o' : KernelObject}
    (hInv : st.objects.invExt) (hStore : storeObject k o' st = .ok ((), st'))
    (hU : o'.untyped? = (st.objects[k]?).bind KernelObject.untyped?) :
    st'.getUntyped? = st.getUntyped? := by
  funext o
  rw [getUntyped?_eq_bind, getUntyped?_eq_bind]
  by_cases e : o = k
  · subst e; rw [storeObject_objects_eq st st' o o' hInv hStore]; exact hU
  · rw [storeObject_objects_ne st st' k o o' e hInv hStore]

/-- A store of a CNode over a CNode keeps every untyped record. -/
theorem getUntyped?_storeObject_cnode {st st' : SystemState} {k : SeLe4n.ObjId} {cn cn' : CNode}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.cnode cn))
    (hStore : storeObject k (.cnode cn') st = .ok ((), st')) :
    st'.getUntyped? = st.getUntyped? :=
  getUntyped?_storeObject hInv hStore (by rw [hPre]; rfl)

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

/-- Descent is transitive. -/
theorem CdtChildReachable.trans' {cdt : CapDerivationTree}
    {a b c : SlotRef} (h₁ : CdtChildReachable cdt a b) (h₂ : CdtChildReachable cdt b c) :
    CdtChildReachable cdt a c := by
  induction h₂ with
  | child hc => exact .trans h₁ hc
  | trans _ hc ih => exact .trans ih hc

/-- **A descent starts at a child of its start.** -/
theorem CdtChildReachable.first {cdt : CapDerivationTree} {a b : SlotRef}
    (h : CdtChildReachable cdt a b) :
    ∃ c ∈ cdt.childrenOf a, c = b ∨ CdtChildReachable cdt c b := by
  induction h with
  | child hc => exact ⟨_, hc, .inl rfl⟩
  | @trans mid c _ hc ih =>
    obtain ⟨d, hd, e | r⟩ := ih
    · subst e; exact ⟨d, hd, .inr (.child hc)⟩
    · exact ⟨d, hd, .inr (.trans r hc)⟩

/-- A slot with no children reaches nothing. -/
theorem CdtChildReachable.not_of_childless {cdt : CapDerivationTree} {a b : SlotRef}
    (h : cdt.childrenOf a = []) : ¬ CdtChildReachable cdt a b := fun r => by
  obtain ⟨c, hc, -⟩ := r.first; rw [h] at hc; cases hc

/-- A slot the tree does not name has no children. -/
theorem childrenOf_eq_nil_of_not_mentions {cdt : CapDerivationTree} {a : SlotRef}
    (h : ¬ cdt.mentions a) : cdt.childrenOf a = [] := by
  cases hc : cdt.childrenOf a with
  | nil => rfl
  | cons c _ => exact absurd (mentions_of_mem_childrenOf (hc ▸ List.mem_cons_self ..)).1 h

/-- A slot a descent reaches is one the tree names. -/
theorem CdtChildReachable.mentions_end {cdt : CapDerivationTree} {a b : SlotRef}
    (h : CdtChildReachable cdt a b) : cdt.mentions b := by
  cases h with
  | child hc => exact (mentions_of_mem_childrenOf hc).2
  | trans _ hc => exact (mentions_of_mem_childrenOf hc).2

/-- **A descent in a tree with an added edge to a fresh slot** is one of the old
tree's, or reaches the new child through its parent. -/
theorem CdtChildReachable.of_addEdge {cdt : CapDerivationTree} {p c : SlotRef} {op : DerivationOp}
    (hc : ¬ cdt.mentions c) (hpc : p ≠ c) {a b : SlotRef}
    (h : CdtChildReachable (cdt.addEdge p c op) a b) :
    CdtChildReachable cdt a b ∨ ((a = p ∨ CdtChildReachable cdt a p) ∧ b = c) := by
  have hcc : cdt.childrenOf c = [] := childrenOf_eq_nil_of_not_mentions hc
  have hstep : ∀ {q x}, x ∈ (cdt.addEdge p c op).childrenOf q →
      x ∈ cdt.childrenOf q ∨ (q = p ∧ x = c) := by
    intro q x hx
    rw [childrenOf_addEdge] at hx
    split at hx
    · next e =>
      rcases List.mem_cons.mp hx with e' | e'
      · exact .inr ⟨e, e'⟩
      · exact .inl e'
    · exact .inl hx
  induction h with
  | child hx =>
    rcases hstep hx with h' | ⟨rfl, rfl⟩
    · exact .inl (.child h')
    · exact .inr ⟨.inl rfl, rfl⟩
  | @trans mid x _ hx ih =>
    rcases ih with r | ⟨-, rfl⟩
    · rcases hstep hx with h' | ⟨rfl, rfl⟩
      · exact .inl (.trans r h')
      · exact .inr ⟨.inr r, rfl⟩
    · rcases hstep hx with h' | ⟨e, -⟩
      · rw [hcc] at h'; cases h'
      · exact absurd e.symm hpc

/-- **A descent in a spliced tree is one of the old tree's.** -/
theorem CdtChildReachable.of_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    {n : SlotRef} (hs : cdt.parentOf n ≠ some n) {a b : SlotRef}
    (h : CdtChildReachable (cdt.spliceNode n) a b) : CdtChildReachable cdt a b := by
  have hstep : ∀ {q x}, x ∈ (cdt.spliceNode n).childrenOf q → CdtChildReachable cdt q x := by
    intro q x hx
    rw [childrenOf_spliceNode hU hs] at hx
    split at hx
    · cases hx
    · rcases mem_replaceSlot.mp hx with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact .child h1
      · exact .trans (.child h1) h2
  induction h with
  | child hx => exact hstep hx
  | trans _ hx ih => exact ih.trans' (hstep hx)

/-- **A descent in a moved tree is an old one renamed back.** -/
theorem CdtChildReachable.of_moveNode {cdt : CapDerivationTree} {old new : SlotRef}
    (hnew : ¬ cdt.mentions new) (hon : old ≠ new) {a b : SlotRef}
    (h : CdtChildReachable (cdt.moveNode old new) a b) :
    CdtChildReachable cdt (renameSlot new old a) (renameSlot new old b) := by
  have hstep : ∀ {q x}, x ∈ (cdt.moveNode old new).childrenOf q →
      renameSlot new old x ∈ cdt.childrenOf (renameSlot new old q) := by
    intro q x hx
    rw [childrenOf_moveNode hnew hon] at hx
    split at hx
    · cases hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hyn : y ≠ new := fun e => hnew (e ▸ (mentions_of_mem_childrenOf hy).2)
      rw [renameSlot_back hyn]; exact hy
  induction h with
  | child hx => exact .child (hstep hx)
  | trans _ hx ih => exact .trans ih (hstep hx)

/-- A list's first element is in it. -/
theorem mem_of_head?_eq_some {l : List SlotRef} {c : SlotRef} (h : l.head? = some c) : c ∈ l := by
  cases l with
  | nil => cases h
  | cons x l => cases h; exact List.mem_cons_self ..

/-- Replacing a slot that is not first keeps the first. -/
theorem replaceSlot_head_ne {n c : SlotRef} {m l : List SlotRef} (h : l.head? = some c)
    (hc : c ≠ n) : (replaceSlot n m l).head? = some c := by
  cases l with
  | nil => cases h
  | cons x l => cases h; simp [replaceSlot, List.flatMap_cons, hc]

/-- Replacing the first slot by a list puts that list's first in its place. -/
theorem replaceSlot_head_self {n d : SlotRef} {m l : List SlotRef} (h : l.head? = some n)
    (hm : m.head? = some d) : (replaceSlot n m l).head? = some d := by
  cases l with
  | nil => cases h
  | cons x l =>
    cases h
    cases m with
    | nil => cases hm
    | cons y m => cases hm; simp [replaceSlot, List.flatMap_cons]

end CapDerivationTree


namespace SystemState

/-- **The shape of a derivation tree over a slot reading, a presence reading and
an untyped reading**: every slot holding a capability is in the tree, the tree
has a preorder, every capability names a present object (`live`), and a child
naming another object than its occupied parent lies, with every slot naming that
object, strictly below that parent (`below`).

WS-ZA ZA5.4 part 19 adds the untyped facts, seL4's `untyped_mdb` and
`untyped_inc`, read through the untyped reader:

* (a) the slots holding untyped capabilities to one untyped form one contiguous
  vertical first-child chain: any two lie on one descent (`chainLinear`), and a
  slot with one below it has the first of its children on that descent
  (`chainFirst`);
* (b) an untyped capability that is not full has no strict descendant naming its
  untyped (`notFullLeaf`), except at the slots `off` names: a copy, mint or
  transfer of an untyped capability is off at its source until it sets the
  source full;
* every capability naming memory carved from an untyped lies strictly below every
  capability to that untyped (`carvedBelow`), "carved from" being the transitive
  closure of the untyped's child list (`CarvedFrom`);
* every child an untyped records is in the store (`childLive`), and an object is
  recorded by at most one untyped (`childUnique`).

Stated over the tree and the readers rather than the state, so a step that
rewrites none of them (a scheduler or machine write) keeps it definitionally. -/
structure TreeShapeOver (cdt : CapDerivationTree) (cap : SlotRef → Option Capability)
    (present : SeLe4n.ObjId → Prop) (ut : SeLe4n.ObjId → Option UntypedObject)
    (off : SlotRef → Prop) : Prop where
  inTree : ∀ r, cap r ≠ none → cdt.mentions r
  ordered : ∃ P, cdt.TreeOrder P
  live : ∀ r o, namesAt cap r o → present o
  below : ∀ p c o, c ∈ cdt.childrenOf p → namesAt cap c o → cap p ≠ none → ¬ namesAt cap p o →
    ∀ r, namesAt cap r o → CapDerivationTree.CdtChildReachable cdt p r
  chainLinear : ∀ u p r, untypedCapAt cap ut p u → untypedCapAt cap ut r u →
    p = r ∨ CapDerivationTree.CdtChildReachable cdt p r ∨
      CapDerivationTree.CdtChildReachable cdt r p
  chainFirst : ∀ u p r, untypedCapAt cap ut p u → untypedCapAt cap ut r u →
    CapDerivationTree.CdtChildReachable cdt p r →
    ∃ c, (cdt.childrenOf p).head? = some c ∧ untypedCapAt cap ut c u ∧
      (c = r ∨ CapDerivationTree.CdtChildReachable cdt c r)
  notFullLeaf : ∀ p c u U, ¬ off p → cap p = some c → c.target = .object u → ut u = some U →
    c.freeIndex < U.regionSize →
    ∀ r, CapDerivationTree.CdtChildReachable cdt p r → ¬ untypedCapAt cap ut r u
  carvedBelow : ∀ u x, CarvedFrom ut u x → ∀ p r, untypedCapAt cap ut p u → namesAt cap r x →
    CapDerivationTree.CdtChildReachable cdt p r
  childLive : ∀ u U, ut u = some U → ∀ ch ∈ U.children, present ch.objId
  childUnique : ∀ u v U V, ut u = some U → ut v = some V → ∀ ch ∈ U.children,
    ∀ ch' ∈ V.children, ch.objId = ch'.objId → u = v

/-- **The shape of the derivation tree over the slots and the store**: every slot
holding a capability is in the tree (`slotsInTree`), the tree has a preorder,
every capability names an object in the store, the slots naming an object a
derivation changed lie below the slot it was derived from, and the untyped
facts hold everywhere. -/
abbrev CapTreeShape (st : SystemState) : Prop :=
  TreeShapeOver st.cdt st.slotCapAt st.objectPresent st.getUntyped? (fun _ => False)

/-- **The shape off (b) at `a`**: what a copy, mint or transfer of an untyped
capability leaves between recording its derivation and setting its source `a`
full. -/
abbrev CapTreeShapeOff (st : SystemState) (a : SlotRef) : Prop :=
  TreeShapeOver st.cdt st.slotCapAt st.objectPresent st.getUntyped? (· = a)

namespace TreeShapeOver

open CapDerivationTree

variable {cdt : CapDerivationTree} {cap cap' : SlotRef → Option Capability}
  {present present' : SeLe4n.ObjId → Prop} {ut : SeLe4n.ObjId → Option UntypedObject}
  {off : SlotRef → Prop}

/-- **Moving the exceptions**: the shape off `off` is the shape off `off'` when
(b) holds at every slot `off` excepts and `off'` does not. -/
theorem reoff (h : TreeShapeOver cdt cap present ut off) {off' : SlotRef → Prop}
    (hb : ∀ p, ¬ off' p → off p → ∀ c u U, cap p = some c → c.target = .object u →
      ut u = some U → c.freeIndex < U.regionSize →
      ∀ r, CapDerivationTree.CdtChildReachable cdt p r → ¬ untypedCapAt cap ut r u) :
    TreeShapeOver cdt cap present ut off' :=
  { h with
    notFullLeaf := fun p c u U hp hc ht hu hf r hr =>
      (Classical.em (off p)).elim (fun ho => hb p hp ho c u U hc ht hu hf r hr)
        fun ho => h.notFullLeaf p c u U ho hc ht hu hf r hr }

/-- **A slot holding no untyped capability owes (b) nothing**, so the shape off
it is the shape. -/
theorem unoff_of_not_untyped {a : SlotRef} (h : TreeShapeOver cdt cap present ut (· = a))
    (hA : ∀ u, ¬ untypedCapAt cap ut a u) : TreeShapeOver cdt cap present ut (fun _ => False) :=
  h.reoff fun _ _ hp c u _ hc ht hu _ _ _ _ =>
    hA u ⟨c, hp ▸ hc, ht, by rw [hu]; exact Option.some_ne_none _⟩

/-- **What is carved from a recorded object is carved from its recorder**: an
object is recorded by one untyped alone (`childUnique`), so a chain ending at
`x`, which `u` records, ends `… u x`. -/
theorem carvedFrom_last (h : TreeShapeOver cdt cap present ut off) {u x t : SeLe4n.ObjId}
    (hux : recordsChild ut u x) (hx : CarvedFrom ut t x) : t = u ∨ CarvedFrom ut t u := by
  have hU : ∀ {v}, recordsChild ut v x → v = u := fun hv => by
    obtain ⟨V, hv, ch, hch, hc⟩ := hv
    obtain ⟨U, hu, ch', hch', hc'⟩ := hux
    exact h.childUnique _ u V U hv hu ch hch ch' hch' (hc.trans hc'.symm)
  cases hx with
  | child hr => exact .inl (hU hr)
  | trans hv hr => exact .inr (hU hr ▸ hv)

/-- More exceptions only drop obligations. -/
theorem mono_off (h : TreeShapeOver cdt cap present ut off) {off' : SlotRef → Prop}
    (hO : ∀ p, off p → off' p) : TreeShapeOver cdt cap present ut off' :=
  h.reoff fun _ hp ho => absurd (hO _ ho) hp

/-- **A reading whose every occupied slot, and every slot the tree names, holds
the old reading's capability keeps the shape** when no object leaves the store:
emptying slots the tree does not name only drops obligations. -/
theorem of_sub (h : TreeShapeOver cdt cap present ut off)
    (hS : ∀ r, cap' r ≠ none ∨ cdt.mentions r → cap' r = cap r)
    (hP : ∀ o, present o → present' o) : TreeShapeOver cdt cap' present' ut off := by
  have hS1 : ∀ r, cap' r ≠ none → cap' r = cap r := fun r hr => hS r (.inl hr)
  have hN : ∀ {r o}, namesAt cap' r o → namesAt cap r o := fun hr =>
    (namesAt_of_eq (hS1 _ (namesAt_occupied hr))).mp hr
  have hU : ∀ {r u}, untypedCapAt cap' ut r u → untypedCapAt cap ut r u := fun hr =>
    (untypedCapAt_of_eq (hS1 _ hr.occupied)).mp hr
  refine ⟨fun r hr => h.inTree r (by rw [← hS1 r hr]; exact hr), h.ordered,
    fun r o hr => hP o (h.live r o (hN hr)), fun p c o hc hcO hp hpO r hr => ?_,
    fun u p r hp hr => h.chainLinear u p r (hU hp) (hU hr),
    fun u p r hp hr hpr => ?_, fun p c u U ho hc ht hu hf r hr hru => ?_,
    fun u x hx p r hp hr => h.carvedBelow u x hx p r (hU hp) (hN hr),
    fun u U hu ch hch => hP _ (h.childLive u U hu ch hch), h.childUnique⟩
  · exact h.below p c o hc (hN hcO) (by rw [← hS1 p hp]; exact hp)
      (fun e => hpO ((namesAt_of_eq (hS1 p hp)).mpr e)) r (hN hr)
  · obtain ⟨c, hc, hcu, hcr⟩ := h.chainFirst u p r (hU hp) (hU hr) hpr
    have hm := (CapDerivationTree.mentions_of_mem_childrenOf
      (CapDerivationTree.mem_of_head?_eq_some hc)).2
    exact ⟨c, hc, (untypedCapAt_of_eq (hS c (.inr hm))).mpr hcu, hcr⟩
  · have hp : cap' p ≠ none := by rw [hc]; exact Option.some_ne_none _
    exact h.notFullLeaf p c u U ho (by rw [← hS1 p hp]; exact hc) ht hu hf r hr (hU hru)

/-- **The same tree, slots, untypeds and no object lost keep the shape.** -/
theorem of_readers (h : TreeShapeOver cdt cap present ut off) {cdt' : CapDerivationTree}
    {ut' : SeLe4n.ObjId → Option UntypedObject} (hCdt : cdt' = cdt) (hC : ∀ r, cap' r = cap r)
    (hP : ∀ o, present o → present' o) (hUt : ut' = ut) : TreeShapeOver cdt' cap' present' ut' off := by
  subst hCdt hUt; exact h.of_sub (fun r _ => hC r) hP


/-- **A splice keeps the shape** (the reading-level statement of
`CapTreeShape.splice`): the spliced slot `n` reads empty and leaves the tree,
every other slot the new tree names or that holds a capability reads as before,
and a slot with children held a capability, so a child of `n` naming another
object than `n`'s parent lay below `n`'s parent already.  An untyped chain
through `n` closes over it: `n`'s first child takes its place. -/
theorem splice (h : TreeShapeOver cdt cap present ut off) {n : SlotRef} {cdt' : CapDerivationTree}
    (hU : cdt.childrenUnique) (hR : cdt.rootsParentless) (hs : cdt.parentOf n ≠ some n)
    (hCdt : cdt' = cdt.spliceNode n) (hn : cap' n = none)
    (hS : ∀ r, r ≠ n → (cap' r ≠ none ∨ cdt'.mentions r) → cap' r = cap r)
    (hP : ∀ o, present o → present' o)
    (hnOcc : cdt.childrenOf n ≠ [] → cap n ≠ none) : TreeShapeOver cdt' cap' present' ut off := by
  subst hCdt
  obtain ⟨P, hPo⟩ := h.ordered
  have hP' := hPo.spliceNode hU hR hs
  have hnn := CapDerivationTree.not_mem_childrenOf_self hU hs
  have hS1 : ∀ r, r ≠ n → cap' r ≠ none → cap' r = cap r := fun r hr h' => hS r hr (.inl h')
  have hrn : ∀ {r o}, namesAt cap' r o → r ≠ n := fun hr e =>
    namesAt_occupied hr (e ▸ hn)
  have hrnU : ∀ {r u}, untypedCapAt cap' ut r u → r ≠ n := fun hr e => hr.occupied (e ▸ hn)
  have hN : ∀ {r o}, namesAt cap' r o → namesAt cap r o := fun hr =>
    (namesAt_of_eq (hS1 _ (hrn hr) (namesAt_occupied hr))).mp hr
  have hUt : ∀ {r u}, untypedCapAt cap' ut r u → untypedCapAt cap ut r u := fun hr =>
    (untypedCapAt_of_eq (hS1 _ (hrnU hr) hr.occupied)).mp hr
  have hFwd : ∀ {a b}, CdtChildReachable cdt a b → a ≠ n → b ≠ n →
      CdtChildReachable (cdt.spliceNode n) a b := fun r ha hb => r.spliceNode hU hs ha hb
  have hBack : ∀ {a b}, CdtChildReachable (cdt.spliceNode n) a b → CdtChildReachable cdt a b :=
    fun r => r.of_spliceNode hU hs
  have hHead : ∀ {p c}, ((cdt.spliceNode n).childrenOf p).head? = some c →
      (cdt.spliceNode n).mentions c := fun hc =>
    (CapDerivationTree.mentions_of_mem_childrenOf (CapDerivationTree.mem_of_head?_eq_some hc)).2
  refine ⟨fun r hr => ?_, ⟨_, hP'⟩, fun r o hr => hP o (h.live r o (hN hr)),
    fun p c o hc hcO hp hpO r hr => ?_, fun u p r hp hr => ?_, fun u p r hp hr hpr => ?_,
    fun p c u U ho hc ht hu hf r hr hru => ?_,
    fun u x hx p r hp hr => hFwd (h.carvedBelow u x hx p r (hUt hp) (hN hr)) (hrnU hp) (hrn hr),
    fun u U hu ch hch => hP _ (h.childLive u U hu ch hch), h.childUnique⟩
  · have hrn' : r ≠ n := fun e => hr (e ▸ hn)
    refine (hP'.mem_iff r).mp (List.mem_filter.mpr ⟨(hPo.mem_iff r).mpr (h.inTree r ?_),
      by simp [hrn']⟩)
    rw [← hS1 r hrn' hr]; exact hr
  · rw [CapDerivationTree.childrenOf_spliceNode hU hs] at hc
    have hpn : p ≠ n := fun e => by rw [if_pos e] at hc; cases hc
    rw [if_neg hpn] at hc
    have hp' : cap p ≠ none := by rw [← hS1 p hpn hp]; exact hp
    have hpO' : ¬ namesAt cap p o := fun e => hpO ((namesAt_of_eq (hS1 p hpn hp)).mpr e)
    have hr' := hN hr
    have hOld : CdtChildReachable cdt p r := by
      rcases CapDerivationTree.mem_replaceSlot.mp hc with ⟨hcp, -⟩ | ⟨hnp, hcn⟩
      · exact h.below p c o hcp (hN hcO) hp' hpO' r hr'
      · by_cases hnO : namesAt cap n o
        · exact h.below p n o hnp hnO hp' hpO' r hr'
        · exact (CdtChildReachable.child hnp).trans'
            (h.below n c o hcn (hN hcO)
              (hnOcc fun e => by rw [e] at hcn; cases hcn) hnO r hr')
    exact hFwd hOld hpn (hrn hr)
  · rcases h.chainLinear u p r (hUt hp) (hUt hr) with e | e | e
    · exact .inl e
    · exact .inr (.inl (hFwd e (hrnU hp) (hrnU hr)))
    · exact .inr (.inr (hFwd e (hrnU hr) (hrnU hp)))
  · have hpn := hrnU hp
    have hrn' := hrnU hr
    have hch : (cdt.spliceNode n).childrenOf p =
        CapDerivationTree.replaceSlot n (cdt.childrenOf n) (cdt.childrenOf p) := by
      rw [CapDerivationTree.childrenOf_spliceNode hU hs, if_neg hpn]
    obtain ⟨c, hc, hcu, hcr⟩ := h.chainFirst u p r (hUt hp) (hUt hr) (hBack hpr)
    by_cases hcn : c = n
    · rw [hcn] at hc hcu hcr
      have hcr' : CdtChildReachable cdt n r := hcr.resolve_left fun e => hrn' e.symm
      obtain ⟨d, hd, hdu, hdr⟩ := h.chainFirst u n r hcu (hUt hr) hcr'
      have hdn : d ≠ n := fun e => hnn (by
        rw [e] at hd; exact CapDerivationTree.mem_of_head?_eq_some hd)
      have hd' : ((cdt.spliceNode n).childrenOf p).head? = some d := by
        rw [hch]; exact CapDerivationTree.replaceSlot_head_self hc hd
      exact ⟨d, hd', (untypedCapAt_of_eq (hS d hdn (.inr (hHead hd')))).mpr hdu,
        hdr.imp id fun e => hFwd e hdn hrn'⟩
    · have hc' : ((cdt.spliceNode n).childrenOf p).head? = some c := by
        rw [hch]; exact CapDerivationTree.replaceSlot_head_ne hc hcn
      exact ⟨c, hc', (untypedCapAt_of_eq (hS c hcn (.inr (hHead hc')))).mpr hcu,
        hcr.imp id fun e => hFwd e hcn hrn'⟩
  · have hpn : p ≠ n := fun e => by rw [e, hn] at hc; cases hc
    have hp' : cap' p ≠ none := by rw [hc]; exact Option.some_ne_none _
    exact h.notFullLeaf p c u U ho (by rw [← hS1 p hpn hp']; exact hc) ht hu hf r (hBack hr)
      (hUt hru)

/-- **An in-place rewrite of an occupied slot that keeps its target keeps the
shape**, when no object leaves the store and (b) holds at the rewritten slot
unless the new exceptions name it. -/
theorem rewrite (h : TreeShapeOver cdt cap present ut off) {off' : SlotRef → Prop} {a : SlotRef}
    {c c' : Capability} (ha : cap a = some c) (ha' : cap' a = some c')
    (hT : c'.target = c.target) (hS : ∀ r, r ≠ a → cap' r = cap r)
    (hP : ∀ o, present o → present' o) (hOff : ∀ p, p ≠ a → ¬ off' p → ¬ off p)
    (hB : ¬ off' a → ∀ u U, c'.target = .object u → ut u = some U →
      c'.freeIndex < U.regionSize →
      ∀ r, CdtChildReachable cdt a r → ¬ untypedCapAt cap ut r u) :
    TreeShapeOver cdt cap' present' ut off' := by
  have hOcc : ∀ r, cap' r ≠ none ↔ cap r ≠ none := fun r => by
    by_cases e : r = a
    · rw [e, ha, ha']; simp
    · rw [hS r e]
  have hN : ∀ r o, namesAt cap' r o ↔ namesAt cap r o := fun r o => by
    by_cases e : r = a
    · rw [e]; unfold namesAt; rw [ha, ha']; simp [Capability.namedObject_of_target hT]
    · exact namesAt_of_eq (hS r e)
  have hU : ∀ r u, untypedCapAt cap' ut r u ↔ untypedCapAt cap ut r u := fun r u => by
    by_cases e : r = a
    · rw [e]; exact untypedCapAt_of_target ha ha' hT
    · exact untypedCapAt_of_eq (hS r e)
  refine ⟨fun r hr => h.inTree r ((hOcc r).mp hr), h.ordered,
    fun r o hr => hP o (h.live r o ((hN r o).mp hr)), fun p c₀ o hc hcO hp hpO r hr => ?_,
    fun u p r hp hr => h.chainLinear u p r ((hU _ _).mp hp) ((hU _ _).mp hr),
    fun u p r hp hr hpr => ?_, fun p d u U ho hd ht hu hf r hr hru => ?_,
    fun u x hx p r hp hr => h.carvedBelow u x hx p r ((hU _ _).mp hp) ((hN _ _).mp hr),
    fun u U hu ch hch => hP _ (h.childLive u U hu ch hch), h.childUnique⟩
  · exact h.below p c₀ o hc ((hN _ _).mp hcO) ((hOcc p).mp hp)
      (fun e => hpO ((hN _ _).mpr e)) r ((hN _ _).mp hr)
  · obtain ⟨d, hd, hdu, hdr⟩ := h.chainFirst u p r ((hU _ _).mp hp) ((hU _ _).mp hr) hpr
    exact ⟨d, hd, (hU _ _).mpr hdu, hdr⟩
  · by_cases e : p = a
    · rw [e] at ho hd hr
      rw [ha'] at hd
      obtain rfl := Option.some.inj hd
      exact hB ho u U ht hu hf r hr ((hU _ _).mp hru)
    · rw [hS p e] at hd
      exact h.notFullLeaf p d u U (hOff p e ho) hd ht hu hf r hr ((hU _ _).mp hru)

/-- **A rewrite that keeps the target and does not lower the free index keeps
the shape off the same slots.** -/
theorem rewrite_le (h : TreeShapeOver cdt cap present ut off) {a : SlotRef}
    {c c' : Capability} (ha : cap a = some c) (ha' : cap' a = some c')
    (hT : c'.target = c.target) (hFI : c.freeIndex ≤ c'.freeIndex)
    (hS : ∀ r, r ≠ a → cap' r = cap r) (hP : ∀ o, present o → present' o) :
    TreeShapeOver cdt cap' present' ut off :=
  h.rewrite ha ha' hT hS hP (fun _ _ h => h) fun ho u U ht hu hf r hr hru =>
    h.notFullLeaf a c u U ho ha (hT ▸ ht) hu (Nat.lt_of_le_of_lt hFI hf) r hr hru

/-- **A rewrite that keeps the target and sets the free index full takes `a` off
the exceptions**: a full capability owes (b) nothing. -/
theorem rewrite_full {a : SlotRef} (h : TreeShapeOver cdt cap present ut (· = a))
    {c c' : Capability} (ha : cap a = some c) (ha' : cap' a = some c')
    (hT : c'.target = c.target)
    (hFull : ∀ u U, c.target = .object u → ut u = some U → c'.freeIndex = U.regionSize)
    (hS : ∀ r, r ≠ a → cap' r = cap r) (hP : ∀ o, present o → present' o) :
    TreeShapeOver cdt cap' present' ut (fun _ => False) :=
  h.rewrite ha ha' hT hS hP (fun _ hp _ e => hp e) fun _ u U ht hu hf =>
    absurd (hFull u U (hT ▸ ht) hu) (Nat.ne_of_lt hf)

/-- **An insert that records its derivation keeps the shape, off (b) at its
source**: `dst`, outside the tree, receives a capability and becomes the first
child of `src`, which holds one.  The new capability is derived from the
source's (it names what the source names, it is an untyped capability only when
the source's is one to the same untyped, and an untyped source has no child,
seL4's `ensureNoChildren`), or
names an object no slot named, whose untyped records nothing, and which lies
below every capability to an untyped it is carved from once it is below `src`
(a carve's).  The source is off (b) until a copy sets it full. -/
theorem addChild (h : TreeShapeOver cdt cap present ut (fun _ => False)) {src dst : SlotRef}
    {cdt' : CapDerivationTree} (op : DerivationOp)
    (hSrc : cap src ≠ none) (hDst : ¬ cdt.mentions dst)
    (hCdt : cdt' = cdt.addEdge src dst op)
    (hS : ∀ r, r ≠ dst → cap' r = cap r)
    (hP : ∀ o, present o → present' o)
    (hNew : ((∀ o, namesAt cap' dst o → namesAt cap src o) ∧
          (∀ u, untypedCapAt cap' ut dst u → untypedCapAt cap ut src u) ∧
          (∀ u, untypedCapAt cap ut src u → cdt.childrenOf src = [])) ∨
        ((∀ u, untypedCapAt cap ut src u → ∀ r, CdtChildReachable cdt src r →
            ¬ untypedCapAt cap ut r u) ∧
          ∀ o, namesAt cap' dst o → (∀ r, ¬ namesAt cap r o) ∧ present' o ∧
            (∀ t, CarvedFrom ut t o → ∀ p, untypedCapAt cap ut p t →
              p = src ∨ CdtChildReachable cdt p src) ∧
            (∀ U, ut o = some U → U.children = []))) :
    TreeShapeOver cdt' cap' present' ut (· = src) := by
  subst hCdt
  have hsd : src ≠ dst := fun e => hDst (e ▸ h.inTree src hSrc)
  have hN : ∀ {r o}, r ≠ dst → (namesAt cap' r o ↔ namesAt cap r o) :=
    fun hr => namesAt_of_eq (hS _ hr)
  have hUe : ∀ {r u}, r ≠ dst → (untypedCapAt cap' ut r u ↔ untypedCapAt cap ut r u) :=
    fun hr => untypedCapAt_of_eq (hS _ hr)
  have hDstCh : dst ∈ (cdt.addEdge src dst op).childrenOf src := by
    rw [CapDerivationTree.childrenOf_addEdge, if_pos rfl]; exact List.mem_cons_self ..
  have hDstHead : ((cdt.addEdge src dst op).childrenOf src).head? = some dst := by
    rw [CapDerivationTree.childrenOf_addEdge, if_pos rfl]; rfl
  have hChNe : ∀ {q}, q ≠ src → (cdt.addEdge src dst op).childrenOf q = cdt.childrenOf q := by
    intro q hq; rw [CapDerivationTree.childrenOf_addEdge, if_neg hq]
  have hBack : ∀ {a b}, CdtChildReachable (cdt.addEdge src dst op) a b →
      CdtChildReachable cdt a b ∨ ((a = src ∨ CdtChildReachable cdt a src) ∧ b = dst) :=
    fun r => r.of_addEdge hDst hsd
  have hLift : ∀ {a b}, CdtChildReachable cdt a b →
      CdtChildReachable (cdt.addEdge src dst op) a b := fun r => r.addEdge src dst op
  have hToDst : ∀ {a}, (a = src ∨ CdtChildReachable cdt a src) →
      CdtChildReachable (cdt.addEdge src dst op) a dst := by
    intro a ha
    rcases ha with e | r
    · rw [e]; exact .child hDstCh
    · exact (hLift r).trans' (.child hDstCh)
  have hNotDst : ∀ {a}, ¬ CdtChildReachable cdt a dst := fun r => hDst r.mentions_end
  have hDstLeaf : ∀ {b}, ¬ CdtChildReachable (cdt.addEdge src dst op) dst b := fun r =>
    CdtChildReachable.not_of_childless (by
      rw [hChNe (Ne.symm hsd)]; exact CapDerivationTree.childrenOf_eq_nil_of_not_mentions hDst) r
  have hLeaf : ∀ u, untypedCapAt cap ut src u → ∀ r, CdtChildReachable cdt src r →
      ¬ untypedCapAt cap ut r u := by
    rcases hNew with ⟨-, -, hL⟩ | ⟨hL, -⟩
    · intro u hu r hr; exact absurd hr (CdtChildReachable.not_of_childless (hL u hu))
    · exact hL
  -- what `dst` names: what `src` names, or a fresh object
  have hNm : ∀ o, namesAt cap' dst o → namesAt cap src o ∨ ((∀ r, ¬ namesAt cap r o) ∧
      present' o ∧ (∀ t, CarvedFrom ut t o → ∀ p, untypedCapAt cap ut p t →
        p = src ∨ CdtChildReachable cdt p src)) := by
    intro o ho
    rcases hNew with ⟨hNmC, -, -⟩ | ⟨-, hF⟩
    · exact .inl (hNmC o ho)
    · obtain ⟨h1, h2, h3, -⟩ := hF o ho
      exact .inr ⟨h1, h2, h3⟩
  -- an untyped capability at `dst`: in a copy, `src`'s too; never in a carve
  have hDstU : ∀ {u}, untypedCapAt cap' ut dst u →
      (untypedCapAt cap ut src u ∧ cdt.childrenOf src = []) ∨
        ((∀ r, ¬ namesAt cap r u) ∧ ∀ U, ut u = some U → U.children = []) := by
    intro u hu
    rcases hNew with ⟨-, hUC, hL⟩ | ⟨-, hF⟩
    · exact .inl ⟨hUC u hu, hL u (hUC u hu)⟩
    · obtain ⟨h1, -, -, h4⟩ := hF u hu.namesAt
      exact .inr ⟨h1, h4⟩
  refine ⟨fun r hr => ?_, ?_, fun r o hr => ?_, fun p c o hc hcO hp hpO r hr => ?_,
    fun u p r hp hr => ?_, fun u p r hp hr hpr => ?_, fun p c u U ho hc ht hu hf r hr hru => ?_,
    fun t x hx p r hp hr => ?_, fun u U hu ch hch => hP _ (h.childLive u U hu ch hch),
    h.childUnique⟩
  · rw [CapDerivationTree.mentions_addEdge]
    by_cases e : r = dst
    · exact .inr (.inr e)
    · exact .inl (h.inTree r (by rw [← hS r e]; exact hr))
  · obtain ⟨P, hPo⟩ := h.ordered
    exact ⟨_, hPo.addEdge (h.inTree src hSrc) hDst op⟩
  · by_cases e : r = dst
    · rw [e] at hr
      rcases hNm o hr with hs | ⟨-, hl, -⟩
      · exact hP o (h.live src o hs)
      · exact hl
    · exact hP o (h.live r o ((hN e).mp hr))
  · have hcases : (p = src ∧ c = dst) ∨ c ∈ cdt.childrenOf p := by
      rw [CapDerivationTree.childrenOf_addEdge] at hc
      split at hc
      · next e => rcases List.mem_cons.mp hc with e' | e'
                  · exact .inl ⟨e, e'⟩
                  · exact .inr e'
      · exact .inr hc
    rcases hcases with ⟨e1, e2⟩ | hcOld
    · rw [e1] at hpO; rw [e2] at hcO
      rcases hNm o hcO with hs | ⟨hno, -, -⟩
      · exact absurd ((hN hsd).mpr hs) hpO
      · by_cases e : r = dst
        · rw [e, e1]; exact .child hDstCh
        · exact absurd ((hN e).mp hr) (hno r)
    · have hm := CapDerivationTree.mentions_of_mem_childrenOf hcOld
      have hcd : c ≠ dst := fun e => hDst (e ▸ hm.2)
      have hpd : p ≠ dst := fun e => hDst (e ▸ hm.1)
      have hcO' := (hN hcd).mp hcO
      have key := h.below p c o hcOld hcO' (by rw [← hS p hpd]; exact hp)
        (fun e => hpO ((hN hpd).mpr e))
      by_cases e : r = dst
      · rw [e] at hr ⊢
        rcases hNm o hr with hs | ⟨hno, -, -⟩
        · exact hToDst (.inr (key src hs))
        · exact absurd hcO' (hno c)
      · exact hLift (key r ((hN e).mp hr))
  · by_cases ep : p = dst
    · by_cases er : r = dst
      · exact .inl (ep.trans er.symm)
      · rw [ep] at hp
        rcases hDstU hp with ⟨hsu, hL⟩ | ⟨hno, -⟩
        · rcases h.chainLinear u src r hsu ((hUe er).mp hr) with e | e | e
          · exact .inr (.inr (by rw [ep, ← e]; exact .child hDstCh))
          · exact absurd e (CdtChildReachable.not_of_childless hL)
          · exact .inr (.inr (by rw [ep]; exact hToDst (.inr e)))
        · exact absurd ((hUe er).mp hr).namesAt (hno r)
    · by_cases er : r = dst
      · rw [er] at hr
        rcases hDstU hr with ⟨hsu, hL⟩ | ⟨hno, -⟩
        · rcases h.chainLinear u p src ((hUe ep).mp hp) hsu with e | e | e
          · exact .inr (.inl (by rw [er, e]; exact .child hDstCh))
          · exact .inr (.inl (by rw [er]; exact hToDst (.inr e)))
          · exact absurd e (CdtChildReachable.not_of_childless hL)
        · exact absurd ((hUe ep).mp hp).namesAt (hno p)
      · rcases h.chainLinear u p r ((hUe ep).mp hp) ((hUe er).mp hr) with e | e | e
        · exact .inl e
        · exact .inr (.inl (hLift e))
        · exact .inr (.inr (hLift e))
  · have hpd : p ≠ dst := fun e => hDstLeaf (e ▸ hpr)
    have hpOld := (hUe hpd).mp hp
    have hHeadMem : ∀ {c}, (cdt.childrenOf p).head? = some c → c ≠ dst := fun hc e =>
      hDst (e ▸ (CapDerivationTree.mentions_of_mem_childrenOf
        (CapDerivationTree.mem_of_head?_eq_some hc)).2)
    rcases hBack hpr with hold | ⟨hps, er⟩
    · have hrd : r ≠ dst := fun e => hNotDst (e ▸ hold)
      have hr0 := (hUe hrd).mp hr
      have hpsrc : p ≠ src := fun e => hLeaf u (e ▸ hpOld) r (e ▸ hold) hr0
      obtain ⟨c, hc, hcu, hcr⟩ := h.chainFirst u p r hpOld hr0 hold
      exact ⟨c, by rw [hChNe hpsrc]; exact hc, (hUe (hHeadMem hc)).mpr hcu, hcr.imp id hLift⟩
    · rw [er] at hr
      rcases hDstU hr with ⟨hsu, hL⟩ | ⟨hno, -⟩
      · rcases hps with e | hps
        · rw [e]; exact ⟨dst, hDstHead, hr, .inl er.symm⟩
        · have hpsrc : p ≠ src := fun e =>
            absurd (e ▸ hps) (CdtChildReachable.not_of_childless (b := src) hL)
          obtain ⟨c, hc, hcu, hcr⟩ := h.chainFirst u p src hpOld hsu hps
          refine ⟨c, by rw [hChNe hpsrc]; exact hc, (hUe (hHeadMem hc)).mpr hcu, .inr ?_⟩
          rw [er]
          rcases hcr with e | e
          · rw [e]; exact .child hDstCh
          · exact hToDst (.inr e)
      · exact absurd hpOld.namesAt (hno p)
  · have hpd : p ≠ dst := fun e => hDstLeaf (e ▸ hr)
    have hc0 : cap p = some c := by rw [← hS p hpd]; exact hc
    rcases hBack hr with hold | ⟨hps, er⟩
    · have hrd : r ≠ dst := fun e => hNotDst (e ▸ hold)
      exact h.notFullLeaf p c u U id hc0 ht hu hf r hold ((hUe hrd).mp hru)
    · rw [er] at hru
      have hpOld : untypedCapAt cap ut p u := ⟨c, hc0, ht, by rw [hu]; exact Option.some_ne_none _⟩
      rcases hDstU hru with ⟨hsu, -⟩ | ⟨hno, -⟩
      · rcases hps with e | hps
        · exact ho e
        · exact h.notFullLeaf p c u U id hc0 ht hu hf src hps hsu
      · exact hno p hpOld.namesAt
  · by_cases ep : p = dst
    · rw [ep] at hp
      rcases hDstU hp with ⟨hsu, hL⟩ | ⟨-, hch⟩
      · exfalso
        by_cases er : r = dst
        · rw [er] at hr
          have hxt : x = t := by
            obtain ⟨c1, h1, h1o⟩ := hr
            obtain ⟨c2, h2, h2t, -⟩ := hp
            rw [h1] at h2
            obtain rfl := Option.some.inj h2
            simp [Capability.namedObject, h2t] at h1o
            exact h1o.symm
          rw [hxt] at hx
          exact CdtChildReachable.not_of_childless hL
            (h.carvedBelow t t hx src src hsu hsu.namesAt)
        · exact CdtChildReachable.not_of_childless hL
            (h.carvedBelow t x hx src r hsu ((hN er).mp hr))
      · exact absurd hx (CarvedFrom.not_of_childless hch)
    · have hpOld := (hUe ep).mp hp
      by_cases er : r = dst
      · rw [er] at hr ⊢
        rcases hNm x hr with hs | ⟨-, -, hF⟩
        · exact hToDst (.inr (h.carvedBelow t x hx p src hpOld hs))
        · exact hToDst (hF t hx p hpOld)
      · exact hLift (h.carvedBelow t x hx p r hpOld ((hN er).mp hr))

/-- **A carve's insert keeps the shape with no exception**: the new capability
names a fresh object and the source has no strict descendant naming its untyped,
so (b) holds at the source too. -/
theorem addChild_fresh (h : TreeShapeOver cdt cap present ut (fun _ => False))
    {src dst : SlotRef} {cdt' : CapDerivationTree} (op : DerivationOp)
    (hSrc : cap src ≠ none) (hDst : ¬ cdt.mentions dst)
    (hCdt : cdt' = cdt.addEdge src dst op)
    (hS : ∀ r, r ≠ dst → cap' r = cap r)
    (hP : ∀ o, present o → present' o)
    (hLeaf : ∀ u, untypedCapAt cap ut src u → ∀ r, CdtChildReachable cdt src r →
        ¬ untypedCapAt cap ut r u)
    (hFresh : ∀ o, namesAt cap' dst o → (∀ r, ¬ namesAt cap r o) ∧ present' o ∧
      (∀ t, CarvedFrom ut t o → ∀ p, untypedCapAt cap ut p t →
        p = src ∨ CdtChildReachable cdt p src) ∧
      (∀ U, ut o = some U → U.children = [])) :
    TreeShapeOver cdt' cap' present' ut (fun _ => False) := by
  have hsd : src ≠ dst := fun e => hDst (e ▸ h.inTree src hSrc)
  have h' := h.addChild op hSrc hDst hCdt hS hP (.inr ⟨hLeaf, hFresh⟩)
  subst hCdt
  refine h'.reoff fun p _ ho c u U hc ht hu _ r hr hru => ?_
  rw [ho] at hc hr
  have hc0 : cap src = some c := by rw [← hS src hsd]; exact hc
  have hsu : untypedCapAt cap ut src u := ⟨c, hc0, ht, by rw [hu]; exact Option.some_ne_none _⟩
  rcases hr.of_addEdge hDst hsd with hold | ⟨-, er⟩
  · have hrd : r ≠ dst := fun e => hDst (e ▸ hold.mentions_end)
    exact hLeaf u hsu r hold ((untypedCapAt_of_eq (hS r hrd)).mp hru)
  · rw [er] at hru
    exact (hFresh u hru.namesAt).1 src hsu.namesAt

/-- **A move keeps the shape** (the reading-level statement of
`CapTreeShape.move`): the source's capability goes to `new`, outside the tree,
which takes the source's place; every other slot keeps its capability, and every
descent, untyped chain included, is renamed with the slot. -/
theorem move (h : TreeShapeOver cdt cap present ut (fun _ => False)) {old new : SlotRef}
    {cdt' : CapDerivationTree} (hon : old ≠ new)
    (hOld : cap old ≠ none) (hNew : ¬ cdt.mentions new)
    (hCdt : cdt' = cdt.moveNode old new) (hOld' : cap' old = none)
    (hMoved : cap' new = cap old)
    (hS : ∀ r, r ≠ old → r ≠ new → cap' r = cap r)
    (hP : ∀ o, present o → present' o) :
    TreeShapeOver cdt' cap' present' ut (fun _ => False) := by
  subst hCdt
  obtain ⟨P, hPo⟩ := h.ordered
  have hP' := hPo.moveNode hNew hon
  have hBackC : ∀ y, y ≠ old → cap' y = cap (CapDerivationTree.renameSlot new old y) := by
    intro y hy
    by_cases e : y = new
    · rw [e]; simp [CapDerivationTree.renameSlot, hMoved]
    · rw [hS y hy e]; simp [CapDerivationTree.renameSlot, e]
  have hForth : ∀ y, y ≠ old → CapDerivationTree.renameSlot old new
      (CapDerivationTree.renameSlot new old y) = y := fun _ hy =>
    CapDerivationTree.renameSlot_forth hy
  have hro : ∀ {r o}, namesAt cap' r o → r ≠ old := fun hr e =>
    namesAt_occupied hr (e ▸ hOld')
  have hroU : ∀ {r u}, untypedCapAt cap' ut r u → r ≠ old := fun hr e => hr.occupied (e ▸ hOld')
  have hN : ∀ {r o}, r ≠ old → (namesAt cap' r o ↔
      namesAt cap (CapDerivationTree.renameSlot new old r) o) :=
    fun hr => namesAt_of_eq (hBackC _ hr)
  have hUt : ∀ {r u}, r ≠ old → (untypedCapAt cap' ut r u ↔
      untypedCapAt cap ut (CapDerivationTree.renameSlot new old r) u) :=
    fun hr => untypedCapAt_of_eq (hBackC _ hr)
  have hBk : ∀ {a b}, CdtChildReachable (cdt.moveNode old new) a b →
      CdtChildReachable cdt (CapDerivationTree.renameSlot new old a)
        (CapDerivationTree.renameSlot new old b) := fun r => r.of_moveNode hNew hon
  have hFwd' : ∀ {a b}, a ≠ old → b ≠ old →
      CdtChildReachable cdt (CapDerivationTree.renameSlot new old a)
        (CapDerivationTree.renameSlot new old b) → CdtChildReachable (cdt.moveNode old new) a b := by
    intro a b ha hb r
    have := r.moveNode hNew hon
    rwa [hForth a ha, hForth b hb] at this
  refine ⟨fun r hr => ?_, ⟨_, hP'⟩, fun r o hr => hP o (h.live _ o ((hN (hro hr)).mp hr)),
    fun p c o hc hcO hp hpO r hr => ?_, fun u p r hp hr => ?_, fun u p r hp hr hpr => ?_,
    fun p c u U _ hc ht hu hf r hr hru => ?_, fun t x hx p r hp hr => ?_,
    fun u U hu ch hch => hP _ (h.childLive u U hu ch hch), h.childUnique⟩
  · refine (hP'.mem_iff r).mp (List.mem_map.mpr ?_)
    by_cases e : r = new
    · exact ⟨old, (hPo.mem_iff old).mpr (h.inTree old hOld),
        by simp [CapDerivationTree.renameSlot, e]⟩
    · have hro' : r ≠ old := fun e' => hr (e' ▸ hOld')
      exact ⟨r, (hPo.mem_iff r).mpr (h.inTree r (by rw [← hS r hro' e]; exact hr)),
        by simp [CapDerivationTree.renameSlot, hro']⟩
  · rw [CapDerivationTree.childrenOf_moveNode hNew hon] at hc
    have hpo : p ≠ old := fun e => by rw [if_pos e] at hc; cases hc
    rw [if_neg hpo] at hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    have hxn : x ≠ new := fun e => hNew (e ▸ (CapDerivationTree.mentions_of_mem_childrenOf hx).2)
    have hcO' := (hN (hro hcO)).mp hcO
    rw [CapDerivationTree.renameSlot_back hxn] at hcO'
    have key := h.below _ x o hx hcO' (by rw [← hBackC p hpo]; exact hp)
      (fun e => hpO ((hN hpo).mpr e)) _ ((hN (hro hr)).mp hr)
    have := key.moveNode hNew hon
    rw [hForth p hpo, hForth r (hro hr)] at this
    exact this
  · have hpo := hroU hp
    have hro' := hroU hr
    rcases h.chainLinear u _ _ ((hUt hpo).mp hp) ((hUt hro').mp hr) with e | e | e
    · exact .inl (by rw [← hForth p hpo, ← hForth r hro', e])
    · exact .inr (.inl (hFwd' hpo hro' e))
    · exact .inr (.inr (hFwd' hro' hpo e))
  · have hpo := hroU hp
    have hro' := hroU hr
    obtain ⟨c, hc, hcu, hcr⟩ :=
      h.chainFirst u _ _ ((hUt hpo).mp hp) ((hUt hro').mp hr) (hBk hpr)
    have hcn : c ≠ new := fun e => hNew (e ▸ (CapDerivationTree.mentions_of_mem_childrenOf
      (CapDerivationTree.mem_of_head?_eq_some hc)).2)
    have hco := CapDerivationTree.renameSlot_ne_old hon c
    refine ⟨CapDerivationTree.renameSlot old new c, ?_, ?_, ?_⟩
    · rw [CapDerivationTree.childrenOf_moveNode hNew hon, if_neg hpo, List.head?_map, hc]; rfl
    · rw [hUt hco, CapDerivationTree.renameSlot_back hcn]; exact hcu
    · rcases hcr with e | e
      · exact .inl (by rw [e, hForth r hro'])
      · have := e.moveNode hNew hon
        rw [hForth r hro'] at this
        exact .inr this
  · have hpo : p ≠ old := fun e => by rw [e, hOld'] at hc; cases hc
    exact h.notFullLeaf _ c u U id (by rw [← hBackC p hpo]; exact hc) ht hu hf _ (hBk hr)
      ((hUt (hroU hru)).mp hru)
  · have hpo := hroU hp
    have hro' := hro hr
    exact hFwd' hpo hro' (h.carvedBelow t x hx _ _ ((hUt hpo).mp hp) ((hN hro').mp hr))

/-- **Recording a carved object keeps the shape**: untyped `u`, keeping its
region, records `w`, a fresh object no slot names and now in the store, whose own
untyped record (if it is one) records nothing; every other untyped record is
kept.  Nothing names `w` yet, so no capability owes it a place. -/
theorem carveRecord (h : TreeShapeOver cdt cap present ut off)
    {ut' : SeLe4n.ObjId → Option UntypedObject} {u w : SeLe4n.ObjId} {U U' : UntypedObject}
    (hU : ut u = some U) (hU' : ut' u = some U') (hReg : U'.regionSize = U.regionSize)
    (hCh : ∀ ch ∈ U'.children, ch ∈ U.children ∨ ch.objId = w)
    (hOther : ∀ v, v ≠ u → v ≠ w → ut' v = ut v)
    (hW : ∀ W, ut' w = some W → W.children = [])
    (hw : ∀ r, ¬ namesAt cap r w) (hwP : ¬ present w) (hwP' : present' w)
    (hP : ∀ o, present o → present' o) :
    TreeShapeOver cdt cap present' ut' off := by
  have hNone : ∀ v, v ≠ w → (ut' v ≠ none ↔ ut v ≠ none) := by
    intro v hv
    by_cases e : v = u
    · rw [e, hU, hU']; simp
    · rw [hOther v e hv]
  have hNw : ∀ {r c v}, cap r = some c → c.target = .object v → v ≠ w := fun hc ht e =>
    hw _ ⟨_, hc, by simp [Capability.namedObject, ht, e]⟩
  have hUt : ∀ {r v}, untypedCapAt cap ut' r v → untypedCapAt cap ut r v ∧ v ≠ w := by
    intro r v hv
    obtain ⟨c, hc, ht, hv⟩ := hv
    exact ⟨⟨c, hc, ht, (hNone v (hNw hc ht)).mp hv⟩, hNw hc ht⟩
  have hUt' : ∀ {r v}, untypedCapAt cap ut r v → v ≠ w → untypedCapAt cap ut' r v := by
    intro r v hv hvw
    obtain ⟨c, hc, ht, hv⟩ := hv
    exact ⟨c, hc, ht, (hNone v hvw).mpr hv⟩
  have hRec : ∀ {v x}, recordsChild ut' v x →
      v ≠ w ∧ (recordsChild ut v x ∨ (v = u ∧ x = w)) := by
    intro v x hr
    obtain ⟨V, hv, ch, hch, hx⟩ := hr
    have hvw : v ≠ w := fun e => by rw [e] at hv; rw [hW V hv] at hch; cases hch
    refine ⟨hvw, ?_⟩
    by_cases e : v = u
    · rw [e, hU'] at hv
      obtain rfl := Option.some.inj hv
      rcases hCh ch hch with h1 | h1
      · exact .inl ⟨U, by rw [e]; exact hU, ch, h1, hx⟩
      · exact .inr ⟨e, hx.symm.trans h1⟩
    · rw [hOther v e hvw] at hv; exact .inl ⟨V, hv, ch, hch, hx⟩
  have hCF : ∀ {t x}, CarvedFrom ut' t x →
      CarvedFrom ut t x ∨ ((t = u ∨ CarvedFrom ut t u) ∧ x = w) := by
    intro t x hx
    induction hx with
    | child hr =>
      rcases (hRec hr).2 with h1 | ⟨e1, e2⟩
      · exact .inl (.child h1)
      · exact .inr ⟨.inl e1, e2⟩
    | trans _ hr ih =>
      obtain ⟨hvw, hr'⟩ := hRec hr
      rcases ih with ih | ⟨-, e⟩
      · rcases hr' with h1 | ⟨e1, e2⟩
        · exact .inl (.trans ih h1)
        · exact .inr ⟨.inr (e1 ▸ ih), e2⟩
      · exact absurd e hvw
  refine ⟨h.inTree, h.ordered, fun r o hr => hP o (h.live r o hr), h.below,
    fun v p r hp hr => h.chainLinear v p r (hUt hp).1 (hUt hr).1,
    fun v p r hp hr hpr => ?_, fun p c v V ho hc ht hv hf r hr hru => ?_,
    fun t x hx p r hp hr => ?_, fun v V hv ch hch => ?_,
    fun a b A B ha hb ch hch ch' hch' hc => ?_⟩
  · obtain ⟨c, hc, hcu, hcr⟩ := h.chainFirst v p r (hUt hp).1 (hUt hr).1 hpr
    exact ⟨c, hc, hUt' hcu (hUt hp).2, hcr⟩
  · have hvw := hNw hc ht
    obtain ⟨V0, hv0, hreg⟩ : ∃ V0, ut v = some V0 ∧ V.regionSize = V0.regionSize := by
      by_cases e : v = u
      · rw [e, hU'] at hv
        obtain rfl := Option.some.inj hv
        exact ⟨U, by rw [e]; exact hU, hReg⟩
      · rw [hOther v e hvw] at hv; exact ⟨V, hv, rfl⟩
    exact h.notFullLeaf p c v V0 ho hc ht hv0 (by rw [← hreg]; exact hf) r hr (hUt hru).1
  · rcases hCF hx with hx' | ⟨-, e⟩
    · exact h.carvedBelow t x hx' p r (hUt hp).1 hr
    · exact absurd (e ▸ hr) (hw r)
  · have hvw : v ≠ w := fun e => by rw [e] at hv; rw [hW V hv] at hch; cases hch
    by_cases e : v = u
    · rw [e, hU'] at hv
      obtain rfl := Option.some.inj hv
      rcases hCh ch hch with h1 | h1
      · exact hP _ (h.childLive u U hU ch h1)
      · rw [h1]; exact hwP'
    · rw [hOther v e hvw] at hv; exact hP _ (h.childLive v V hv ch hch)
  · have hrA : recordsChild ut' a ch.objId := ⟨A, ha, ch, hch, rfl⟩
    have hrB : recordsChild ut' b ch.objId := ⟨B, hb, ch', hch', hc.symm⟩
    obtain ⟨-, hA⟩ := hRec hrA
    obtain ⟨-, hB⟩ := hRec hrB
    have hlive : ∀ {v}, recordsChild ut v ch.objId → ch.objId ≠ w := by
      intro v hv e
      obtain ⟨V, hv, c0, hc0, hx⟩ := hv
      exact hwP (by rw [← e, ← hx]; exact h.childLive v V hv c0 hc0)
    rcases hA with hA | ⟨ea, ex⟩ <;> rcases hB with hB | ⟨eb, ex'⟩
    · obtain ⟨A0, ha0, c1, hc1, hx1⟩ := hA
      obtain ⟨B0, hb0, c2, hc2, hx2⟩ := hB
      exact h.childUnique a b A0 B0 ha0 hb0 c1 hc1 c2 hc2 (hx1.trans hx2.symm)
    · exact absurd ex' (hlive hA)
    · exact absurd ex (hlive hB)
    · exact ea.trans eb.symm

/-- **A step that keeps the tree, the slots, the untyped records and every
object keeps the shape, off the same slots.** -/
theorem of_frame {st st' : SystemState} {off : SlotRef → Prop}
    (h : TreeShapeOver st.cdt st.slotCapAt st.objectPresent st.getUntyped? off)
    (hF : SlotTreeFrame st st') :
    TreeShapeOver st'.cdt st'.slotCapAt st'.objectPresent st'.getUntyped? off :=
  h.of_readers hF.cdt hF.slotCapAt hF.present hF.untyped

end TreeShapeOver

namespace CapTreeShape

variable {st st' : SystemState}

/-- A slot holding a capability is in the preorder. -/
theorem mem_order (h : CapTreeShape st) {P : List SlotRef} (hP : st.cdt.TreeOrder P)
    {r : SlotRef} (hr : st.slotCapAt r ≠ none) : r ∈ P :=
  (hP.mem_iff r).mpr (h.inTree r hr)

/-- **A step that keeps the tree and every slot keeps the shape** when no object
leaves the store and every untyped record is kept. -/
theorem of_frame (h : CapTreeShape st) (hF : SlotTreeFrame st st') : CapTreeShape st' :=
  TreeShapeOver.of_frame h hF

/-- **A step that keeps the tree and the untyped records, and whose every
occupied slot and every slot the tree names holds the pre-state's capability,
keeps the shape** when no object leaves the store. -/
theorem of_sub (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt)
    (hS : ∀ r, st'.slotCapAt r ≠ none ∨ st.cdt.mentions r → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hUt : st'.getUntyped? = st.getUntyped?) : CapTreeShape st' := by
  unfold CapTreeShape; rw [hCdt, hUt]; exact TreeShapeOver.of_sub h hS hP

/-- **An in-place rewrite of an occupied slot that keeps its target and does not
lower its free index keeps the shape**, when no object leaves the store and
every untyped record is kept. -/
theorem rewrite (h : CapTreeShape st) (hCdt : st'.cdt = st.cdt) {a : SlotRef}
    {c c' : Capability} (ha : st.slotCapAt a = some c) (ha' : st'.slotCapAt a = some c')
    (hT : c'.target = c.target) (hFI : c.freeIndex ≤ c'.freeIndex)
    (hS : ∀ r, r ≠ a → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hUt : st'.getUntyped? = st.getUntyped?) : CapTreeShape st' := by
  unfold CapTreeShape; rw [hCdt, hUt]; exact TreeShapeOver.rewrite_le h ha ha' hT hFI hS hP

/-- **A delete's splice keeps the shape**: the deleted slot `n` is empty and
leaves the tree, and every other slot keeps its capability and its place in the
preorder (`TreeOrder.spliceNode`); a slot with children held a capability, so a
child of `n` naming another object than `n`'s parent lay below `n`'s parent
already, and an untyped chain through `n` closes over it
(`TreeShapeOver.splice`). -/
theorem splice (h : CapTreeShape st) {n : SlotRef} (hU : st.cdt.childrenUnique)
    (hR : st.cdt.rootsParentless) (hs : st.cdt.parentOf n ≠ some n)
    (hCdt : st'.cdt = st.cdt.spliceNode n) (hn : st'.slotCapAt n = none)
    (hS : ∀ r, r ≠ n → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hUt : st'.getUntyped? = st.getUntyped?)
    (hnOcc : st.cdt.childrenOf n ≠ [] → st.slotCapAt n ≠ none) : CapTreeShape st' := by
  unfold CapTreeShape; rw [hUt]
  exact TreeShapeOver.splice h hU hR hs hCdt hn (fun r hr _ => hS r hr) hP hnOcc

/-- **A move keeps the shape**: the source's capability goes to `new`, empty
and outside the tree, which takes the source's place in the preorder
(`TreeOrder.moveNode`); every other slot keeps its capability, and every descent
is renamed with the slot. -/
theorem move (h : CapTreeShape st) {old new : SlotRef} (hon : old ≠ new)
    (hOld : st.slotCapAt old ≠ none) (hNew : ¬ st.cdt.mentions new)
    (hCdt : st'.cdt = st.cdt.moveNode old new) (hOld' : st'.slotCapAt old = none)
    (hMoved : st'.slotCapAt new = st.slotCapAt old)
    (hS : ∀ r, r ≠ old → r ≠ new → st'.slotCapAt r = st.slotCapAt r)
    (hP : ∀ o, st.objectPresent o → st'.objectPresent o)
    (hUt : st'.getUntyped? = st.getUntyped?) : CapTreeShape st' := by
  unfold CapTreeShape; rw [hUt]
  exact TreeShapeOver.move h hon hOld hNew hCdt hOld' hMoved hS hP

end CapTreeShape

end SystemState

end SeLe4n.Model
