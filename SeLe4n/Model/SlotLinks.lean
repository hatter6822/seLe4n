-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# Slot derivation links in the state (WS-ZA ZA5.3 part 4)

The derivation links every slot holds, read from and written to its CNode's link
words.  `SystemState.slotLinkAt` is the state's `LinkView`; the tree operations'
link writes (`linkAddChild`, …) write words in place and are proven to act on
that view as `LinkView.addChild`, … do, so the agreement proofs of
`SeLe4n.Model.Object.DerivationLinks` carry over to the state.
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

namespace SystemState

/-- **The derivation links the slots hold**: link `f` of slot `r`, read from its
CNode's link words.  A slot of no CNode holds none. -/
def slotLinkAt (st : SystemState) : LinkView := fun r f =>
  match st.getCNode? r.cnode with
  | some cn => cn.linkAt r.slot f
  | none => none

theorem slotLinkAt_def (st : SystemState) (r : SlotRef) (f : LinkField) :
    st.slotLinkAt r f = match st.objects[r.cnode]? with
      | some (.cnode cn) => cn.linkAt r.slot f
      | _ => none := by
  unfold slotLinkAt getCNode?
  cases st.objects[r.cnode]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- The CNode word of link `f` of slot `(o, s)` (0 when it has no target). -/
@[inline] def slotLinkNodeWord (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) : Nat :=
  match st.getCNode? o with
  | some cn => cn.linkNodeWord s f
  | none => 0

theorem slotLinkNodeWord_def (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) : st.slotLinkNodeWord o s f = match st.objects[o]? with
      | some (.cnode cn) => cn.linkNodeWord s f
      | _ => 0 := by
  unfold slotLinkNodeWord getCNode?
  cases st.objects[o]? with
  | none => rfl
  | some ob => cases ob <;> rfl

/-- The slot word of link `f` of slot `(o, s)`. -/
@[inline] def slotLinkSlotWord (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) : Nat :=
  match st.getCNode? o with
  | some cn => cn.linkSlotWord s f
  | none => 0

theorem slotLinkSlotWord_def (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) : st.slotLinkSlotWord o s f = match st.objects[o]? with
      | some (.cnode cn) => cn.linkSlotWord s f
      | _ => 0 := by
  unfold slotLinkSlotWord getCNode?
  cases st.objects[o]? with
  | none => rfl
  | some ob => cases ob <;> rfl

theorem slotLinkAt_eq_decode (st : SystemState) (r : SlotRef) (f : LinkField) :
    st.slotLinkAt r f =
      decodeLink (st.slotLinkNodeWord r.cnode r.slot f) (st.slotLinkSlotWord r.cnode r.slot f) := by
  rw [slotLinkAt_def, slotLinkNodeWord_def, slotLinkSlotWord_def]
  split <;> rfl

/-- **`st'` is `st` with only derivation-link words rewritten**: every other
field is `st`'s, and every object is unchanged or a CNode that differs only in
its links.  Every link writer below is one (`linksOnlyWrite` lemmas), and every
reader that ignores links — slot lookups, the CNode's geometry, every other
object — reads the same in both. -/
def linksOnlyWrite (st st' : SystemState) : Prop :=
  st' = { st with objects := st'.objects } ∧
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ cn cn' : CNode, st.objects[oid]? = some (.cnode cn) ∧
      st'.objects[oid]? = some (.cnode cn') ∧ cn'.withoutLinks = cn.withoutLinks

namespace linksOnlyWrite

theorem refl (st : SystemState) : linksOnlyWrite st st :=
  ⟨rfl, fun _ => .inl rfl⟩

theorem trans {st₁ st₂ st₃ : SystemState} (h₁ : linksOnlyWrite st₁ st₂)
    (h₂ : linksOnlyWrite st₂ st₃) : linksOnlyWrite st₁ st₃ := by
  refine ⟨?_, fun oid => ?_⟩
  · rw [h₂.1, h₁.1]
  · rcases h₂.2 oid with e₂ | ⟨b, c, hb, hc, hbc⟩
    · rcases h₁.2 oid with e₁ | ⟨a, b', ha, hb', hab⟩
      · exact .inl (e₂.trans e₁)
      · exact .inr ⟨a, b', ha, e₂.trans hb', hab⟩
    · rcases h₁.2 oid with e₁ | ⟨a, b', ha, hb', hab⟩
      · exact .inr ⟨b, c, e₁ ▸ hb, hc, hbc⟩
      · rw [hb'] at hb; cases hb
        exact .inr ⟨a, c, ha, hc, hbc.trans hab⟩

/-- Every object other than a CNode reads the same. -/
theorem objects_of_not_cnode {st st' : SystemState} (h : linksOnlyWrite st st')
    {oid : SeLe4n.ObjId} {o : KernelObject} (ho : st.objects[oid]? = some o)
    (hn : ∀ cn, o ≠ .cnode cn) : st'.objects[oid]? = some o := by
  rcases h.2 oid with e | ⟨cn, _, hc, _, _⟩
  · rw [e, ho]
  · rw [ho] at hc; cases hc; exact absurd rfl (hn cn)

theorem cnode_back {st st' : SystemState} (h : linksOnlyWrite st st') {oid : SeLe4n.ObjId}
    {cn' : CNode} (h' : st'.objects[oid]? = some (.cnode cn')) :
    ∃ cn, st.objects[oid]? = some (.cnode cn) ∧ cn'.withoutLinks = cn.withoutLinks := by
  rcases h.2 oid with e | ⟨cn, cn'', ha, hb, hc⟩
  · exact ⟨cn', e ▸ h', rfl⟩
  · rw [hb] at h'; cases h'; exact ⟨cn, ha, hc⟩

theorem cnode_fwd {st st' : SystemState} (h : linksOnlyWrite st st') {oid : SeLe4n.ObjId}
    {cn : CNode} (hc : st.objects[oid]? = some (.cnode cn)) :
    ∃ cn', st'.objects[oid]? = some (.cnode cn') ∧ cn'.withoutLinks = cn.withoutLinks := by
  rcases h.2 oid with e | ⟨cn0, cn', ha, hb, hw⟩
  · exact ⟨cn, e.trans hc, rfl⟩
  · rw [hc] at ha; cases ha; exact ⟨cn', hb, hw⟩

theorem obj_back {st st' : SystemState} (h : linksOnlyWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (h' : st'.objects[oid]? = some o) (hn : ∀ cn, o ≠ .cnode cn) :
    st.objects[oid]? = some o := by
  rcases h.2 oid with e | ⟨cn, cn', ha, hb, hc⟩
  · rw [← e]; exact h'
  · rw [hb] at h'; cases h'; exact absurd rfl (hn cn')

/-- Every field but the objects is the pre-state's. -/
theorem fields {st st' : SystemState} (h : linksOnlyWrite st st') :
    st' = { st with objects := st'.objects } := h.1

end linksOnlyWrite

/-- A slot inside a live CNode's slot array: a slot whose links can be written. -/
def slotInCNode (st : SystemState) (r : SlotRef) : Prop :=
  ∃ cn, st.objects[r.cnode]? = some (.cnode cn) ∧ r.slot.toNat < 2 ^ cn.radixWidth

/-- **Write link `f` of slot `(o, s)`** as its two words, in place: the CNode
is rewritten in its object-table slot and nothing else in the state changes.
The identity when `o` holds no CNode. -/
@[inline] def setSlotLinkWords (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) : SystemState :=
  match st.getCNode? o with
  | some _ => st.modifyObject o (mapCNodeObject (·.setLinkWords s f c w))
  | none => st

theorem setSlotLinkWords_def (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) : st.setSlotLinkWords o s f c w = match st.objects[o]? with
      | some (.cnode _) => st.modifyObject o (mapCNodeObject (·.setLinkWords s f c w))
      | _ => st := by
  unfold setSlotLinkWords getCNode?
  cases st.objects[o]? with
  | none => rfl
  | some ob => cases ob <;> rfl

theorem setSlotLinkWords_of_cnode {st : SystemState} {o : SeLe4n.ObjId} {cn : CNode}
    (h : st.objects[o]? = some (.cnode cn)) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    st.setSlotLinkWords o s f c w =
      { st with objects := st.objects.insert o (.cnode (cn.setLinkWords s f c w)) } := by
  rw [setSlotLinkWords_def]; unfold modifyObject
  rw [h]
  simp only
  rw [RHTable.modify_of_get? h]
  rfl

@[simp] theorem setSlotLinkWords_cdt (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) : (st.setSlotLinkWords o s f c w).cdt = st.cdt := by
  rw [setSlotLinkWords_def]; unfold modifyObject
  split <;> rfl

theorem setSlotLinkWords_objects {st : SystemState} (hInv : st.objects.invExt)
    {o : SeLe4n.ObjId} {cn : CNode} (h : st.objects[o]? = some (.cnode cn))
    (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) (x : SeLe4n.ObjId) :
    (st.setSlotLinkWords o s f c w).objects[x]? =
      if x = o then some (.cnode (cn.setLinkWords s f c w)) else st.objects[x]? := by
  rw [setSlotLinkWords_of_cnode h]
  simp only
  split
  · next hx => subst hx; exact RHTable.getElem?_insert_self _ _ _ hInv
  · next hx =>
    have hNe : ¬((o == x) = true) := by intro heq; exact hx (eq_of_beq heq).symm
    exact RHTable.getElem?_insert_ne _ _ _ _ hNe hInv

theorem setSlotLinkWords_of_not_cnode {st : SystemState} {o : SeLe4n.ObjId}
    (h : ∀ cn, st.objects[o]? ≠ some (.cnode cn)) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    st.setSlotLinkWords o s f c w = st := by
  rw [setSlotLinkWords_def]
  split
  · next cn hc => exact absurd hc (h cn)
  · rfl

theorem setSlotLinkWords_invExt {st : SystemState} (hInv : st.objects.invExt)
    (o : SeLe4n.ObjId) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords o s f c w).objects.invExt := by
  by_cases h : ∃ cn, st.objects[o]? = some (.cnode cn)
  · obtain ⟨cn, hcn⟩ := h
    rw [setSlotLinkWords_of_cnode hcn]
    exact RHTable_insert_preserves_invExt _ _ _ hInv
  · rw [setSlotLinkWords_of_not_cnode (fun cn hc => h ⟨cn, hc⟩)]; exact hInv

theorem setSlotLinkWords_linksOnlyWrite {st : SystemState} (hInv : st.objects.invExt)
    (o : SeLe4n.ObjId) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    linksOnlyWrite st (st.setSlotLinkWords o s f c w) := by
  by_cases h : ∃ cn, st.objects[o]? = some (.cnode cn)
  · obtain ⟨cn, hcn⟩ := h
    refine ⟨by rw [setSlotLinkWords_of_cnode hcn], fun x => ?_⟩
    rw [setSlotLinkWords_objects hInv hcn]
    split
    · next hx => subst hx; exact .inr ⟨cn, _, hcn, rfl, rfl⟩
    · exact .inl rfl
  · rw [setSlotLinkWords_of_not_cnode (fun cn hc => h ⟨cn, hc⟩)]
    exact linksOnlyWrite.refl st

/-- **A link write acts on the link view as `LinkView.set`**, for a slot inside
a live CNode. -/
theorem slotLinkAt_setSlotLinkWords {st : SystemState} (hInv : st.objects.invExt)
    {o : SeLe4n.ObjId} {s : SeLe4n.Slot} (h : st.slotInCNode ⟨o, s⟩) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords o s f c w).slotLinkAt = st.slotLinkAt.set ⟨o, s⟩ f (decodeLink c w) := by
  obtain ⟨cn, hcn, hs⟩ := h
  funext r f'
  simp only [slotLinkAt_def, LinkView.set]
  rw [setSlotLinkWords_objects hInv hcn]
  by_cases hr : r.cnode = o
  · rw [if_pos hr, hr, hcn]
    simp only
    rw [CNode.linkAt_setLinkWords cn hs]
    have : (r = ⟨o, s⟩ ∧ f' = f) ↔ (r.slot = s ∧ f' = f) := by
      constructor
      · rintro ⟨rfl, hf⟩; exact ⟨rfl, hf⟩
      · rintro ⟨hs', hf⟩; exact ⟨by cases r; simp_all, hf⟩
    simp only [this]
  · rw [if_neg hr]
    have : ¬ (r = ⟨o, s⟩ ∧ f' = f) := fun ⟨e, _⟩ => hr (e ▸ rfl)
    rw [if_neg this]

/-- A link write keeps every slot inside or outside its CNode. -/
theorem slotInCNode_setSlotLinkWords {st : SystemState} (hInv : st.objects.invExt)
    (o : SeLe4n.ObjId) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) (r : SlotRef) :
    (st.setSlotLinkWords o s f c w).slotInCNode r ↔ st.slotInCNode r := by
  by_cases h : ∃ cn, st.objects[o]? = some (.cnode cn)
  · obtain ⟨cn, hcn⟩ := h
    unfold slotInCNode
    rw [setSlotLinkWords_objects hInv hcn]
    by_cases hr : r.cnode = o
    · simp only [hr, hcn]
      constructor
      · rintro ⟨_, he, hs⟩; cases he; exact ⟨cn, rfl, hs⟩
      · rintro ⟨_, he, hs⟩; cases he; exact ⟨_, rfl, hs⟩
    · simp only [if_neg hr]
  · rw [setSlotLinkWords_of_not_cnode (fun cn hc => h ⟨cn, hc⟩)]

theorem slotLinkAt_setSlotLinkWords_ref {st : SystemState} (hInv : st.objects.invExt)
    {r : SlotRef} (h : st.slotInCNode r) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords r.cnode r.slot f c w).slotLinkAt = st.slotLinkAt.set r f (decodeLink c w) :=
  slotLinkAt_setSlotLinkWords hInv h f c w

theorem decodeLink_ref (r : SlotRef) : decodeLink (r.cnode.toNat + 1) (r.slot.toNat + 1) = some r :=
  decodeLink_codes (some r)

/-- **Link `c` as the new first child of `p`**, in words: the state form of
`LinkView.addChild` (`slotLinkAt_linkAddChild`). -/
@[inline] def linkAddChild (st : SystemState) (p c : SlotRef) : SystemState :=
  let fc := st.slotLinkNodeWord p.cnode p.slot .firstChild
  let fs := st.slotLinkSlotWord p.cnode p.slot .firstChild
  let st1 := st.setSlotLinkWords c.cnode c.slot .parent (p.cnode.toNat + 1) (p.slot.toNat + 1)
  let st2 := st1.setSlotLinkWords c.cnode c.slot .next fc fs
  let st3 := st2.setSlotLinkWords c.cnode c.slot .prev 0 0
  let st4 := if fc = 0 then st3
    else st3.setSlotLinkWords (SeLe4n.ObjId.ofNat (fc - 1)) (SeLe4n.Slot.ofNat (fs - 1)) .prev
      (c.cnode.toNat + 1) (c.slot.toNat + 1)
  st4.setSlotLinkWords p.cnode p.slot .firstChild (c.cnode.toNat + 1) (c.slot.toNat + 1)

/-- Link writes keep the object table's extension invariant and every slot's
place in its CNode. -/
theorem linkAddChild_frame {st : SystemState} (hInv : st.objects.invExt) (p c : SlotRef) :
    (st.linkAddChild p c).objects.invExt ∧
      ∀ r, (st.linkAddChild p c).slotInCNode r ↔ st.slotInCNode r := by
  unfold linkAddChild
  simp only
  have h1 := setSlotLinkWords_invExt hInv c.cnode c.slot .parent (p.cnode.toNat + 1) (p.slot.toNat + 1)
  have h2 := setSlotLinkWords_invExt h1 c.cnode c.slot .next
    (st.slotLinkNodeWord p.cnode p.slot .firstChild) (st.slotLinkSlotWord p.cnode p.slot .firstChild)
  have h3 := setSlotLinkWords_invExt h2 c.cnode c.slot .prev 0 0
  split
  · refine ⟨setSlotLinkWords_invExt h3 _ _ _ _ _, fun r => ?_⟩
    rw [slotInCNode_setSlotLinkWords h3, slotInCNode_setSlotLinkWords h2,
      slotInCNode_setSlotLinkWords h1, slotInCNode_setSlotLinkWords hInv]
  · have h4 := setSlotLinkWords_invExt h3 (SeLe4n.ObjId.ofNat (st.slotLinkNodeWord p.cnode p.slot .firstChild - 1))
      (SeLe4n.Slot.ofNat (st.slotLinkSlotWord p.cnode p.slot .firstChild - 1)) .prev
      (c.cnode.toNat + 1) (c.slot.toNat + 1)
    refine ⟨setSlotLinkWords_invExt h4 _ _ _ _ _, fun r => ?_⟩
    rw [slotInCNode_setSlotLinkWords h4, slotInCNode_setSlotLinkWords h3,
      slotInCNode_setSlotLinkWords h2, slotInCNode_setSlotLinkWords h1,
      slotInCNode_setSlotLinkWords hInv]

/-- **`linkAddChild` acts on the link view as `LinkView.addChild`**, when `p`,
`c` and `p`'s first child are slots of live CNodes. -/
theorem slotLinkAt_linkAddChild {st : SystemState} (hInv : st.objects.invExt) {p c : SlotRef}
    (hp : st.slotInCNode p) (hc : st.slotInCNode c)
    (hx : ∀ x, st.slotLinkAt p .firstChild = some x → st.slotInCNode x) :
    (st.linkAddChild p c).slotLinkAt = st.slotLinkAt.addChild p c := by
  have hf0 := slotLinkAt_eq_decode st p .firstChild
  unfold linkAddChild LinkView.addChild
  simp only
  have h1 := setSlotLinkWords_invExt hInv c.cnode c.slot .parent (p.cnode.toNat + 1) (p.slot.toNat + 1)
  have h2 := setSlotLinkWords_invExt h1 c.cnode c.slot .next
    (st.slotLinkNodeWord p.cnode p.slot .firstChild) (st.slotLinkSlotWord p.cnode p.slot .firstChild)
  have h3 := setSlotLinkWords_invExt h2 c.cnode c.slot .prev 0 0
  have v : ∀ r, ((((st.setSlotLinkWords c.cnode c.slot .parent (p.cnode.toNat + 1)
      (p.slot.toNat + 1)).setSlotLinkWords c.cnode c.slot .next
      (st.slotLinkNodeWord p.cnode p.slot .firstChild)
      (st.slotLinkSlotWord p.cnode p.slot .firstChild)).setSlotLinkWords c.cnode c.slot .prev 0 0)
      ).slotInCNode r ↔ st.slotInCNode r := fun r => by
    rw [slotInCNode_setSlotLinkWords h2, slotInCNode_setSlotLinkWords h1,
      slotInCNode_setSlotLinkWords hInv]
  have e3 : (((st.setSlotLinkWords c.cnode c.slot .parent (p.cnode.toNat + 1)
      (p.slot.toNat + 1)).setSlotLinkWords c.cnode c.slot .next
      (st.slotLinkNodeWord p.cnode p.slot .firstChild)
      (st.slotLinkSlotWord p.cnode p.slot .firstChild)).setSlotLinkWords c.cnode c.slot .prev 0 0
      ).slotLinkAt = ((st.slotLinkAt.set c .parent (some p)).set c .next
        (st.slotLinkAt p .firstChild)).set c .prev none := by
    rw [slotLinkAt_setSlotLinkWords_ref h2 ((slotInCNode_setSlotLinkWords h1 _ _ _ _ _ c).mpr
        ((slotInCNode_setSlotLinkWords hInv _ _ _ _ _ c).mpr hc)),
      slotLinkAt_setSlotLinkWords_ref h1 ((slotInCNode_setSlotLinkWords hInv _ _ _ _ _ c).mpr hc),
      slotLinkAt_setSlotLinkWords_ref hInv hc, decodeLink_ref, hf0]
    rfl
  split
  · next h0 =>
    have hn : st.slotLinkAt p .firstChild = none := by rw [hf0, h0]; rfl
    rw [slotLinkAt_setSlotLinkWords_ref h3 ((v p).mpr hp), e3, decodeLink_ref, hn]
  · next h0 =>
    have hs : st.slotLinkAt p .firstChild =
        some ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord p.cnode p.slot .firstChild - 1),
          SeLe4n.Slot.ofNat (st.slotLinkSlotWord p.cnode p.slot .firstChild - 1)⟩ := by
      rw [hf0]; unfold decodeLink; rw [if_neg h0]
    have hxv := hx _ hs
    have h4 := setSlotLinkWords_invExt h3
      (SeLe4n.ObjId.ofNat (st.slotLinkNodeWord p.cnode p.slot .firstChild - 1))
      (SeLe4n.Slot.ofNat (st.slotLinkSlotWord p.cnode p.slot .firstChild - 1)) .prev
      (c.cnode.toNat + 1) (c.slot.toNat + 1)
    rw [slotLinkAt_setSlotLinkWords_ref h4
        ((slotInCNode_setSlotLinkWords h3 _ _ _ _ _ p).mpr ((v p).mpr hp)),
      slotLinkAt_setSlotLinkWords h3 ((v _).mpr hxv), e3, decodeLink_ref, hs]

/-- The slot a nonzero link names, as its words address it. -/
theorem slotLinkAt_of_ne_zero {st : SystemState} {r : SlotRef} {f : LinkField}
    (h : st.slotLinkNodeWord r.cnode r.slot f ≠ 0) :
    st.slotLinkAt r f = some ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord r.cnode r.slot f - 1),
      SeLe4n.Slot.ofNat (st.slotLinkSlotWord r.cnode r.slot f - 1)⟩ := by
  rw [slotLinkAt_eq_decode]; unfold decodeLink; rw [if_neg h]

theorem slotLinkAt_of_eq_zero {st : SystemState} {r : SlotRef} {f : LinkField}
    (h : st.slotLinkNodeWord r.cnode r.slot f = 0) : st.slotLinkAt r f = none := by
  rw [slotLinkAt_eq_decode]; unfold decodeLink; rw [if_pos h]

/-- One link write to a slot of a live CNode: what it keeps and what it sets. -/
theorem setSlotLinkWords_step {st : SystemState} (hInv : st.objects.invExt) {o : SeLe4n.ObjId}
    {s : SeLe4n.Slot} (h : st.slotInCNode ⟨o, s⟩) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords o s f c w).objects.invExt ∧
      (∀ r, (st.setSlotLinkWords o s f c w).slotInCNode r ↔ st.slotInCNode r) ∧
      (st.setSlotLinkWords o s f c w).slotLinkAt = st.slotLinkAt.set ⟨o, s⟩ f (decodeLink c w) :=
  ⟨setSlotLinkWords_invExt hInv o s f c w, slotInCNode_setSlotLinkWords hInv o s f c w,
    slotLinkAt_setSlotLinkWords hInv h f c w⟩

/-- **Unlink `n` from its siblings**, in words: the state form of
`LinkView.unlinkChild` (`slotLinkAt_linkUnlinkChild`). -/
def linkUnlinkChild (st : SystemState) (n : SlotRef) : SystemState :=
  let pc := st.slotLinkNodeWord n.cnode n.slot .prev
  let ps := st.slotLinkSlotWord n.cnode n.slot .prev
  let nc := st.slotLinkNodeWord n.cnode n.slot .next
  let ns := st.slotLinkSlotWord n.cnode n.slot .next
  let uc := st.slotLinkNodeWord n.cnode n.slot .parent
  let us := st.slotLinkSlotWord n.cnode n.slot .parent
  let st1 := if pc = 0 then
      (if uc = 0 then st
       else st.setSlotLinkWords (SeLe4n.ObjId.ofNat (uc - 1)) (SeLe4n.Slot.ofNat (us - 1))
        .firstChild nc ns)
    else st.setSlotLinkWords (SeLe4n.ObjId.ofNat (pc - 1)) (SeLe4n.Slot.ofNat (ps - 1)) .next nc ns
  let st2 := if nc = 0 then st1
    else st1.setSlotLinkWords (SeLe4n.ObjId.ofNat (nc - 1)) (SeLe4n.Slot.ofNat (ns - 1)) .prev pc ps
  ((st2.setSlotLinkWords n.cnode n.slot .parent 0 0).setSlotLinkWords n.cnode n.slot .next 0 0
    ).setSlotLinkWords n.cnode n.slot .prev 0 0

/-- **`linkUnlinkChild` acts on the link view as `LinkView.unlinkChild`**, when
`n` and the slots its links name are slots of live CNodes. -/
theorem linkUnlinkChild_spec {st : SystemState} (hInv : st.objects.invExt) {n : SlotRef}
    (hn : st.slotInCNode n) (hT : ∀ f x, st.slotLinkAt n f = some x → st.slotInCNode x) :
    (st.linkUnlinkChild n).objects.invExt ∧
      (∀ r, (st.linkUnlinkChild n).slotInCNode r ↔ st.slotInCNode r) ∧
      (st.linkUnlinkChild n).slotLinkAt = st.slotLinkAt.unlinkChild n := by
  have ePr := slotLinkAt_eq_decode st n .prev
  have eNx := slotLinkAt_eq_decode st n .next
  have eUp := slotLinkAt_eq_decode st n .parent
  unfold linkUnlinkChild
  simp only
  generalize st.slotLinkNodeWord n.cnode n.slot .prev = pc at *
  generalize st.slotLinkSlotWord n.cnode n.slot .prev = ps at *
  generalize st.slotLinkNodeWord n.cnode n.slot .next = nc at *
  generalize st.slotLinkSlotWord n.cnode n.slot .next = ns at *
  generalize st.slotLinkNodeWord n.cnode n.slot .parent = uc at *
  generalize st.slotLinkSlotWord n.cnode n.slot .parent = us at *
  have addr : ∀ {f c w}, st.slotLinkAt n f = decodeLink c w → c ≠ 0 →
      st.slotInCNode ⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ ∧
      decodeLink c w = some ⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ := by
    intro f c w he hc
    have hd : decodeLink c w = some ⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ := by
      unfold decodeLink; rw [if_neg hc]
    exact ⟨hT f _ (he.trans hd), hd⟩
  have zero : ∀ {c w : Nat}, c = 0 → decodeLink c w = none := fun h => by
    subst h; rfl
  -- the first write (to the previous sibling, or else the parent)
  obtain ⟨st1, hst1, i1, v1, e1⟩ : ∃ st1, st1 = (if pc = 0 then
      (if uc = 0 then st
       else st.setSlotLinkWords (SeLe4n.ObjId.ofNat (uc - 1)) (SeLe4n.Slot.ofNat (us - 1))
        .firstChild nc ns)
      else st.setSlotLinkWords (SeLe4n.ObjId.ofNat (pc - 1)) (SeLe4n.Slot.ofNat (ps - 1)) .next nc ns) ∧
      st1.objects.invExt ∧ (∀ r, st1.slotInCNode r ↔ st.slotInCNode r) ∧
      st1.slotLinkAt = (match st.slotLinkAt n .prev with
        | some x => st.slotLinkAt.set x .next (st.slotLinkAt n .next)
        | none => match st.slotLinkAt n .parent with
          | some p => st.slotLinkAt.set p .firstChild (st.slotLinkAt n .next)
          | none => st.slotLinkAt) := by
    refine ⟨_, rfl, ?_⟩
    by_cases hp : pc = 0
    · rw [if_pos hp, ePr, zero hp]
      by_cases hu : uc = 0
      · rw [if_pos hu, eUp, zero hu]; exact ⟨hInv, fun _ => .rfl, rfl⟩
      · rw [if_neg hu]
        obtain ⟨hv, hd⟩ := addr eUp hu
        obtain ⟨i, v, e⟩ := setSlotLinkWords_step hInv hv .firstChild nc ns
        exact ⟨i, v, by rw [e, eUp, hd, eNx]⟩
    · rw [if_neg hp]
      obtain ⟨hv, hd⟩ := addr ePr hp
      obtain ⟨i, v, e⟩ := setSlotLinkWords_step hInv hv .next nc ns
      exact ⟨i, v, by rw [e, ePr, hd, eNx]⟩
  rw [← hst1]
  -- the second write (to the next sibling)
  obtain ⟨st2, hst2, i2, v2, e2⟩ : ∃ st2, st2 = (if nc = 0 then st1
      else st1.setSlotLinkWords (SeLe4n.ObjId.ofNat (nc - 1)) (SeLe4n.Slot.ofNat (ns - 1)) .prev pc ps) ∧
      st2.objects.invExt ∧ (∀ r, st2.slotInCNode r ↔ st.slotInCNode r) ∧
      st2.slotLinkAt = (match st.slotLinkAt n .next with
        | some y => st1.slotLinkAt.set y .prev (st.slotLinkAt n .prev)
        | none => st1.slotLinkAt) := by
    refine ⟨_, rfl, ?_⟩
    by_cases hx : nc = 0
    · rw [if_pos hx, eNx, zero hx]; exact ⟨i1, v1, rfl⟩
    · rw [if_neg hx]
      obtain ⟨hv, hd⟩ := addr eNx hx
      obtain ⟨i, v, e⟩ := setSlotLinkWords_step i1 ((v1 _).mpr hv) .prev pc ps
      exact ⟨i, fun r => (v r).trans (v1 r), by rw [e, eNx, hd, ePr]⟩
  rw [← hst2]
  obtain ⟨i3, v3, e3⟩ := setSlotLinkWords_step i2 ((v2 n).mpr hn) .parent 0 0
  obtain ⟨i4, v4, e4⟩ := setSlotLinkWords_step i3 ((v3 n).mpr ((v2 n).mpr hn)) .next 0 0
  obtain ⟨i5, v5, e5⟩ := setSlotLinkWords_step i4 ((v4 n).mpr ((v3 n).mpr ((v2 n).mpr hn))) .prev 0 0
  refine ⟨i5, fun r => ((v5 r).trans (v4 r)).trans ((v3 r).trans (v2 r)), ?_⟩
  rw [e5, e4, e3, e2, e1]
  rfl

/-- **Orphan the sibling chain from the slot words `(c, w)`**, at most `k`
slots: clear each one's parent and sibling links, reading its next sibling
before clearing it.  The state form of folding `LinkView.orphan` over the walk
(`linkOrphanChain_spec`). -/
def linkOrphanChain : Nat → SystemState → Nat → Nat → SystemState
  | 0, st, _, _ => st
  | k + 1, st, c, w =>
    if c = 0 then st
    else
      let o := SeLe4n.ObjId.ofNat (c - 1)
      let s := SeLe4n.Slot.ofNat (w - 1)
      let nc := st.slotLinkNodeWord o s .next
      let ns := st.slotLinkSlotWord o s .next
      linkOrphanChain k (((st.setSlotLinkWords o s .parent 0 0).setSlotLinkWords o s .next 0 0
        ).setSlotLinkWords o s .prev 0 0) nc ns

theorem linkOrphanChain_spec : ∀ (k : Nat) {st : SystemState} (c w : Nat),
    st.objects.invExt →
    (∀ x ∈ st.slotLinkAt.walk k (decodeLink c w), st.slotInCNode x) →
    (st.slotLinkAt.walk k (decodeLink c w)).Nodup →
    (linkOrphanChain k st c w).objects.invExt ∧
      (∀ r, (linkOrphanChain k st c w).slotInCNode r ↔ st.slotInCNode r) ∧
      (linkOrphanChain k st c w).slotLinkAt =
        (st.slotLinkAt.walk k (decodeLink c w)).foldl LinkView.orphan st.slotLinkAt
  | 0, st, _, _, hInv, _, _ => ⟨hInv, fun _ => .rfl, rfl⟩
  | k + 1, st, c, w, hInv, hV, hNd => by
    unfold linkOrphanChain
    by_cases hc : c = 0
    · subst hc; exact ⟨hInv, fun _ => .rfl, rfl⟩
    · rw [if_neg hc]
      simp only
      have hd : decodeLink c w = some ⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ := by
        unfold decodeLink; rw [if_neg hc]
      rw [hd] at hV hNd ⊢
      generalize hx : (⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ : SlotRef) = x at *
      have hxo : SeLe4n.ObjId.ofNat (c - 1) = x.cnode := by rw [← hx]
      have hxs : SeLe4n.Slot.ofNat (w - 1) = x.slot := by rw [← hx]
      rw [hxo, hxs]
      simp only [LinkView.walk, List.foldl_cons] at hV hNd ⊢
      have ⟨hxL, hNd'⟩ := List.nodup_cons.mp hNd
      have hxv := hV x (List.mem_cons_self ..)
      have eN := slotLinkAt_eq_decode st x .next
      obtain ⟨i1, v1, e1⟩ := setSlotLinkWords_step hInv hxv .parent 0 0
      obtain ⟨i2, v2, e2⟩ := setSlotLinkWords_step i1 ((v1 x).mpr hxv) .next 0 0
      obtain ⟨i3, v3, e3⟩ := setSlotLinkWords_step i2 ((v2 x).mpr ((v1 x).mpr hxv)) .prev 0 0
      have eO : (((st.setSlotLinkWords x.cnode x.slot .parent 0 0).setSlotLinkWords x.cnode x.slot
          .next 0 0).setSlotLinkWords x.cnode x.slot .prev 0 0).slotLinkAt =
          st.slotLinkAt.orphan x := by
        rw [e3, e2, e1]; rfl
      have hW : (((st.setSlotLinkWords x.cnode x.slot .parent 0 0).setSlotLinkWords x.cnode x.slot
          .next 0 0).setSlotLinkWords x.cnode x.slot .prev 0 0).slotLinkAt.walk k
          (decodeLink (st.slotLinkNodeWord x.cnode x.slot .next) (st.slotLinkSlotWord x.cnode x.slot .next)) =
          st.slotLinkAt.walk k (st.slotLinkAt x .next) := by
        rw [eO, ← eN]
        refine LinkView.walk_congr k _ (fun v hv => ?_)
        have hvx : v ≠ x := fun e => hxL (e ▸ hv)
        unfold LinkView.orphan
        simp [LinkView.set, hvx]
      have vAll : ∀ r, (((st.setSlotLinkWords x.cnode x.slot .parent 0 0).setSlotLinkWords x.cnode
          x.slot .next 0 0).setSlotLinkWords x.cnode x.slot .prev 0 0).slotInCNode r ↔
          st.slotInCNode r := fun r => ((v3 r).trans (v2 r)).trans (v1 r)
      obtain ⟨j, vj, ej⟩ := linkOrphanChain_spec k _ _ i3
        (fun y hy => (vAll y).mpr (hV y (List.mem_cons_of_mem _ (hW ▸ hy))))
        (hW ▸ hNd')
      refine ⟨j, fun r => (vj r).trans (vAll r), ?_⟩
      rw [ej, hW, eO]

/-- **The link writes of removing `n` from the tree**, in words: unlink `n`,
orphan its children (at most `k`), clear its first-child link.  The state form
of `LinkView.removeNodeLinks` over the children walk (`linkRemoveNode_spec`). -/
def linkRemoveNode (st : SystemState) (n : SlotRef) (k : Nat) : SystemState :=
  let fc := st.slotLinkNodeWord n.cnode n.slot .firstChild
  let fs := st.slotLinkSlotWord n.cnode n.slot .firstChild
  (linkOrphanChain k (st.linkUnlinkChild n) fc fs).setSlotLinkWords n.cnode n.slot .firstChild 0 0

theorem linkRemoveNode_spec {st : SystemState} (hInv : st.objects.invExt) {n : SlotRef} (k : Nat)
    (hn : st.slotInCNode n) (hT : ∀ f x, st.slotLinkAt n f = some x → st.slotInCNode x)
    (hC : ∀ x ∈ st.slotLinkAt.walk k (st.slotLinkAt n .firstChild), st.slotInCNode x)
    (hNd : (st.slotLinkAt.walk k (st.slotLinkAt n .firstChild)).Nodup)
    (hSelf : ∀ w ∈ st.slotLinkAt.walk k (st.slotLinkAt n .firstChild),
      w ≠ n ∧ st.slotLinkAt n .prev ≠ some w) :
    (st.linkRemoveNode n k).objects.invExt ∧
      (∀ r, (st.linkRemoveNode n k).slotInCNode r ↔ st.slotInCNode r) ∧
      (st.linkRemoveNode n k).slotLinkAt =
        st.slotLinkAt.removeNodeLinks n (st.slotLinkAt.walk k (st.slotLinkAt n .firstChild)) := by
  have eF := slotLinkAt_eq_decode st n .firstChild
  obtain ⟨i1, v1, e1⟩ := linkUnlinkChild_spec hInv hn hT
  have hW : (st.linkUnlinkChild n).slotLinkAt.walk k
      (decodeLink (st.slotLinkNodeWord n.cnode n.slot .firstChild)
        (st.slotLinkSlotWord n.cnode n.slot .firstChild)) =
      st.slotLinkAt.walk k (st.slotLinkAt n .firstChild) := by
    rw [e1, ← eF]
    refine LinkView.walk_congr k _ (fun w hw => ?_)
    obtain ⟨h1, h2⟩ := hSelf w hw
    rw [LinkView.unlinkChild_next, if_neg h1, if_neg h2]
  obtain ⟨i2, v2, e2⟩ := linkOrphanChain_spec k _ _ i1
    (fun x hx => (v1 x).mpr (hC x (hW ▸ hx))) (hW ▸ hNd)
  unfold linkRemoveNode
  simp only
  obtain ⟨i3, v3, e3⟩ := setSlotLinkWords_step i2 ((v2 n).mpr ((v1 n).mpr hn)) .firstChild 0 0
  refine ⟨i3, fun r => ((v3 r).trans (v2 r)).trans (v1 r), ?_⟩
  rw [e3, e2, hW, e1]
  rfl

/-- **Link the sibling chain from the slot words `(c, w)` under `u`**, at most
`k` slots, each as `u`'s new first child, reading each one's next sibling
before linking it.  The state form of folding `LinkView.addChild u` over the
walk (`linkReparentChain_spec`). -/
def linkReparentChain : Nat → SystemState → SlotRef → Nat → Nat → SystemState
  | 0, st, _, _, _ => st
  | k + 1, st, u, c, w =>
    if c = 0 then st
    else
      let o := SeLe4n.ObjId.ofNat (c - 1)
      let s := SeLe4n.Slot.ofNat (w - 1)
      let nc := st.slotLinkNodeWord o s .next
      let ns := st.slotLinkSlotWord o s .next
      linkReparentChain k (st.linkAddChild u ⟨o, s⟩) u nc ns

theorem linkReparentChain_spec : ∀ (k : Nat) {st : SystemState} (u : SlotRef) (c w : Nat),
    st.objects.invExt → st.slotInCNode u →
    (∀ x, st.slotLinkAt u .firstChild = some x → st.slotInCNode x) →
    (∀ x ∈ st.slotLinkAt.walk k (decodeLink c w), st.slotInCNode x) →
    (st.slotLinkAt.walk k (decodeLink c w)).Nodup →
    (linkReparentChain k st u c w).objects.invExt ∧
      (∀ r, (linkReparentChain k st u c w).slotInCNode r ↔ st.slotInCNode r) ∧
      (linkReparentChain k st u c w).slotLinkAt =
        (st.slotLinkAt.walk k (decodeLink c w)).foldl (fun L c => L.addChild u c) st.slotLinkAt
  | 0, st, _, _, _, hInv, _, _, _, _ => ⟨hInv, fun _ => .rfl, rfl⟩
  | k + 1, st, u, c, w, hInv, hu, hF, hV, hNd => by
    unfold linkReparentChain
    by_cases hc : c = 0
    · subst hc; exact ⟨hInv, fun _ => .rfl, rfl⟩
    · rw [if_neg hc]
      simp only
      have hd : decodeLink c w = some ⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ := by
        unfold decodeLink; rw [if_neg hc]
      rw [hd] at hV hNd ⊢
      generalize hx : (⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩ : SlotRef) = x at *
      have hxo : SeLe4n.ObjId.ofNat (c - 1) = x.cnode := by rw [← hx]
      have hxs : SeLe4n.Slot.ofNat (w - 1) = x.slot := by rw [← hx]
      rw [hxo, hxs]
      simp only [LinkView.walk, List.foldl_cons] at hV hNd ⊢
      have ⟨hxL, hNd'⟩ := List.nodup_cons.mp hNd
      have hxv := hV x (List.mem_cons_self ..)
      have eN := slotLinkAt_eq_decode st x .next
      obtain ⟨i1, v1⟩ := linkAddChild_frame hInv u x
      have e1 := slotLinkAt_linkAddChild hInv hu hxv hF
      have hW : (st.linkAddChild u x).slotLinkAt.walk k
          (decodeLink (st.slotLinkNodeWord x.cnode x.slot .next)
            (st.slotLinkSlotWord x.cnode x.slot .next)) =
          st.slotLinkAt.walk k (st.slotLinkAt x .next) := by
        rw [e1, ← eN]
        refine LinkView.walk_congr k _ (fun v hv => ?_)
        have hvx : v ≠ x := fun e => hxL (e ▸ hv)
        rw [LinkView.addChild_next, if_neg hvx]
      obtain ⟨j, vj, ej⟩ := linkReparentChain_spec k u _ _ i1 ((v1 u).mpr hu)
        (fun y hy => by
          rw [e1, LinkView.addChild_firstChild, if_pos rfl] at hy
          cases hy; exact (v1 _).mpr hxv)
        (fun y hy => (v1 y).mpr (hV y (List.mem_cons_of_mem _ (hW ▸ hy))))
        (hW ▸ hNd')
      refine ⟨j, fun r => (vj r).trans (v1 r), ?_⟩
      rw [ej, hW, e1]

/-- The slots a walk visits are link targets, so slots of live CNodes when every
link names one. -/
theorem walk_valid {st : SystemState}
    (hAll : ∀ r f x, st.slotLinkAt r f = some x → st.slotInCNode x) (k : Nat) (r : SlotRef)
    (f : LinkField) : ∀ x ∈ st.slotLinkAt.walk k (st.slotLinkAt r f), st.slotInCNode x := by
  intro x hx
  rcases LinkView.mem_walk hx with h | ⟨v, h⟩
  · exact hAll _ _ _ h
  · exact hAll _ _ _ h

/-- **The link writes of splicing `n` out**, in words: with a parent `u`, unlink
`n`, link its children under `u` in chain order and clear its first-child link;
without one, remove it (`linkSpliceNode_spec`). -/
def linkSpliceNode (st : SystemState) (n : SlotRef) (k : Nat) : SystemState :=
  let uc := st.slotLinkNodeWord n.cnode n.slot .parent
  let us := st.slotLinkSlotWord n.cnode n.slot .parent
  if uc = 0 then st.linkRemoveNode n k
  else
    let fc := st.slotLinkNodeWord n.cnode n.slot .firstChild
    let fs := st.slotLinkSlotWord n.cnode n.slot .firstChild
    (linkReparentChain k (st.linkUnlinkChild n)
      ⟨SeLe4n.ObjId.ofNat (uc - 1), SeLe4n.Slot.ofNat (us - 1)⟩ fc fs).setSlotLinkWords
      n.cnode n.slot .firstChild 0 0

theorem linkSpliceNode_spec {st : SystemState} (hInv : st.objects.invExt) {n : SlotRef} (k : Nat)
    (hn : st.slotInCNode n) (hAll : ∀ r f x, st.slotLinkAt r f = some x → st.slotInCNode x)
    (hNd : (st.slotLinkAt.walk k (st.slotLinkAt n .firstChild)).Nodup)
    (hSelf : ∀ w ∈ st.slotLinkAt.walk k (st.slotLinkAt n .firstChild),
      w ≠ n ∧ st.slotLinkAt n .prev ≠ some w) :
    (st.linkSpliceNode n k).objects.invExt ∧
      (∀ r, (st.linkSpliceNode n k).slotInCNode r ↔ st.slotInCNode r) ∧
      (st.linkSpliceNode n k).slotLinkAt =
        match st.slotLinkAt n .parent with
        | none => st.slotLinkAt.removeNodeLinks n (st.slotLinkAt.walk k (st.slotLinkAt n .firstChild))
        | some u => ((st.slotLinkAt.walk k (st.slotLinkAt n .firstChild)).foldl
            (fun (L : LinkView) c => L.addChild u c) (st.slotLinkAt.unlinkChild n)).set n .firstChild none := by
  have eU := slotLinkAt_eq_decode st n .parent
  have eF := slotLinkAt_eq_decode st n .firstChild
  unfold linkSpliceNode
  simp only
  by_cases hu : st.slotLinkNodeWord n.cnode n.slot .parent = 0
  · rw [if_pos hu, slotLinkAt_of_eq_zero hu]
    exact linkRemoveNode_spec hInv k hn (fun f x h => hAll n f x h) (walk_valid hAll k n .firstChild)
      hNd hSelf
  · rw [if_neg hu, slotLinkAt_of_ne_zero hu]
    simp only
    generalize hU : (⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord n.cnode n.slot .parent - 1),
      SeLe4n.Slot.ofNat (st.slotLinkSlotWord n.cnode n.slot .parent - 1)⟩ : SlotRef) = u
    have hUp : st.slotLinkAt n .parent = some u := by rw [slotLinkAt_of_ne_zero hu, hU]
    obtain ⟨i1, v1, e1⟩ := linkUnlinkChild_spec hInv hn (fun f x h => hAll n f x h)
    have hW : (st.linkUnlinkChild n).slotLinkAt.walk k
        (decodeLink (st.slotLinkNodeWord n.cnode n.slot .firstChild)
          (st.slotLinkSlotWord n.cnode n.slot .firstChild)) =
        st.slotLinkAt.walk k (st.slotLinkAt n .firstChild) := by
      rw [e1, ← eF]
      refine LinkView.walk_congr k _ (fun w hw => ?_)
      obtain ⟨h1, h2⟩ := hSelf w hw
      rw [LinkView.unlinkChild_next, if_neg h1, if_neg h2]
    have hC := walk_valid hAll k n .firstChild
    obtain ⟨i2, v2, e2⟩ := linkReparentChain_spec k u _ _ i1 ((v1 u).mpr (hAll _ _ _ hUp))
      (fun x hx => by
        rw [e1] at hx
        obtain ⟨v, g, hv⟩ := LinkView.unlinkChild_target hx
        exact (v1 x).mpr (hAll _ _ _ hv))
      (fun x hx => (v1 x).mpr (hC x (hW ▸ hx))) (hW ▸ hNd)
    obtain ⟨i3, v3, e3⟩ := setSlotLinkWords_step i2 ((v2 n).mpr ((v1 n).mpr hn)) .firstChild 0 0
    refine ⟨i3, fun r => ((v3 r).trans (v2 r)).trans (v1 r), ?_⟩
    rw [e3, e2, hW, e1]
    rfl

/-- **The link writes of moving `old` to `new`**, in words: unlink `old`, link
`new` under `old`'s parent, link `old`'s children under `new` in chain order and
clear `old`'s first-child link (`linkMoveNode_spec`). -/
def linkMoveNode (st : SystemState) (old new : SlotRef) (k : Nat) : SystemState :=
  let uc := st.slotLinkNodeWord old.cnode old.slot .parent
  let us := st.slotLinkSlotWord old.cnode old.slot .parent
  let fc := st.slotLinkNodeWord old.cnode old.slot .firstChild
  let fs := st.slotLinkSlotWord old.cnode old.slot .firstChild
  let st1 := st.linkUnlinkChild old
  let st2 := if uc = 0 then st1
    else st1.linkAddChild ⟨SeLe4n.ObjId.ofNat (uc - 1), SeLe4n.Slot.ofNat (us - 1)⟩ new
  (linkReparentChain k st2 new fc fs).setSlotLinkWords old.cnode old.slot .firstChild 0 0

theorem linkMoveNode_spec {st : SystemState} (hInv : st.objects.invExt) {old new : SlotRef}
    (k : Nat) (ho : st.slotInCNode old) (hnw : st.slotInCNode new)
    (hAll : ∀ r f x, st.slotLinkAt r f = some x → st.slotInCNode x)
    (hNd : (st.slotLinkAt.walk k (st.slotLinkAt old .firstChild)).Nodup)
    (hSelf : ∀ w ∈ st.slotLinkAt.walk k (st.slotLinkAt old .firstChild),
      w ≠ old ∧ st.slotLinkAt old .prev ≠ some w ∧ w ≠ new) :
    (st.linkMoveNode old new k).objects.invExt ∧
      (∀ r, (st.linkMoveNode old new k).slotInCNode r ↔ st.slotInCNode r) ∧
      (st.linkMoveNode old new k).slotLinkAt =
        ((st.slotLinkAt.walk k (st.slotLinkAt old .firstChild)).foldl (fun (L : LinkView) c => L.addChild new c)
          (match st.slotLinkAt old .parent with
           | some u => (st.slotLinkAt.unlinkChild old).addChild u new
           | none => st.slotLinkAt.unlinkChild old)).set old .firstChild none := by
  have eF := slotLinkAt_eq_decode st old .firstChild
  obtain ⟨i1, v1, e1⟩ := linkUnlinkChild_spec hInv ho (fun f x h => hAll old f x h)
  have hC := walk_valid hAll k old .firstChild
  have t1 : ∀ r f x, (st.linkUnlinkChild old).slotLinkAt r f = some x →
      (st.linkUnlinkChild old).slotInCNode x := fun r f x h => by
    rw [e1] at h
    obtain ⟨v, g, hv⟩ := LinkView.unlinkChild_target h
    exact (v1 x).mpr (hAll _ _ _ hv)
  -- the second stage: `new` under `old`'s parent
  obtain ⟨st2, hst2, i2, v2, e2, t2⟩ : ∃ st2, st2 = (if st.slotLinkNodeWord old.cnode old.slot .parent = 0
      then st.linkUnlinkChild old
      else (st.linkUnlinkChild old).linkAddChild
        ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord old.cnode old.slot .parent - 1),
          SeLe4n.Slot.ofNat (st.slotLinkSlotWord old.cnode old.slot .parent - 1)⟩ new) ∧
      st2.objects.invExt ∧ (∀ r, st2.slotInCNode r ↔ st.slotInCNode r) ∧
      st2.slotLinkAt = (match st.slotLinkAt old .parent with
        | some u => (st.slotLinkAt.unlinkChild old).addChild u new
        | none => st.slotLinkAt.unlinkChild old) ∧
      (∀ x, st2.slotLinkAt new .firstChild = some x → st2.slotInCNode x) := by
    refine ⟨_, rfl, ?_⟩
    by_cases hu : st.slotLinkNodeWord old.cnode old.slot .parent = 0
    · rw [if_pos hu, slotLinkAt_of_eq_zero hu]
      exact ⟨i1, v1, e1, fun x h => t1 _ _ _ h⟩
    · rw [if_neg hu, slotLinkAt_of_ne_zero hu]
      simp only
      generalize hU : (⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord old.cnode old.slot .parent - 1),
        SeLe4n.Slot.ofNat (st.slotLinkSlotWord old.cnode old.slot .parent - 1)⟩ : SlotRef) = u
      have hUp : st.slotLinkAt old .parent = some u := by rw [slotLinkAt_of_ne_zero hu, hU]
      have hu1 := (v1 u).mpr (hAll _ _ _ hUp)
      have hn1 := (v1 new).mpr hnw
      obtain ⟨j, vj⟩ := linkAddChild_frame i1 u new
      have ej := slotLinkAt_linkAddChild i1 hu1 hn1 (fun x h => t1 _ _ _ h)
      refine ⟨j, fun r => (vj r).trans (v1 r), by rw [ej, e1], fun x h => ?_⟩
      rw [ej, LinkView.addChild_firstChild] at h
      split at h
      · cases h; exact (vj _).mpr hn1
      · exact (vj x).mpr (t1 _ _ _ h)
  unfold linkMoveNode
  simp only
  rw [← hst2]
  have hW : st2.slotLinkAt.walk k
      (decodeLink (st.slotLinkNodeWord old.cnode old.slot .firstChild)
        (st.slotLinkSlotWord old.cnode old.slot .firstChild)) =
      st.slotLinkAt.walk k (st.slotLinkAt old .firstChild) := by
    rw [← eF, e2]
    refine LinkView.walk_congr k _ (fun w hw => ?_)
    obtain ⟨h1, h2, h3⟩ := hSelf w hw
    cases st.slotLinkAt old .parent with
    | some u =>
      show (st.slotLinkAt.unlinkChild old).addChild u new w .next = _
      rw [LinkView.addChild_next, if_neg h3, LinkView.unlinkChild_next, if_neg h1, if_neg h2]
    | none =>
      show st.slotLinkAt.unlinkChild old w .next = _
      rw [LinkView.unlinkChild_next, if_neg h1, if_neg h2]
  obtain ⟨i3, v3, e3⟩ := linkReparentChain_spec k new _ _ i2 ((v2 new).mpr hnw) t2
    (fun x hx => (v2 x).mpr (hC x (hW ▸ hx))) (hW ▸ hNd)
  obtain ⟨i4, v4, e4⟩ := setSlotLinkWords_step i3 ((v3 old).mpr ((v2 old).mpr ho)) .firstChild 0 0
  refine ⟨i4, fun r => ((v4 r).trans (v3 r)).trans (v2 r), ?_⟩
  rw [e4, e3, hW, e2]
  rfl

/-- Two CNodes that agree off their derivation links agree on anything that
reads past those links (slots, geometry). -/
@[elab_without_expected_type]
theorem _root_.SeLe4n.Model.CNode.proj_eq_of_withoutLinks_eq {α : Sort _} {a b : CNode} (f : CNode → α)
    (h : a.withoutLinks = b.withoutLinks)
    (hf : ∀ c : CNode, f c.withoutLinks = f c := by intro; rfl) : f a = f b := by
  rw [← hf a, ← hf b, h]

/-- **`st'` holds `st`'s objects up to CNode derivation links**: at every key
the same object, or a CNode that differs from `st`'s only in its links.  The
object half of `linksOnlyWrite`, for a step that also rewrites the tree. -/
def objectsAgreeOffDerivationLinks (st' st : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ cn cn' : CNode, st.objects[oid]? = some (.cnode cn) ∧
      st'.objects[oid]? = some (.cnode cn') ∧ cn'.withoutLinks = cn.withoutLinks

/-- **`st'` holds `st`'s object at `oid` up to CNode derivation links**: the
pointwise body of `objectsAgreeOffDerivationLinks`. -/
def objectAgreesOffDerivationLinksAt (st' st : SystemState) (oid : SeLe4n.ObjId) : Prop :=
  st'.objects[oid]? = st.objects[oid]? ∨
    ∃ cn cn' : CNode, st.objects[oid]? = some (.cnode cn) ∧
      st'.objects[oid]? = some (.cnode cn') ∧ cn'.withoutLinks = cn.withoutLinks

namespace objectAgreesOffDerivationLinksAt

variable {st st' : SystemState} {oid : SeLe4n.ObjId}

theorem of_eq (h : st'.objects[oid]? = st.objects[oid]?) :
    objectAgreesOffDerivationLinksAt st' st oid := .inl h

theorem trans {st₁ st₂ st₃ : SystemState} (h₂ : objectAgreesOffDerivationLinksAt st₃ st₂ oid)
    (h₁ : objectAgreesOffDerivationLinksAt st₂ st₁ oid) :
    objectAgreesOffDerivationLinksAt st₃ st₁ oid := by
  rcases h₂ with e₂ | ⟨b, c, hb, hc, hbc⟩
  · rcases h₁ with e₁ | ⟨a, b', ha, hb', hab⟩
    · exact .inl (e₂.trans e₁)
    · exact .inr ⟨a, b', ha, e₂.trans hb', hab⟩
  · rcases h₁ with e₁ | ⟨a, b', ha, hb', hab⟩
    · exact .inr ⟨b, c, e₁ ▸ hb, hc, hbc⟩
    · rw [hb'] at hb; cases hb
      exact .inr ⟨a, c, ha, hc, hbc.trans hab⟩

/-- A non-CNode object read in the later state was there before. -/
theorem obj_back (h : objectAgreesOffDerivationLinksAt st' st oid) {o : KernelObject}
    (h' : st'.objects[oid]? = some o) (hn : ∀ cn, o ≠ .cnode cn) :
    st.objects[oid]? = some o := by
  rcases h with e | ⟨_, _, _, hb, _⟩
  · rw [← e]; exact h'
  · rw [hb] at h'; cases h'; exact absurd rfl (hn _)

/-- A non-CNode object is still there afterwards. -/
theorem obj_fwd (h : objectAgreesOffDerivationLinksAt st' st oid) {o : KernelObject}
    (h' : st.objects[oid]? = some o) (hn : ∀ cn, o ≠ .cnode cn) :
    st'.objects[oid]? = some o := by
  rcases h with e | ⟨_, _, ha, _, _⟩
  · rw [e]; exact h'
  · rw [ha] at h'; cases h'; exact absurd rfl (hn _)

theorem cnode_fwd (h : objectAgreesOffDerivationLinksAt st' st oid) {cn : CNode}
    (hc : st.objects[oid]? = some (.cnode cn)) :
    ∃ cn', st'.objects[oid]? = some (.cnode cn') ∧ cn'.withoutLinks = cn.withoutLinks := by
  rcases h with e | ⟨cn0, cn', ha, hb, hw⟩
  · exact ⟨cn, e.trans hc, rfl⟩
  · rw [ha] at hc; cases hc; exact ⟨cn', hb, hw⟩

end objectAgreesOffDerivationLinksAt

namespace objectsAgreeOffDerivationLinks

theorem refl (st : SystemState) : objectsAgreeOffDerivationLinks st st := fun _ => .inl rfl

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    objectsAgreeOffDerivationLinks st' st := fun _ => .inl (by rw [h])

theorem of_linksOnlyWrite {st st' : SystemState} (h : linksOnlyWrite st st') :
    objectsAgreeOffDerivationLinks st' st := h.2

/-- The relation reads the object stores alone. -/
theorem congr {a a' b b' : SystemState} (ha : a'.objects = a.objects)
    (hb : b'.objects = b.objects) (h : objectsAgreeOffDerivationLinks a b) :
    objectsAgreeOffDerivationLinks a' b' := fun x => by rw [ha, hb]; exact h x

theorem trans {st₁ st₂ st₃ : SystemState} (h₂ : objectsAgreeOffDerivationLinks st₃ st₂)
    (h₁ : objectsAgreeOffDerivationLinks st₂ st₁) : objectsAgreeOffDerivationLinks st₃ st₁ := by
  intro oid
  rcases h₂ oid with e₂ | ⟨b, c, hb, hc, hbc⟩
  · rcases h₁ oid with e₁ | ⟨a, b', ha, hb', hab⟩
    · exact .inl (e₂.trans e₁)
    · exact .inr ⟨a, b', ha, e₂.trans hb', hab⟩
  · rcases h₁ oid with e₁ | ⟨a, b', ha, hb', hab⟩
    · exact .inr ⟨b, c, e₁ ▸ hb, hc, hbc⟩
    · rw [hb'] at hb; cases hb; exact .inr ⟨a, c, ha, hc, hbc.trans hab⟩

variable {st st' : SystemState} (h : objectsAgreeOffDerivationLinks st' st)
include h

theorem cnode_back {oid : SeLe4n.ObjId} {cn' : CNode} (h' : st'.objects[oid]? = some (.cnode cn')) :
    ∃ cn, st.objects[oid]? = some (.cnode cn) ∧ cn'.withoutLinks = cn.withoutLinks := by
  rcases h oid with e | ⟨cn, cn'', ha, hb, hc⟩
  · exact ⟨cn', e ▸ h', rfl⟩
  · rw [hb] at h'; cases h'; exact ⟨cn, ha, hc⟩

theorem cnode_fwd {oid : SeLe4n.ObjId} {cn : CNode} (hc : st.objects[oid]? = some (.cnode cn)) :
    ∃ cn', st'.objects[oid]? = some (.cnode cn') ∧ cn'.withoutLinks = cn.withoutLinks := by
  rcases h oid with e | ⟨cn0, cn', ha, hb, hw⟩
  · exact ⟨cn, e.trans hc, rfl⟩
  · rw [hc] at ha; cases ha; exact ⟨cn', hb, hw⟩

/-- Link writes keep every slot inside or outside its CNode. -/
theorem slotInCNode_iff (r : SlotRef) : st'.slotInCNode r ↔ st.slotInCNode r := by
  constructor
  · rintro ⟨cn', hc', hs⟩
    obtain ⟨cn, hc, hw⟩ := h.cnode_back hc'
    exact ⟨cn, hc, by
      have := congrArg CNode.radixWidth hw; simp only [CNode.radixWidth_withoutLinks] at this
      rw [← this]; exact hs⟩
  · rintro ⟨cn, hc, hs⟩
    obtain ⟨cn', hc', hw⟩ := h.cnode_fwd hc
    exact ⟨cn', hc', by
      have := congrArg CNode.radixWidth hw; simp only [CNode.radixWidth_withoutLinks] at this
      rw [this]; exact hs⟩

theorem obj_back {oid : SeLe4n.ObjId} {o : KernelObject} (h' : st'.objects[oid]? = some o)
    (hn : ∀ cn, o ≠ .cnode cn) : st.objects[oid]? = some o := by
  rcases h oid with e | ⟨cn, cn', ha, hb, hc⟩
  · rw [← e]; exact h'
  · rw [hb] at h'; cases h'; exact absurd rfl (hn cn')

theorem obj_fwd {oid : SeLe4n.ObjId} {o : KernelObject} (h' : st.objects[oid]? = some o)
    (hn : ∀ cn, o ≠ .cnode cn) : st'.objects[oid]? = some o := by
  rcases h oid with e | ⟨cn, cn', ha, hb, hc⟩
  · rw [e]; exact h'
  · rw [ha] at h'; cases h'; exact absurd rfl (hn cn)

/-- A non-CNode object reads the same in both stores. -/
theorem obj_iff {oid : SeLe4n.ObjId} {o : KernelObject} (hn : ∀ cn, o ≠ .cnode cn) :
    st'.objects[oid]? = some o ↔ st.objects[oid]? = some o :=
  ⟨fun e => h.obj_back e hn, fun e => h.obj_fwd e hn⟩

theorem none_iff {oid : SeLe4n.ObjId} : st'.objects[oid]? = none ↔ st.objects[oid]? = none := by
  rcases h oid with e | ⟨cn, cn', ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]; simp

/-- Slot lookups never read links. -/
theorem lookupSlotCap (r : SlotRef) : st'.lookupSlotCap r = st.lookupSlotCap r := by
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  rcases h r.cnode with e | ⟨cn, cn', ha, hb, hw⟩
  · rw [e]
  · rw [ha, hb]; exact CNode.proj_eq_of_withoutLinks_eq (·.lookup r.slot) hw

theorem getCNode?_isSome (id : SeLe4n.ObjId) :
    (st'.getCNode? id).isSome = (st.getCNode? id).isSome := by
  unfold SystemState.getCNode?
  rcases h id with e | ⟨cn, cn', ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]; rfl

theorem getTcb? (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?
  rcases h tid.toObjId with e | ⟨cn, cn', ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]

theorem getSchedContext? (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  rcases h scId.toObjId with e | ⟨cn, cn', ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]

theorem getReply? (rid : SeLe4n.ReplyId) : st'.getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?
  rcases h rid.toObjId with e | ⟨cn, cn', ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]

end objectsAgreeOffDerivationLinks

/-- **A state reached from `st₀` by link-word writes alone**: what every link
writer below produces.  A property every single link write keeps holds of every
state so reached (`linkReach.closed`), so a consumer frames a writer once, at
`setSlotLinkWords`. -/
inductive linkReach : SystemState → SystemState → Prop
  | refl (st : SystemState) : linkReach st st
  | step {st₀ st : SystemState} (h : linkReach st₀ st) (o : SeLe4n.ObjId)
      (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
      linkReach st₀ (st.setSlotLinkWords o s f c w)

theorem linkReach.trans {st₀ st₁ st₂ : SystemState} (h₁ : linkReach st₀ st₁)
    (h₂ : linkReach st₁ st₂) : linkReach st₀ st₂ := by
  induction h₂ with
  | refl => exact h₁
  | step _ o s f c w ih => exact ih.step o s f c w

/-- A property of well-formed states that every link write keeps holds after
any run of link writes. -/
theorem linkReach.closed {P : SystemState → Prop}
    (hP : ∀ st o s f c w, st.objects.invExt → P st → P (st.setSlotLinkWords o s f c w))
    {st₀ st : SystemState} (h : linkReach st₀ st) (hInv : st₀.objects.invExt) (h₀ : P st₀) :
    P st ∧ st.objects.invExt := by
  induction h with
  | refl => exact ⟨h₀, hInv⟩
  | step _ o s f c w ih =>
      exact ⟨hP _ o s f c w ih.2 ih.1, setSlotLinkWords_invExt ih.2 o s f c w⟩

theorem linkReach.cdt {st₀ st : SystemState} (h : linkReach st₀ st) : st.cdt = st₀.cdt := by
  induction h with
  | refl => rfl
  | step _ o s f c w ih => rw [setSlotLinkWords_cdt]; exact ih

theorem setSlotLinkWords_fields (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) :
    st.setSlotLinkWords o s f c w = { st with objects := (st.setSlotLinkWords o s f c w).objects } := by
  rw [setSlotLinkWords_def]; unfold modifyObject
  split <;> rfl

/-- A link write commutes with replacing the tree: it reads and writes objects alone. -/
theorem setSlotLinkWords_with_cdt (st : SystemState) (cdt : CapDerivationTree) (o : SeLe4n.ObjId)
    (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    ({ st with cdt := cdt } : SystemState).setSlotLinkWords o s f c w =
      { st.setSlotLinkWords o s f c w with cdt := cdt } := by
  simp only [setSlotLinkWords_def]; unfold modifyObject
  have e : ({ st with cdt := cdt } : SystemState).objects = st.objects := rfl
  rw [e]
  cases h : st.objects[o]? with
  | none => rfl
  | some ob => cases ob <;> rfl

/-- Every field but the objects is the start state's. -/
theorem linkReach.fields {st₀ st : SystemState} (h : linkReach st₀ st) :
    st = { st₀ with objects := st.objects } := by
  induction h with
  | refl => rfl
  | step _ o s f c w ih => rw [setSlotLinkWords_fields]; rw [ih]

/-- Link writes run the same with the tree replaced. -/
theorem linkReach.with_cdt {st₀ st : SystemState} (h : linkReach st₀ st) (cdt : CapDerivationTree) :
    linkReach { st₀ with cdt := cdt } { st with cdt := cdt } := by
  induction h with
  | refl => exact .refl _
  | step _ o s f c w ih => rw [← setSlotLinkWords_with_cdt]; exact ih.step o s f c w

theorem linkReach.invExt {st₀ st : SystemState} (h : linkReach st₀ st)
    (hInv : st₀.objects.invExt) : st.objects.invExt :=
  (h.closed (P := fun _ => True) (fun _ _ _ _ _ _ _ _ => trivial) hInv trivial).2

theorem linkReach.linksOnly {st₀ st : SystemState} (h : linkReach st₀ st)
    (hInv : st₀.objects.invExt) : linksOnlyWrite st₀ st := by
  induction h with
  | refl => exact linksOnlyWrite.refl _
  | step h' o s f c w ih =>
      exact ih.trans (setSlotLinkWords_linksOnlyWrite (h'.invExt hInv) o s f c w)

theorem linkReach.agree {st₀ st : SystemState} (h : linkReach st₀ st)
    (hInv : st₀.objects.invExt) : objectsAgreeOffDerivationLinks st st₀ :=
  (h.linksOnly hInv).2

theorem linkAddChild_reach {st₀ st : SystemState} (h : linkReach st₀ st) (p c : SlotRef) :
    linkReach st₀ (st.linkAddChild p c) := by
  have h3 := ((h.step c.cnode c.slot .parent (p.cnode.toNat + 1) (p.slot.toNat + 1)).step
    c.cnode c.slot .next (st.slotLinkNodeWord p.cnode p.slot .firstChild)
      (st.slotLinkSlotWord p.cnode p.slot .firstChild)).step c.cnode c.slot .prev 0 0
  unfold linkAddChild
  simp only
  split
  · exact h3.step _ _ _ _ _
  · exact (h3.step _ _ _ _ _).step _ _ _ _ _

theorem linkUnlinkChild_reach {st₀ st : SystemState} (h : linkReach st₀ st) (n : SlotRef) :
    linkReach st₀ (st.linkUnlinkChild n) := by
  unfold linkUnlinkChild; simp only
  have h1 : linkReach st₀ (if st.slotLinkNodeWord n.cnode n.slot .prev = 0 then
      (if st.slotLinkNodeWord n.cnode n.slot .parent = 0 then st
       else st.setSlotLinkWords (SeLe4n.ObjId.ofNat (st.slotLinkNodeWord n.cnode n.slot .parent - 1))
        (SeLe4n.Slot.ofNat (st.slotLinkSlotWord n.cnode n.slot .parent - 1)) .firstChild
        (st.slotLinkNodeWord n.cnode n.slot .next) (st.slotLinkSlotWord n.cnode n.slot .next))
      else st.setSlotLinkWords (SeLe4n.ObjId.ofNat (st.slotLinkNodeWord n.cnode n.slot .prev - 1))
        (SeLe4n.Slot.ofNat (st.slotLinkSlotWord n.cnode n.slot .prev - 1)) .next
        (st.slotLinkNodeWord n.cnode n.slot .next) (st.slotLinkSlotWord n.cnode n.slot .next)) := by
    split
    · split
      · exact h
      · exact h.step _ _ _ _ _
    · exact h.step _ _ _ _ _
  generalize (if st.slotLinkNodeWord n.cnode n.slot .prev = 0 then _ else _) = st1 at h1 ⊢
  have h2 : linkReach st₀ (if st.slotLinkNodeWord n.cnode n.slot .next = 0 then st1
      else st1.setSlotLinkWords (SeLe4n.ObjId.ofNat (st.slotLinkNodeWord n.cnode n.slot .next - 1))
        (SeLe4n.Slot.ofNat (st.slotLinkSlotWord n.cnode n.slot .next - 1)) .prev
        (st.slotLinkNodeWord n.cnode n.slot .prev) (st.slotLinkSlotWord n.cnode n.slot .prev)) := by
    split
    · exact h1
    · exact h1.step _ _ _ _ _
  exact ((h2.step _ _ _ _ _).step _ _ _ _ _).step _ _ _ _ _

theorem linkOrphanChain_reach : ∀ (k : Nat) {st₀ st : SystemState} (c w : Nat), linkReach st₀ st →
    linkReach st₀ (linkOrphanChain k st c w)
  | 0, _, _, _, _, h => h
  | k + 1, _, _, c, _, h => by
    unfold linkOrphanChain
    split
    · exact h
    · exact linkOrphanChain_reach k _ _ (((h.step _ _ _ _ _).step _ _ _ _ _).step _ _ _ _ _)

theorem linkReparentChain_reach : ∀ (k : Nat) {st₀ st : SystemState} (u : SlotRef) (c w : Nat),
    linkReach st₀ st → linkReach st₀ (linkReparentChain k st u c w)
  | 0, _, _, _, _, _, h => h
  | k + 1, _, _, u, c, _, h => by
    unfold linkReparentChain
    split
    · exact h
    · exact linkReparentChain_reach k u _ _ (linkAddChild_reach h _ _)

theorem linkRemoveNode_reach {st₀ st : SystemState} (h : linkReach st₀ st) (n : SlotRef) (k : Nat) :
    linkReach st₀ (st.linkRemoveNode n k) :=
  (linkOrphanChain_reach k _ _ (linkUnlinkChild_reach h n)).step _ _ _ _ _

theorem linkSpliceNode_reach {st₀ st : SystemState} (h : linkReach st₀ st) (n : SlotRef) (k : Nat) :
    linkReach st₀ (st.linkSpliceNode n k) := by
  unfold linkSpliceNode; simp only
  split
  · exact linkRemoveNode_reach h n k
  · exact (linkReparentChain_reach k _ _ _ (linkUnlinkChild_reach h n)).step _ _ _ _ _

theorem linkMoveNode_reach {st₀ st : SystemState} (h : linkReach st₀ st) (old new : SlotRef)
    (k : Nat) : linkReach st₀ (st.linkMoveNode old new k) := by
  unfold linkMoveNode; simp only
  have h1 := linkUnlinkChild_reach h old
  refine (linkReparentChain_reach k _ _ _ ?_).step _ _ _ _ _
  split
  · exact h1
  · exact linkAddChild_reach h1 _ _

/-! ## Tree updates with the links that spell them

Each tree update the kernel makes, then its link writes (which read only links,
so they may follow the tree's own update).  The walks' fuel is the pre-state's edge count, which bounds every child chain
(`LinksAgree.walk_firstChild`).  Given links that agree with an acyclic tree
whose every slot lies in a live CNode, the post-state's links agree with the
post-state's tree. -/

/-- **Record `c` as derived from `p`**: the edge, and the links that spell it. -/
@[inline] def cdtAddChild (st : SystemState) (p c : SlotRef) (op : DerivationOp) : SystemState :=
  (st.modifyCdt (·.addEdge p c op)).linkAddChild p c

/-- **Splice `n` out of the tree**, its children moving to its parent. -/
@[inline] def cdtSplice (st : SystemState) (n : SlotRef) : SystemState :=
  let k := st.cdt.edges.length
  (st.modifyCdt (·.spliceNode n)).linkSpliceNode n k

/-- **Move node `old` to slot `new`**. -/
@[inline] def cdtMove (st : SystemState) (old new : SlotRef) : SystemState :=
  let k := st.cdt.edges.length
  (st.modifyCdt (·.moveNode old new)).linkMoveNode old new k

/-- **Remove node `n` and every edge at it**, its children becoming roots. -/
@[inline] def cdtRemove (st : SystemState) (n : SlotRef) : SystemState :=
  let k := st.cdt.edges.length
  (st.modifyCdt (·.removeNode n)).linkRemoveNode n k

theorem cdtAddChild_reach (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    linkReach { st with cdt := st.cdt.addEdge p c op } (st.cdtAddChild p c op) :=
  linkAddChild_reach (linkReach.refl _) p c

theorem cdtSplice_reach (st : SystemState) (n : SlotRef) :
    linkReach { st with cdt := st.cdt.spliceNode n } (st.cdtSplice n) :=
  linkSpliceNode_reach (linkReach.refl _) n _

theorem cdtMove_reach (st : SystemState) (old new : SlotRef) :
    linkReach { st with cdt := st.cdt.moveNode old new } (st.cdtMove old new) :=
  linkMoveNode_reach (linkReach.refl _) old new _

theorem cdtRemove_reach (st : SystemState) (n : SlotRef) :
    linkReach { st with cdt := st.cdt.removeNode n } (st.cdtRemove n) :=
  linkRemoveNode_reach (linkReach.refl _) n _

/-- Adding `c` under `p` keeps the links agreeing with the tree, when `c` has no
parent yet and every slot involved lies in a live CNode. -/
theorem cdtAddChild_agree {st : SystemState} (hInv : st.objects.invExt)
    (hL : LinksAgree st.slotLinkAt st.cdt) (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r)
    {p c : SlotRef} (op : DerivationOp) (hp : st.slotInCNode p) (hc : st.slotInCNode c)
    (hcN : st.cdt.parentOf c = none) (hpc : p ≠ c) :
    LinksAgree (st.cdtAddChild p c op).slotLinkAt (st.cdtAddChild p c op).cdt := by
  rw [(cdtAddChild_reach st p c op).cdt]
  unfold cdtAddChild; simp only [modifyCdt_eq]
  rw [slotLinkAt_linkAddChild (st := { st with cdt := st.cdt.addEdge p c op }) hInv hp hc
    (fun x hx => hM x (hL.target_mentions hx))]
  exact hL.addChild op hcN hpc

/-- Splicing a slot of a live CNode out of an acyclic tree keeps the links
agreeing with it (`cdtSplice_agree` drops the side condition). -/
theorem cdtSplice_agree_of_slotInCNode {st : SystemState} (hInv : st.objects.invExt)
    (hL : LinksAgree st.slotLinkAt st.cdt) (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r)
    (hWF : st.cdt.edgeWellFounded) {n : SlotRef} (hn : st.slotInCNode n) :
    LinksAgree (st.cdtSplice n).slotLinkAt (st.cdtSplice n).cdt := by
  rw [(cdtSplice_reach st n).cdt]
  have hW := hL.walk_firstChild n (Nat.le_refl st.cdt.edges.length)
  have hAll : ∀ r f x, st.slotLinkAt r f = some x → st.slotInCNode x :=
    fun _ _ x hx => hM x (hL.target_mentions hx)
  have hSelf := hL.children_not_self_or_prev (hL.parentOf_ne_self_of_wf hWF n)
  have hX : ({ st with cdt := st.cdt.spliceNode n } : SystemState).slotLinkAt = st.slotLinkAt := rfl
  obtain ⟨-, -, hV⟩ := linkSpliceNode_spec (st := { st with cdt := st.cdt.spliceNode n }) hInv
    st.cdt.edges.length hn (by rw [hX]; exact hAll)
    (by rw [hX, hW]; exact CapDerivationTree.childrenOf_nodup hL.childrenUnique n)
    (by rw [hX, hW]; exact hSelf)
  unfold cdtSplice; simp only [modifyCdt_eq]
  rw [hV, hX, hW, hL.parent n]
  have hS := hL.spliceNode_of_wf hWF n
  unfold LinkView.spliceLinks at hS
  cases hu : st.cdt.parentOf n with
  | none => rw [hu] at hS; exact hS
  | some u => rw [hu] at hS; exact hS

/-- Moving node `old` of an acyclic tree to a slot `new` outside it keeps the
links agreeing with the tree. -/
theorem cdtMove_agree {st : SystemState} (hInv : st.objects.invExt)
    (hL : LinksAgree st.slotLinkAt st.cdt) (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r)
    (hWF : st.cdt.edgeWellFounded) {old new : SlotRef} (ho : st.slotInCNode old)
    (hnw : st.slotInCNode new) (hnew : ¬ st.cdt.mentions new) (hon : old ≠ new) :
    LinksAgree (st.cdtMove old new).slotLinkAt (st.cdtMove old new).cdt := by
  rw [(cdtMove_reach st old new).cdt]
  have hW := hL.walk_firstChild old (Nat.le_refl st.cdt.edges.length)
  have hAll : ∀ r f x, st.slotLinkAt r f = some x → st.slotInCNode x :=
    fun _ _ x hx => hM x (hL.target_mentions hx)
  have hSelf := hL.children_not_self_or_prev (hL.parentOf_ne_self_of_wf hWF old)
  have hX : ({ st with cdt := st.cdt.moveNode old new } : SystemState).slotLinkAt =
      st.slotLinkAt := rfl
  obtain ⟨-, -, hV⟩ := linkMoveNode_spec (st := { st with cdt := st.cdt.moveNode old new }) hInv
    st.cdt.edges.length ho hnw (by rw [hX]; exact hAll)
    (by rw [hX, hW]; exact CapDerivationTree.childrenOf_nodup hL.childrenUnique old)
    (by
      rw [hX, hW]
      intro w hw
      obtain ⟨h1, h2⟩ := hSelf w hw
      refine ⟨h1, h2, fun e => hnew (e ▸ ?_)⟩
      obtain ⟨e', he', -, hc⟩ := (CapDerivationTree.mem_childrenOf st.cdt old w).mp hw
      exact ⟨e', he', .inr hc⟩)
  unfold cdtMove; simp only [modifyCdt_eq]
  rw [hV, hX, hW, hL.parent old]
  exact hL.moveNode_of_wf hWF old new hnew hon

/-- Removing node `n` keeps the links agreeing with the tree, when the tree is
acyclic. -/
theorem cdtRemove_agree_of_slotInCNode {st : SystemState} (hInv : st.objects.invExt)
    (hL : LinksAgree st.slotLinkAt st.cdt) (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r)
    (hWF : st.cdt.edgeWellFounded) {n : SlotRef} (hn : st.slotInCNode n) :
    LinksAgree (st.cdtRemove n).slotLinkAt (st.cdtRemove n).cdt := by
  rw [(cdtRemove_reach st n).cdt]
  have hW := hL.walk_firstChild n (Nat.le_refl st.cdt.edges.length)
  have hAll : ∀ r f x, st.slotLinkAt r f = some x → st.slotInCNode x :=
    fun _ _ x hx => hM x (hL.target_mentions hx)
  have hSelf := hL.children_not_self_or_prev (hL.parentOf_ne_self_of_wf hWF n)
  have hX : ({ st with cdt := st.cdt.removeNode n } : SystemState).slotLinkAt = st.slotLinkAt := rfl
  obtain ⟨-, -, hV⟩ := linkRemoveNode_spec (st := { st with cdt := st.cdt.removeNode n }) hInv
    st.cdt.edges.length hn (fun f x h => hAll n f x h) (walk_valid hAll _ n .firstChild)
    (by rw [hX, hW]; exact CapDerivationTree.childrenOf_nodup hL.childrenUnique n)
    (by rw [hX, hW]; exact hSelf)
  unfold cdtRemove; simp only [modifyCdt_eq]
  rw [hV, hX, hW]
  exact hL.removeNode n

/-! ### What a paired tree update leaves alone

Every field but the tree and the object store is the pre-state's, and the
objects agree with the pre-state's up to derivation links. -/

theorem cdtAddChild_fields (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    st.cdtAddChild p c op = { st with cdt := st.cdt.addEdge p c op, objects := (st.cdtAddChild p c op).objects } :=
  (cdtAddChild_reach st p c op).fields

@[simp] theorem cdtAddChild_cdt (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).cdt = st.cdt.addEdge p c op := (cdtAddChild_reach st p c op).cdt

@[simp] theorem cdtAddChild_machine (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).machine = st.machine := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_objectIndex (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).objectIndex = st.objectIndex := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_objectIndexSet (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).objectIndexSet = st.objectIndexSet := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_services (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).services = st.services := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_scheduler (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).scheduler = st.scheduler := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_irqHandlers (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).irqHandlers = st.irqHandlers := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_lifecycle (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).lifecycle = st.lifecycle := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_asidTable (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).asidTable = st.asidTable := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_interfaceRegistry (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).interfaceRegistry = st.interfaceRegistry := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_serviceRegistry (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).serviceRegistry = st.serviceRegistry := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_tlb (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).tlb = st.tlb := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_tlbShootdown (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).tlbShootdown = st.tlbShootdown := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_perCoreTlb (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).perCoreTlb = st.perCoreTlb := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_perCoreICache (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).perCoreICache = st.perCoreICache := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_pendingIcacheMaintenance (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).pendingIcacheMaintenance = st.pendingIcacheMaintenance := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_pendingPhysicalWrites (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).pendingPhysicalWrites = st.pendingPhysicalWrites := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_declassificationAuditLog (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).declassificationAuditLog = st.declassificationAuditLog := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_declassificationAuditEpoch (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).declassificationAuditEpoch = st.declassificationAuditEpoch := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_declassificationRefusals (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).declassificationRefusals = st.declassificationRefusals := by rw [cdtAddChild_fields]

@[simp] theorem cdtAddChild_declassificationTaint (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).declassificationTaint = st.declassificationTaint := by rw [cdtAddChild_fields]

theorem cdtAddChild_agreeObjects {st : SystemState} (hInv : st.objects.invExt) (p c : SlotRef) (op : DerivationOp) :
    objectsAgreeOffDerivationLinks (st.cdtAddChild p c op) st ∧ (st.cdtAddChild p c op).objects.invExt :=
  ⟨(cdtAddChild_reach st p c op).agree hInv, (cdtAddChild_reach st p c op).invExt hInv⟩

theorem cdtSplice_fields (st : SystemState) (n : SlotRef) :
    st.cdtSplice n = { st with cdt := st.cdt.spliceNode n, objects := (st.cdtSplice n).objects } :=
  (cdtSplice_reach st n).fields

@[simp] theorem cdtSplice_cdt (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).cdt = st.cdt.spliceNode n := (cdtSplice_reach st n).cdt

@[simp] theorem cdtSplice_machine (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).machine = st.machine := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_objectIndex (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).objectIndex = st.objectIndex := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_objectIndexSet (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).objectIndexSet = st.objectIndexSet := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_services (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).services = st.services := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_scheduler (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).scheduler = st.scheduler := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_irqHandlers (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).irqHandlers = st.irqHandlers := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_lifecycle (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).lifecycle = st.lifecycle := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_asidTable (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).asidTable = st.asidTable := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_interfaceRegistry (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).interfaceRegistry = st.interfaceRegistry := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_serviceRegistry (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).serviceRegistry = st.serviceRegistry := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_tlb (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).tlb = st.tlb := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_tlbShootdown (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).tlbShootdown = st.tlbShootdown := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_perCoreTlb (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).perCoreTlb = st.perCoreTlb := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_perCoreICache (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).perCoreICache = st.perCoreICache := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_pendingIcacheMaintenance (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).pendingIcacheMaintenance = st.pendingIcacheMaintenance := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_pendingPhysicalWrites (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).pendingPhysicalWrites = st.pendingPhysicalWrites := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_declassificationAuditLog (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).declassificationAuditLog = st.declassificationAuditLog := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_declassificationAuditEpoch (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).declassificationAuditEpoch = st.declassificationAuditEpoch := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_declassificationRefusals (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).declassificationRefusals = st.declassificationRefusals := by rw [cdtSplice_fields]

@[simp] theorem cdtSplice_declassificationTaint (st : SystemState) (n : SlotRef) :
    (st.cdtSplice n).declassificationTaint = st.declassificationTaint := by rw [cdtSplice_fields]

theorem cdtSplice_agreeObjects {st : SystemState} (hInv : st.objects.invExt) (n : SlotRef) :
    objectsAgreeOffDerivationLinks (st.cdtSplice n) st ∧ (st.cdtSplice n).objects.invExt :=
  ⟨(cdtSplice_reach st n).agree hInv, (cdtSplice_reach st n).invExt hInv⟩

theorem cdtMove_fields (st : SystemState) (old new : SlotRef) :
    st.cdtMove old new = { st with cdt := st.cdt.moveNode old new, objects := (st.cdtMove old new).objects } :=
  (cdtMove_reach st old new).fields

@[simp] theorem cdtMove_cdt (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).cdt = st.cdt.moveNode old new := (cdtMove_reach st old new).cdt

@[simp] theorem cdtMove_machine (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).machine = st.machine := by rw [cdtMove_fields]

@[simp] theorem cdtMove_objectIndex (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).objectIndex = st.objectIndex := by rw [cdtMove_fields]

@[simp] theorem cdtMove_objectIndexSet (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).objectIndexSet = st.objectIndexSet := by rw [cdtMove_fields]

@[simp] theorem cdtMove_services (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).services = st.services := by rw [cdtMove_fields]

@[simp] theorem cdtMove_scheduler (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).scheduler = st.scheduler := by rw [cdtMove_fields]

@[simp] theorem cdtMove_irqHandlers (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).irqHandlers = st.irqHandlers := by rw [cdtMove_fields]

@[simp] theorem cdtMove_lifecycle (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).lifecycle = st.lifecycle := by rw [cdtMove_fields]

@[simp] theorem cdtMove_asidTable (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).asidTable = st.asidTable := by rw [cdtMove_fields]

@[simp] theorem cdtMove_interfaceRegistry (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).interfaceRegistry = st.interfaceRegistry := by rw [cdtMove_fields]

@[simp] theorem cdtMove_serviceRegistry (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).serviceRegistry = st.serviceRegistry := by rw [cdtMove_fields]

@[simp] theorem cdtMove_tlb (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).tlb = st.tlb := by rw [cdtMove_fields]

@[simp] theorem cdtMove_tlbShootdown (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).tlbShootdown = st.tlbShootdown := by rw [cdtMove_fields]

@[simp] theorem cdtMove_perCoreTlb (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).perCoreTlb = st.perCoreTlb := by rw [cdtMove_fields]

@[simp] theorem cdtMove_perCoreICache (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).perCoreICache = st.perCoreICache := by rw [cdtMove_fields]

@[simp] theorem cdtMove_pendingIcacheMaintenance (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).pendingIcacheMaintenance = st.pendingIcacheMaintenance := by rw [cdtMove_fields]

@[simp] theorem cdtMove_pendingPhysicalWrites (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).pendingPhysicalWrites = st.pendingPhysicalWrites := by rw [cdtMove_fields]

@[simp] theorem cdtMove_declassificationAuditLog (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).declassificationAuditLog = st.declassificationAuditLog := by rw [cdtMove_fields]

@[simp] theorem cdtMove_declassificationAuditEpoch (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).declassificationAuditEpoch = st.declassificationAuditEpoch := by rw [cdtMove_fields]

@[simp] theorem cdtMove_declassificationRefusals (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).declassificationRefusals = st.declassificationRefusals := by rw [cdtMove_fields]

@[simp] theorem cdtMove_declassificationTaint (st : SystemState) (old new : SlotRef) :
    (st.cdtMove old new).declassificationTaint = st.declassificationTaint := by rw [cdtMove_fields]

theorem cdtMove_agreeObjects {st : SystemState} (hInv : st.objects.invExt) (old new : SlotRef) :
    objectsAgreeOffDerivationLinks (st.cdtMove old new) st ∧ (st.cdtMove old new).objects.invExt :=
  ⟨(cdtMove_reach st old new).agree hInv, (cdtMove_reach st old new).invExt hInv⟩

theorem cdtRemove_fields (st : SystemState) (n : SlotRef) :
    st.cdtRemove n = { st with cdt := st.cdt.removeNode n, objects := (st.cdtRemove n).objects } :=
  (cdtRemove_reach st n).fields

@[simp] theorem cdtRemove_cdt (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).cdt = st.cdt.removeNode n := (cdtRemove_reach st n).cdt

@[simp] theorem cdtRemove_machine (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).machine = st.machine := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_objectIndex (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).objectIndex = st.objectIndex := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_objectIndexSet (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).objectIndexSet = st.objectIndexSet := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_services (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).services = st.services := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_scheduler (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).scheduler = st.scheduler := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_irqHandlers (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).irqHandlers = st.irqHandlers := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_lifecycle (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).lifecycle = st.lifecycle := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_asidTable (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).asidTable = st.asidTable := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_interfaceRegistry (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).interfaceRegistry = st.interfaceRegistry := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_serviceRegistry (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).serviceRegistry = st.serviceRegistry := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_tlb (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).tlb = st.tlb := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_tlbShootdown (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).tlbShootdown = st.tlbShootdown := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_perCoreTlb (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).perCoreTlb = st.perCoreTlb := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_perCoreICache (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).perCoreICache = st.perCoreICache := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_pendingIcacheMaintenance (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).pendingIcacheMaintenance = st.pendingIcacheMaintenance := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_pendingPhysicalWrites (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).pendingPhysicalWrites = st.pendingPhysicalWrites := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_declassificationAuditLog (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).declassificationAuditLog = st.declassificationAuditLog := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_declassificationAuditEpoch (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).declassificationAuditEpoch = st.declassificationAuditEpoch := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_declassificationRefusals (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).declassificationRefusals = st.declassificationRefusals := by rw [cdtRemove_fields]

@[simp] theorem cdtRemove_declassificationTaint (st : SystemState) (n : SlotRef) :
    (st.cdtRemove n).declassificationTaint = st.declassificationTaint := by rw [cdtRemove_fields]

theorem cdtRemove_agreeObjects {st : SystemState} (hInv : st.objects.invExt) (n : SlotRef) :
    objectsAgreeOffDerivationLinks (st.cdtRemove n) st ∧ (st.cdtRemove n).objects.invExt :=
  ⟨(cdtRemove_reach st n).agree hInv, (cdtRemove_reach st n).invExt hInv⟩

/-! ### Steps that keep every slot's links

A step that rewrites a CNode's capabilities or geometry but not its link words,
or that writes no CNode, reads the same link at every slot. -/

/-- The links read the same in two states whose CNodes hold the same link words,
key by key. -/
theorem slotLinkAt_eq_of_links {st st' : SystemState}
    (h : ∀ oid, (st'.getCNode? oid).map CNode.links = (st.getCNode? oid).map CNode.links) :
    st'.slotLinkAt = st.slotLinkAt := by
  funext r f
  have hr := h r.cnode
  unfold slotLinkAt
  cases h1 : st'.getCNode? r.cnode <;> cases h2 : st.getCNode? r.cnode <;>
    rw [h1, h2] at hr <;> simp at hr <;>
    simp only [CNode.linkAt, CNode.linkNodeWord, CNode.linkSlotWord, hr]

/-- The links read the same in two states with the same CNodes. -/
theorem slotLinkAt_eq_of_getCNode {st st' : SystemState}
    (h : ∀ oid, st'.getCNode? oid = st.getCNode? oid) : st'.slotLinkAt = st.slotLinkAt :=
  slotLinkAt_eq_of_links fun oid => by rw [h oid]

/-- Storing over a CNode a CNode with the same link words keeps every slot's
links: a capability write, a slot clear and a slot filter all are such stores. -/
theorem slotLinkAt_storeObject_cnode {st st' : SystemState} {oid : SeLe4n.ObjId}
    {cn cn' : CNode} (hObjInv : st.objects.invExt) (hPre : st.objects[oid]? = some (.cnode cn))
    (hLinks : cn'.links = cn.links) (hStore : storeObject oid (.cnode cn') st = .ok ((), st')) :
    st'.slotLinkAt = st.slotLinkAt := by
  refine slotLinkAt_eq_of_links fun o => ?_
  by_cases h : o = oid
  · subst h
    have h1 := storeObject_objects_eq st st' o _ hObjInv hStore
    rw [(getCNode?_eq_some_iff st' o cn').mpr h1, (getCNode?_eq_some_iff st o cn).mpr hPre]
    simp [hLinks]
  · unfold getCNode?; rw [storeObject_objects_ne st st' oid o _ h hObjInv hStore]

/-- Storing over a CNode a CNode of the same radix keeps every slot inside or
outside its CNode. -/
theorem slotInCNode_storeObject_cnode {st st' : SystemState} {oid : SeLe4n.ObjId}
    {cn cn' : CNode} (hObjInv : st.objects.invExt) (hPre : st.objects[oid]? = some (.cnode cn))
    (hRw : cn'.radixWidth = cn.radixWidth) (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (r : SlotRef) : st'.slotInCNode r ↔ st.slotInCNode r := by
  unfold slotInCNode
  by_cases h : r.cnode = oid
  · rw [h, storeObject_objects_eq st st' oid _ hObjInv hStore, hPre]
    constructor
    · rintro ⟨_, he, hs⟩; cases he; exact ⟨cn, rfl, hRw ▸ hs⟩
    · rintro ⟨_, he, hs⟩; cases he; exact ⟨cn', rfl, hRw ▸ hs⟩
  · rw [storeObject_objects_ne st st' oid r.cnode _ h hObjInv hStore]

/-! ### A slot outside every CNode holds no link words

Its words read 0 and writing them changes no link, so splicing it out of a tree
that does not name it is the identity on the tree and on the links. -/

theorem slotLinkWords_zero_of_not_slotInCNode {st : SystemState} {o : SeLe4n.ObjId}
    {s : SeLe4n.Slot} (h : ¬ st.slotInCNode ⟨o, s⟩) (f : LinkField) :
    st.slotLinkNodeWord o s f = 0 ∧ st.slotLinkSlotWord o s f = 0 := by
  rw [slotLinkNodeWord_def, slotLinkSlotWord_def]
  split
  · next cn hcn =>
    have hs : ¬ s.toNat < 2 ^ cn.radixWidth := fun hs => h ⟨cn, hcn, hs⟩
    have hz := cn.links_size
    have hf : f.offset + 1 < slotLinkWords := by
      cases f <;> simp [LinkField.offset, slotLinkWords]
    have hb : cn.links.size ≤ CNode.linkBase s f := by
      unfold CNode.linkBase; rw [hz]
      have := Nat.mul_le_mul_left slotLinkWords (Nat.le_of_not_lt hs); omega
    simp only [CNode.linkNodeWord, CNode.linkSlotWord, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by omega : cn.links.size ≤ CNode.linkBase s f + 1),
      Array.getElem?_eq_none hb, Option.getD_none, and_self]
  · exact ⟨rfl, rfl⟩

theorem slotLinkAt_setSlotLinkWords_of_not {st : SystemState} (hInv : st.objects.invExt)
    {o : SeLe4n.ObjId} {s : SeLe4n.Slot} (h : ¬ st.slotInCNode ⟨o, s⟩) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords o s f c w).slotLinkAt = st.slotLinkAt := by
  by_cases hc : ∃ cn, st.objects[o]? = some (.cnode cn)
  · obtain ⟨cn, hcn⟩ := hc
    have hs : ¬ s.toNat < 2 ^ cn.radixWidth := fun hs => h ⟨cn, hcn, hs⟩
    have hf : f.offset + 1 < slotLinkWords := by
      cases f <;> simp [LinkField.offset, slotLinkWords]
    have hb : cn.links.size ≤ CNode.linkBase s f := by
      unfold CNode.linkBase; rw [cn.links_size]
      have := Nat.mul_le_mul_left slotLinkWords (Nat.le_of_not_lt hs); omega
    have hL : (cn.setLinkWords s f c w).links = cn.links := by
      simp only [CNode.setLinkWords]
      rw [Array.setIfInBounds_eq_of_size_le hb,
        Array.setIfInBounds_eq_of_size_le (by omega : cn.links.size ≤ CNode.linkBase s f + 1)]
    refine slotLinkAt_eq_of_links fun x => ?_
    unfold getCNode?
    rw [setSlotLinkWords_objects hInv hcn]
    by_cases hx : x = o
    · subst hx; rw [if_pos rfl, hcn]; simp [hL]
    · rw [if_neg hx]
  · rw [setSlotLinkWords_of_not_cnode (fun cn hc' => hc ⟨cn, hc'⟩)]

/-- The four link writes at a slot outside every CNode change no link and keep
it outside every CNode. -/
private theorem slotLinkAt_writes_of_not {st : SystemState} (hInv : st.objects.invExt)
    {n : SlotRef} (h : ¬ st.slotInCNode n) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords n.cnode n.slot f c w).slotLinkAt = st.slotLinkAt ∧
      ¬ (st.setSlotLinkWords n.cnode n.slot f c w).slotInCNode n ∧
      (st.setSlotLinkWords n.cnode n.slot f c w).objects.invExt :=
  ⟨slotLinkAt_setSlotLinkWords_of_not hInv h f c w,
    fun h' => h ((slotInCNode_setSlotLinkWords hInv _ _ f c w n).mp h'),
    setSlotLinkWords_invExt hInv _ _ f c w⟩

/-- **Splicing a slot outside every CNode out of the tree changes nothing**:
the tree does not name it, so the tree is unchanged, and its link words read 0,
so every link write lands nowhere. -/
theorem cdtSplice_of_not_slotInCNode {st : SystemState} (hInv : st.objects.invExt)
    (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r) {n : SlotRef} (hn : ¬ st.slotInCNode n) :
    (st.cdtSplice n).slotLinkAt = st.slotLinkAt ∧ (st.cdtSplice n).cdt = st.cdt := by
  have hNM : ¬ st.cdt.mentions n := fun h => hn (hM n h)
  refine ⟨?_, ?_⟩
  · let s0 : SystemState := { st with cdt := st.cdt.spliceNode n }
    have hn0 : ¬ s0.slotInCNode n := hn
    have hI0 : s0.objects.invExt := hInv
    obtain ⟨zU, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .parent
    obtain ⟨zF, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .firstChild
    obtain ⟨zP, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .prev
    obtain ⟨zN, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .next
    unfold cdtSplice; simp only [modifyCdt_eq]
    show (s0.linkSpliceNode n _).slotLinkAt = st.slotLinkAt
    unfold linkSpliceNode linkRemoveNode linkUnlinkChild
    simp only [zU, zF, zP, zN, if_true]
    obtain ⟨e1, h1, i1⟩ := slotLinkAt_writes_of_not hI0 hn0 .parent 0 0
    obtain ⟨e2, h2, i2⟩ := slotLinkAt_writes_of_not i1 h1 .next 0 0
    obtain ⟨e3, h3, i3⟩ := slotLinkAt_writes_of_not i2 h2 .prev 0 0
    have hOrph : ∀ k (t : SystemState) w, linkOrphanChain k t 0 w = t := by
      intro k t w; cases k <;> rfl
    rw [hOrph]
    obtain ⟨e4, -, -⟩ := slotLinkAt_writes_of_not i3 h3 .firstChild 0 0
    rw [e4, e3, e2, e1]; rfl
  · rw [(cdtSplice_reach st n).cdt]
    show st.cdt.spliceNode n = st.cdt
    have hNone : st.cdt.edges.find? (fun e => e.isChildOf n) = none := by
      rw [List.find?_eq_none]
      intro e he hc
      exact hNM ⟨e, he, .inr (by simpa [CapDerivationEdge.isChildOf] using hc)⟩
    unfold CapDerivationTree.spliceNode CapDerivationTree.removeNode
    rw [hNone]
    simp only
    rw [List.filter_eq_self.mpr]
    intro e he
    have h1 : e.parent ≠ n := fun h => hNM ⟨e, he, .inl h⟩
    have h2 : e.child ≠ n := fun h => hNM ⟨e, he, .inr h⟩
    simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf, h1, h2]

/-- **Splicing any slot out of an acyclic tree keeps the links agreeing with
it**: a slot of a live CNode by the link rewrite, any other because the tree
does not name it and the splice changes nothing. -/
theorem cdtSplice_agree {st : SystemState} (hInv : st.objects.invExt)
    (hL : LinksAgree st.slotLinkAt st.cdt) (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r)
    (hWF : st.cdt.edgeWellFounded) (n : SlotRef) :
    LinksAgree (st.cdtSplice n).slotLinkAt (st.cdtSplice n).cdt := by
  by_cases hn : st.slotInCNode n
  · exact cdtSplice_agree_of_slotInCNode hInv hL hM hWF hn
  · obtain ⟨e1, e2⟩ := cdtSplice_of_not_slotInCNode hInv hM hn
    rw [e1, e2]; exact hL

/-- **Removing a slot outside every CNode from the tree changes nothing**, for
the reason the splice does (`cdtSplice_of_not_slotInCNode`). -/
theorem cdtRemove_of_not_slotInCNode {st : SystemState} (hInv : st.objects.invExt)
    (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r) {n : SlotRef} (hn : ¬ st.slotInCNode n) :
    (st.cdtRemove n).slotLinkAt = st.slotLinkAt ∧ (st.cdtRemove n).cdt = st.cdt := by
  have hNM : ¬ st.cdt.mentions n := fun h => hn (hM n h)
  refine ⟨?_, ?_⟩
  · let s0 : SystemState := { st with cdt := st.cdt.removeNode n }
    have hn0 : ¬ s0.slotInCNode n := hn
    have hI0 : s0.objects.invExt := hInv
    obtain ⟨zU, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .parent
    obtain ⟨zF, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .firstChild
    obtain ⟨zP, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .prev
    obtain ⟨zN, -⟩ := slotLinkWords_zero_of_not_slotInCNode hn0 .next
    unfold cdtRemove; simp only [modifyCdt_eq]
    show (s0.linkRemoveNode n _).slotLinkAt = st.slotLinkAt
    unfold linkRemoveNode linkUnlinkChild
    simp only [zU, zF, zP, zN, if_true]
    obtain ⟨e1, h1, i1⟩ := slotLinkAt_writes_of_not hI0 hn0 .parent 0 0
    obtain ⟨e2, h2, i2⟩ := slotLinkAt_writes_of_not i1 h1 .next 0 0
    obtain ⟨e3, h3, i3⟩ := slotLinkAt_writes_of_not i2 h2 .prev 0 0
    have hOrph : ∀ k (t : SystemState) w, linkOrphanChain k t 0 w = t := by
      intro k t w; cases k <;> rfl
    rw [hOrph]
    obtain ⟨e4, -, -⟩ := slotLinkAt_writes_of_not i3 h3 .firstChild 0 0
    rw [e4, e3, e2, e1]; rfl
  · rw [(cdtRemove_reach st n).cdt]
    show st.cdt.removeNode n = st.cdt
    unfold CapDerivationTree.removeNode
    rw [List.filter_eq_self.mpr]
    intro e he
    have h1 : e.parent ≠ n := fun h => hNM ⟨e, he, .inl h⟩
    have h2 : e.child ≠ n := fun h => hNM ⟨e, he, .inr h⟩
    simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf, h1, h2]

/-- **Removing any slot from an acyclic tree keeps the links agreeing with it.** -/
theorem cdtRemove_agree {st : SystemState} (hInv : st.objects.invExt)
    (hL : LinksAgree st.slotLinkAt st.cdt) (hM : ∀ r, st.cdt.mentions r → st.slotInCNode r)
    (hWF : st.cdt.edgeWellFounded) (n : SlotRef) :
    LinksAgree (st.cdtRemove n).slotLinkAt (st.cdtRemove n).cdt := by
  by_cases hn : st.slotInCNode n
  · exact cdtRemove_agree_of_slotInCNode hInv hL hM hWF hn
  · obtain ⟨e1, e2⟩ := cdtRemove_of_not_slotInCNode hInv hM hn
    rw [e1, e2]; exact hL


end SystemState

end SeLe4n.Model
