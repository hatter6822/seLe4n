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

namespace SystemState

/-- **The derivation links the slots hold**: link `f` of slot `r`, read from its
CNode's link words.  A slot of no CNode holds none. -/
def slotLinkAt (st : SystemState) : LinkView := fun r f =>
  match st.objects[r.cnode]? with
  | some (.cnode cn) => cn.linkAt r.slot f
  | _ => none

/-- The CNode word of link `f` of slot `(o, s)` (0 when it has no target). -/
@[inline] def slotLinkNodeWord (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) : Nat :=
  match st.objects[o]? with
  | some (.cnode cn) => cn.linkNodeWord s f
  | _ => 0

/-- The slot word of link `f` of slot `(o, s)`. -/
@[inline] def slotLinkSlotWord (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) : Nat :=
  match st.objects[o]? with
  | some (.cnode cn) => cn.linkSlotWord s f
  | _ => 0

theorem slotLinkAt_eq_decode (st : SystemState) (r : SlotRef) (f : LinkField) :
    st.slotLinkAt r f =
      decodeLink (st.slotLinkNodeWord r.cnode r.slot f) (st.slotLinkSlotWord r.cnode r.slot f) := by
  unfold slotLinkAt slotLinkNodeWord slotLinkSlotWord
  split <;> rfl

/-- A slot inside a live CNode's slot array: a slot whose links can be written. -/
def slotInCNode (st : SystemState) (r : SlotRef) : Prop :=
  ∃ cn, st.objects[r.cnode]? = some (.cnode cn) ∧ r.slot.toNat < 2 ^ cn.radixWidth

/-- **Write link `f` of slot `(o, s)`** as its two words, in place. -/
@[inline] def setSlotLinkWords (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) : SystemState :=
  st.storeCNodeWith o (·.setLinkWords s f c w)

theorem setSlotLinkWords_objects {st : SystemState} (hInv : st.objects.invExt)
    {o : SeLe4n.ObjId} {cn : CNode} (h : st.objects[o]? = some (.cnode cn))
    (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) (x : SeLe4n.ObjId) :
    (st.setSlotLinkWords o s f c w).objects[x]? =
      if x = o then some (.cnode (cn.setLinkWords s f c w)) else st.objects[x]? := by
  have hS := storeObject_cnode_eq_storeCNodeWith h (·.setLinkWords s f c w)
  unfold setSlotLinkWords
  split
  · next hx => subst hx; exact storeObject_objects_eq _ _ _ _ hInv hS
  · next hx => exact storeObject_objects_ne _ _ _ _ _ hx hInv hS

theorem setSlotLinkWords_of_not_cnode {st : SystemState} {o : SeLe4n.ObjId}
    (h : ∀ cn, st.objects[o]? ≠ some (.cnode cn)) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    st.setSlotLinkWords o s f c w = st := by
  unfold setSlotLinkWords storeCNodeWith
  split
  · next cn hc => exact absurd hc (h cn)
  · rfl

theorem setSlotLinkWords_invExt {st : SystemState} (hInv : st.objects.invExt)
    (o : SeLe4n.ObjId) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords o s f c w).objects.invExt := by
  by_cases h : ∃ cn, st.objects[o]? = some (.cnode cn)
  · obtain ⟨cn, hcn⟩ := h
    exact storeObject_preserves_objects_invExt _ _ _ _ hInv
      (storeObject_cnode_eq_storeCNodeWith hcn (·.setLinkWords s f c w))
  · rw [setSlotLinkWords_of_not_cnode (fun cn hc => h ⟨cn, hc⟩)]; exact hInv

/-- **A link write acts on the link view as `LinkView.set`**, for a slot inside
a live CNode. -/
theorem slotLinkAt_setSlotLinkWords {st : SystemState} (hInv : st.objects.invExt)
    {o : SeLe4n.ObjId} {s : SeLe4n.Slot} (h : st.slotInCNode ⟨o, s⟩) (f : LinkField) (c w : Nat) :
    (st.setSlotLinkWords o s f c w).slotLinkAt = st.slotLinkAt.set ⟨o, s⟩ f (decodeLink c w) := by
  obtain ⟨cn, hcn, hs⟩ := h
  funext r f'
  simp only [slotLinkAt, LinkView.set]
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
    · simp only [if_pos hr, hr, hcn]
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

end SystemState

end SeLe4n.Model
