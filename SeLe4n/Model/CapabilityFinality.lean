-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.SlotTreeShape

/-!
# Capability finality, read from the derivation links

seL4's `isFinalCapability`: a capability is the last one naming its object when
neither of its mapping-database neighbours names that object.  The slots naming
one object form one contiguous preorder run (`TreeShapeOver.sameObjectContiguous`,
seL4's `mdb_chunked`), so a second slot naming the object exists exactly when the
slot right before or right after this one in the preorder names it.  Those two
slots are read from the slot's own four link words: the slot after it is its
first child, its next sibling, or (when it is the last child of its parent and
the run would have to leave the parent's subtree) a slot whose naming forces the
parent to name the object; the slot before it is its parent or its previous
sibling, which names the object whenever a slot below it does.

* `SystemState.capIsFinal` — the kernel's reader: the slot's capability, then the
  parent, first-child, `prev` and `next` words, each decoded inline and its slot's
  capability compared by object id (`Capability.namesObjectWord`).  Word reads
  and comparisons only: no list, no `Option` kept across calls, no closure.
* `SystemState.capFinalSpec` — the specification: no other slot names the
  object the slot's capability names.
* `SystemState.capIsFinal_eq_true_iff_links` — the reader is the link-level
  statement, with no invariant.
* `SystemState.linksFinal_iff_of_shape` — under the links' agreement, the tree
  shape, the occupied tree slots and acyclicity, the link-level statement is the
  specification.
-/

namespace SeLe4n.Model

open CapDerivationTree

/-- **Whether a capability names the object whose identifier word is `o`**:
`Capability.namedObject` compared with `o` by word, building no `Option`.  The
audit-trail capability names nothing. -/
@[inline] def Capability.namesObjectWord (c : Capability) (o : Nat) : Bool :=
  match c.target with
  | .object x => x.val == o
  | .cnodeSlot cn _ => cn.val == o
  | .replyCap r => r.toNat == o
  | .auditTrail => false

theorem Capability.namesObjectWord_iff (c : Capability) (o : SeLe4n.ObjId) :
    c.namesObjectWord o.val = true ↔ c.namedObject = some o := by
  unfold Capability.namesObjectWord Capability.namedObject
  cases c.target with
  | object x => cases x; cases o; simp
  | cnodeSlot cn _ => cases cn; cases o; simp
  | replyCap r =>
    cases o
    simp only [SeLe4n.ReplyId.toObjId, SeLe4n.ObjId.ofNat, Option.some.injEq, SeLe4n.ObjId.mk.injEq,
      beq_iff_eq]
  | auditTrail => simp

namespace SystemState

/-- **Whether link `f` of slot `r` names a slot whose capability names the
object word `o`**: the link's object word, zero for no link, then the slot the
two words name, read in place. -/
@[inline] def linkNamesObject (st : SystemState) (r : SlotRef) (f : LinkField) (o : Nat) : Bool :=
  let c := st.slotLinkNodeWord r.cnode r.slot f
  c != 0 &&
    match st.slotCapAt ⟨SeLe4n.ObjId.ofNat (c - 1),
        SeLe4n.Slot.ofNat (st.slotLinkSlotWord r.cnode r.slot f - 1)⟩ with
    | some k => k.namesObjectWord o
    | none => false

/-- **No neighbour of `r` names the object word `o`**: neither its parent, its
first child, nor its previous or next sibling. -/
@[inline] def linksMissObject (st : SystemState) (r : SlotRef) (o : Nat) : Bool :=
  !st.linkNamesObject r .parent o && !st.linkNamesObject r .firstChild o &&
    !st.linkNamesObject r .prev o && !st.linkNamesObject r .next o

/-- **Whether the capability in slot `slot` of `cnode` is final** (seL4's
`isFinalCapability`): no slot its four derivation links name holds a capability
naming the same object.  An empty slot and the audit-trail capability, which
names nothing, are final.  It takes the slot's two words, so a caller builds no
address record.  Equal to `capFinalSpec` under the capability bundle. -/
def capIsFinal (st : SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) : Bool :=
  match st.slotCapAt ⟨cnode, slot⟩ with
  | none => true
  | some c =>
    match c.target with
    | .object x => st.linksMissObject ⟨cnode, slot⟩ x.val
    | .cnodeSlot cn _ => st.linksMissObject ⟨cnode, slot⟩ cn.val
    | .replyCap rp => st.linksMissObject ⟨cnode, slot⟩ rp.toNat
    | .auditTrail => true

/-- **The specification of finality**: no other slot holds a capability naming
the object the capability in slot `r` names. -/
def capFinalSpec (st : SystemState) (r : SlotRef) : Prop :=
  ∀ o, namesAt st.slotCapAt r o → ∀ r', r' ≠ r → ¬ namesAt st.slotCapAt r' o

theorem linkNamesObject_iff (st : SystemState) (r : SlotRef) (f : LinkField) (o : SeLe4n.ObjId) :
    st.linkNamesObject r f o.val = true ↔
      ∃ x, st.slotLinkAt r f = some x ∧ namesAt st.slotCapAt x o := by
  rw [slotLinkAt_eq_decode]
  unfold linkNamesObject decodeLink
  by_cases hc : st.slotLinkNodeWord r.cnode r.slot f = 0
  · simp [hc]
  · simp only [hc, if_false, Option.some.injEq, exists_eq_left']
    unfold namesAt
    cases h : st.slotCapAt ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord r.cnode r.slot f - 1),
        SeLe4n.Slot.ofNat (st.slotLinkSlotWord r.cnode r.slot f - 1)⟩ with
    | none => simp
    | some k => simp [Capability.namesObjectWord_iff, hc]

theorem linksMissObject_iff (st : SystemState) (r : SlotRef) (o : SeLe4n.ObjId) :
    st.linksMissObject r o.val = true ↔
      ∀ f x, st.slotLinkAt r f = some x → ¬ namesAt st.slotCapAt x o := by
  unfold linksMissObject
  simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, linkNamesObject_iff]
  constructor
  · rintro ⟨⟨⟨hp, hc⟩, hv⟩, hn⟩ f x hx hxo
    cases f
    · exact hp ⟨x, hx, hxo⟩
    · exact hc ⟨x, hx, hxo⟩
    · exact hn ⟨x, hx, hxo⟩
    · exact hv ⟨x, hx, hxo⟩
  · intro h
    exact ⟨⟨⟨fun ⟨x, hx, hxo⟩ => h _ x hx hxo, fun ⟨x, hx, hxo⟩ => h _ x hx hxo⟩,
      fun ⟨x, hx, hxo⟩ => h _ x hx hxo⟩, fun ⟨x, hx, hxo⟩ => h _ x hx hxo⟩

/-- **The reader is the link-level statement**: `capIsFinal` holds exactly when
no slot a link of `r` names holds a capability naming the object `r`'s does. -/
theorem capIsFinal_eq_true_iff_links (st : SystemState) (r : SlotRef) :
    st.capIsFinal r.cnode r.slot = true ↔ ∀ o, namesAt st.slotCapAt r o →
      ∀ f x, st.slotLinkAt r f = some x → ¬ namesAt st.slotCapAt x o := by
  unfold capIsFinal
  cases hc : st.slotCapAt r with
  | none => simp [namesAt, hc]
  | some c =>
    have hn : ∀ o, namesAt st.slotCapAt r o ↔ c.namedObject = some o := fun o => by
      simp [namesAt, hc]
    simp only [hn]
    unfold Capability.namedObject
    cases c.target with
    | object x => simpa using linksMissObject_iff st r x
    | cnodeSlot cn _ => simpa using linksMissObject_iff st r cn
    | replyCap rp => simpa using linksMissObject_iff st r rp.toObjId
    | auditTrail => simp

/-- A descent followed by a descent is a descent. -/
theorem desc_trans {ch : SlotRef → List SlotRef} {a b c : SlotRef} (h₁ : Desc ch a b)
    (h₂ : Desc ch b c) : Desc ch a c := by
  induction h₂ with
  | child hc => exact .trans h₁ hc
  | trans _ hc ih => exact .trans ih hc

/-- **A root's siblings are the whole root chain**: the parentless slots form at
most one chain. -/
theorem siblingsOf_of_mem_roots {L : LinkView} {cdt : CapDerivationTree} (hL : LinksAgree L cdt)
    (hOne : cdt.rootChains.length ≤ 1) {r : SlotRef} (hr : r ∈ cdt.rootChains.flatten) :
    cdt.siblingsOf r = cdt.rootChains.flatten := by
  rw [siblingsOf_of_root (hL.rootsParentless r hr)]
  unfold rootChain
  match hc : cdt.rootChains, hOne, hr with
  | [], _, hr => simp at hr
  | [C], _, hr =>
    have hnd := hL.rootsNodup
    rw [hc] at hnd
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hr ⊢
    exact SlotList.chainOf_of_mem hnd (List.mem_singleton_self C) hr
  | _ :: _ :: _, h, _ => simp at h

/-- **Up a descent, every slot names `o`**: when `m` lies below `q` and names
`o`, and `r` names `o` without lying below `q`, then `q` names `o` — a slot on
the way not naming it would put every slot naming `o`, `r` among them, below it
(`below`). -/
theorem names_up_of_shape {cdt : CapDerivationTree}
    {cap : SlotRef → Option Capability} {present : SeLe4n.ObjId → Prop}
    {ut : SeLe4n.ObjId → Option UntypedObject} {off : SlotRef → Prop}
    (hS : TreeShapeOver cdt cap present ut off) (hC : ∀ r, cdt.mentions r → cap r ≠ none)
    {r : SlotRef} {o : SeLe4n.ObjId} (hr : namesAt cap r o) {q m : SlotRef}
    (hm : Desc cdt.childrenOf q m) (hmo : namesAt cap m o) (hqr : ¬ Desc cdt.childrenOf q r) :
    namesAt cap q o := by
  have belowOf : ∀ {p c}, c ∈ cdt.childrenOf p → namesAt cap c o → ¬ namesAt cap p o →
      Desc cdt.childrenOf p r := fun hc hco hp =>
    (desc_childrenOf_iff cdt _ _).mpr
      (hS.below _ _ o hc hco (hC _ (mentions_of_mem_childrenOf hc).1) hp r hr)
  induction hm with
  | child hc => exact Classical.byContradiction fun hq' => hqr (belowOf hc hmo hq')
  | @trans m' _ hd' hc ih =>
    exact Classical.byContradiction fun hq' => by
      by_cases hm' : namesAt cap m' o
      · exact hq' (ih hm')
      · exact hqr (desc_trans hd' (belowOf hc hmo hm'))

/-- **Finality under the shape**: for a slot `r` naming `o`, no slot a link of
`r` names names `o` exactly when no other slot names `o` — when the links agree
with the tree, the tree has its shape, every slot the tree names is occupied and
the tree is acyclic.  The slots naming `o` are one preorder run, so a second one
puts a run slot right before or right after `r`; the slot after `r` is its first
child or next sibling, or lies outside the subtree of the parent `r` is the last
child of, which then names `o` (`below`); the slot before `r` is its parent or
lies at or below its previous sibling, which then names `o` (`below`, up the
descent). -/
theorem linksFinal_iff_of_shape {L : LinkView} {cdt : CapDerivationTree}
    {cap : SlotRef → Option Capability} {present : SeLe4n.ObjId → Prop}
    {ut : SeLe4n.ObjId → Option UntypedObject} {off : SlotRef → Prop}
    (hL : LinksAgree L cdt) (hS : TreeShapeOver cdt cap present ut off)
    (hC : ∀ r, cdt.mentions r → cap r ≠ none) (hWF : cdt.edgeWellFounded)
    {r : SlotRef} {o : SeLe4n.ObjId} (hr : namesAt cap r o) :
    (∀ f x, L r f = some x → ¬ namesAt cap x o) ↔ ∀ r', r' ≠ r → ¬ namesAt cap r' o := by
  have capOf : ∀ {x}, namesAt cap x o → cap x ≠ none := fun ⟨c, hc, _⟩ => by simp [hc]
  constructor
  · intro hN r' hne hr'
    obtain ⟨P, hP⟩ := hS.ordered
    have memP : ∀ {x}, namesAt cap x o → x ∈ P := fun hx => hP.complete _ (hS.inTree _ (capOf hx))
    have descOf := fun {a b : SlotRef} (h : CdtChildReachable cdt a b) =>
      (desc_childrenOf_iff cdt a b).mpr h
    -- a parent not naming `o` puts every slot naming `o` below it
    have belowOf : ∀ {p c}, c ∈ cdt.childrenOf p → namesAt cap c o → ¬ namesAt cap p o →
        ∀ x, namesAt cap x o → Desc cdt.childrenOf p x := fun hc hco hp x hx =>
      descOf (hS.below _ _ o hc hco (hC _ (mentions_of_mem_childrenOf hc).1) hp x hx)
    have hSib : ∀ {M}, (M = cdt.rootChains.flatten ∨ ∃ y ∈ P, M = cdt.childrenOf y) → r ∈ M →
        cdt.siblingsOf r = M := fun hM hrM => by
      rcases hM with rfl | ⟨y, -, rfl⟩
      · exact siblingsOf_of_mem_roots hL hP.oneChain hrM
      · exact hL.siblingsOf_of_mem_children hrM
    rcases (hS.sameObjectContiguous P hP o).neighbour (memP hr) hr (memP hr') hr' hne with
      ⟨X, x, Y, hPe, hx⟩ | ⟨X, x, Y, hPe, hx⟩
    · rcases hP.forest.pred_cases hP.nodup hPe with ⟨hrx, -⟩ | ⟨M, hM, q, hq, hqx, hqr⟩
      · exact hN .parent x (by rw [hL.parent]; exact (mem_childrenOf_iff_parentOf hL.childrenUnique x r).mp hrx) hx
      · have hrM : r ∈ M := Classical.byContradiction fun hn => by
          rw [SlotList.predIn_of_not_mem hn] at hq; cases hq
        have hLq : L r .prev = some q := by rw [hL.prev, hSib hM hrM]; exact hq
        refine hN .prev q hLq ?_
        rcases hqx with rfl | hd
        · exact hx
        · exact names_up_of_shape hS hC hr hd hx hqr
    · rcases hP.forest.succ_cases hP.nodup hPe with hh | ⟨-, hs | ⟨y, -, hry, hs | ⟨-, hnd⟩⟩⟩
      · exact hN .firstChild x (by rw [hL.firstChild]; exact hh) hx
      · have hrM : r ∈ cdt.rootChains.flatten := Classical.byContradiction fun hn => by
          rw [SlotList.succIn_of_not_mem hn] at hs; cases hs
        exact hN .next x (by rw [hL.next, hSib (.inl rfl) hrM]; exact hs) hx
      · exact hN .next x (by rw [hL.next, hL.siblingsOf_of_mem_children hry]; exact hs) hx
      · refine hN .parent y (by rw [hL.parent]; exact (mem_childrenOf_iff_parentOf hL.childrenUnique y r).mp hry) ?_
        exact Classical.byContradiction fun hy => hnd (belowOf hry hr hy x hx)
  · intro hN f x hx
    refine hN x ?_
    rintro rfl
    cases f with
    | parent => exact hL.parentOf_ne_self_of_wf hWF x (by rw [← hL.parent]; exact hx)
    | firstChild =>
      rw [hL.firstChild] at hx
      obtain ⟨e, he, hp, hc⟩ := childrenOf_to_edge cdt x x (List.mem_of_mem_head? hx)
      exact edgeWellFounded_no_self_edge hWF he (hp.trans hc.symm)
    | next => exact hL.next_ne_self x hx
    | prev => exact hL.prev_ne_self x hx

/-- **The reader is the specification under the shape**: `capIsFinal` holds
exactly when no other slot names the object `r`'s capability names. -/
theorem capIsFinal_iff_of_shape {st : SystemState} {present : SeLe4n.ObjId → Prop}
    {ut : SeLe4n.ObjId → Option UntypedObject} {off : SlotRef → Prop}
    (hL : LinksAgree st.slotLinkAt st.cdt) (hS : TreeShapeOver st.cdt st.slotCapAt present ut off)
    (hC : ∀ r, st.cdt.mentions r → st.slotCapAt r ≠ none) (hWF : st.cdt.edgeWellFounded)
    (r : SlotRef) : st.capIsFinal r.cnode r.slot = true ↔ st.capFinalSpec r := by
  rw [capIsFinal_eq_true_iff_links]
  exact forall_congr' fun o => imp_congr_right fun hr => linksFinal_iff_of_shape hL hS hC hWF hr

end SystemState

end SeLe4n.Model
