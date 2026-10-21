-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.Structures

/-!
# Derivation links (WS-ZA ZA5.3 part 4)

Each slot holds the slot addresses of its parent, its first child and its next
and previous siblings, as seL4's `cte_t` holds its mapping-database node.  This
module states, over any link reading `L : SlotRef → LinkField → Option SlotRef`,
what it means for the links to encode a derivation tree (`LinksAgree`), proves
that the executable sibling walk reads a node's children, and proves that each
tree operation's link writes keep the agreement.  A CNode holds its slots' links
as words (`CNode.linkAt`, `CNode.setLinkWords`); the state-level reading
(`SystemState.slotLinkAt`) instantiates `L`.
-/

namespace SeLe4n.Model

/-- The four derivation links a slot holds. -/
inductive LinkField where
  | parent | firstChild | next | prev
  deriving Repr, DecidableEq

/-- A reading of every slot's links. -/
abbrev LinkView := SlotRef → LinkField → Option SlotRef

namespace LinkView

/-- `L` with link `f` of slot `r` replaced by `v`. -/
def set (L : LinkView) (r : SlotRef) (f : LinkField) (v : Option SlotRef) : LinkView :=
  fun r' f' => if r' = r ∧ f' = f then v else L r' f'

@[simp] theorem set_same (L : LinkView) (r : SlotRef) (f : LinkField) (v : Option SlotRef) :
    L.set r f v r f = v := by simp [set]

theorem set_ne (L : LinkView) {r r' : SlotRef} {f f' : LinkField} (v : Option SlotRef)
    (h : r' ≠ r ∨ f' ≠ f) : L.set r f v r' f' = L r' f' := by
  unfold set; rw [if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h <;> contradiction

theorem set_ne_slot (L : LinkView) {r r' : SlotRef} (f f' : LinkField) (v : Option SlotRef)
    (h : r' ≠ r) : L.set r f v r' f' = L r' f' := L.set_ne v (.inl h)

theorem set_ne_field (L : LinkView) (r r' : SlotRef) {f f' : LinkField} (v : Option SlotRef)
    (h : f' ≠ f) : L.set r f v r' f' = L r' f' := L.set_ne v (.inr h)

end LinkView

namespace LinkField

/-- The word offset of a link within its slot's `slotLinkWords` words. -/
@[inline] def offset : LinkField → Nat
  | .parent => 0 | .firstChild => 2 | .next => 4 | .prev => 6

end LinkField

/-- The word a link holds for its target's CNode: 0 for no target, else the
CNode's id plus one. -/
@[inline] def linkNodeCode : Option SlotRef → Nat
  | none => 0
  | some r => r.cnode.toNat + 1

/-- The word a link holds for its target's slot: 0 for no target, else the slot
index plus one. -/
@[inline] def linkSlotCode : Option SlotRef → Nat
  | none => 0
  | some r => r.slot.toNat + 1

/-- The link two words hold: none when the CNode word is 0, else the slot whose
CNode and slot are the words less one. -/
def decodeLink (c w : Nat) : Option SlotRef :=
  if c = 0 then none else some ⟨SeLe4n.ObjId.ofNat (c - 1), SeLe4n.Slot.ofNat (w - 1)⟩

@[simp] theorem decodeLink_codes (v : Option SlotRef) :
    decodeLink (linkNodeCode v) (linkSlotCode v) = v := by
  cases v with
  | none => rfl
  | some r => simp [decodeLink, linkNodeCode, linkSlotCode, SeLe4n.ObjId.ofNat_toNat,
      SeLe4n.Slot.ofNat_toNat]

namespace CNode

/-- The index of the first of link `f`'s two words for slot `s`. -/
@[inline] def linkBase (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  slotLinkWords * s.toNat + f.offset

/-- The CNode word of link `f` of slot `s` (0 when it has no target). -/
@[inline] def linkNodeWord (node : CNode) (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  node.links.getD (linkBase s f) 0

/-- The slot word of link `f` of slot `s`. -/
@[inline] def linkSlotWord (node : CNode) (s : SeLe4n.Slot) (f : LinkField) : Nat :=
  node.links.getD (linkBase s f + 1) 0

/-- Link `f` of slot `s`, decoded from its two words (`decodeLink`). -/
def linkAt (node : CNode) (s : SeLe4n.Slot) (f : LinkField) : Option SlotRef :=
  decodeLink (node.linkNodeWord s f) (node.linkSlotWord s f)

/-- Write link `f` of slot `s` in place, as its two words `c` and `w`. -/
@[inline] def setLinkWords (node : CNode) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) : CNode :=
  { node with
    links := (node.links.setIfInBounds (linkBase s f) c).setIfInBounds (linkBase s f + 1) w
    links_size := by simp [node.links_size] }

@[simp] theorem lookup_setLinkWords (node : CNode) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat)
    (s' : SeLe4n.Slot) : (node.setLinkWords s f c w).lookup s' = node.lookup s' := rfl

@[simp] theorem radixWidth_setLinkWords (node : CNode) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    (node.setLinkWords s f c w).radixWidth = node.radixWidth := rfl

/-- **Every link word is 0**: the CNode holds no derivation link.  The boot check
reads it (a boot CNode derives nothing), and so does every fresh CNode. -/
def linksClear (node : CNode) : Bool := node.links.toList.all (· == 0)

theorem linkAt_of_linksClear {node : CNode} (h : node.linksClear = true)
    (s : SeLe4n.Slot) (f : LinkField) : node.linkAt s f = none := by
  have hz : node.linkNodeWord s f = 0 := by
    unfold linkNodeWord
    rw [Array.getD_eq_getD_getElem?]
    cases hi : node.links[linkBase s f]? with
    | none => rfl
    | some v =>
      have hm : v ∈ node.links := Array.mem_of_getElem? hi
      have := (List.all_eq_true.mp h) v (Array.mem_def.mp hm)
      simpa using this
  unfold linkAt decodeLink; rw [hz]; rfl

theorem linkBase_ne {s s' : SeLe4n.Slot} {f f' : LinkField} (h : ¬ (s' = s ∧ f' = f)) :
    linkBase s f ≠ linkBase s' f' ∧ linkBase s f + 1 ≠ linkBase s' f' ∧
      linkBase s f ≠ linkBase s' f' + 1 ∧ linkBase s f + 1 ≠ linkBase s' f' + 1 := by
  have key : s'.toNat ≠ s.toNat ∨ f' ≠ f := by
    by_cases e : s'.toNat = s.toNat
    · exact .inr fun hf => h ⟨SeLe4n.Slot.ext e, hf⟩
    · exact .inl e
  unfold linkBase slotLinkWords
  cases f <;> cases f' <;>
    simp only [LinkField.offset, ne_eq, not_true_eq_false, or_false, reduceCtorEq,
      not_false_eq_true, or_true] at key ⊢ <;> omega

/-- **Writing a link's words** sets that link, for a slot inside the CNode, and
leaves every other link. -/
theorem linkAt_setLinkWords (node : CNode) {s : SeLe4n.Slot} (hs : s.toNat < 2 ^ node.radixWidth)
    (f : LinkField) (c w : Nat) (s' : SeLe4n.Slot) (f' : LinkField) :
    (node.setLinkWords s f c w).linkAt s' f' =
      if s' = s ∧ f' = f then decodeLink c w else node.linkAt s' f' := by
  have hb : linkBase s f + 1 < node.links.size := by
    rw [node.links_size]
    have h1 : slotLinkWords * (s.toNat + 1) ≤ slotLinkWords * 2 ^ node.radixWidth :=
      Nat.mul_le_mul_left _ hs
    unfold linkBase slotLinkWords at *
    cases f <;> simp only [LinkField.offset] <;> omega
  unfold linkAt linkNodeWord linkSlotWord setLinkWords
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases he : s' = s ∧ f' = f
  · obtain ⟨rfl, rfl⟩ := he
    have hne : linkBase s' f' + 1 ≠ linkBase s' f' := Nat.succ_ne_self _
    simp only [hb, Nat.lt_of_succ_lt hb, if_true, hne, if_false, Option.getD_some, and_self]
  · have ⟨n1, n2, n3, n4⟩ := linkBase_ne he
    simp only [n1, n2, n3, n4, if_false, he]

end CNode
/-! ### Neighbours in a list -/

namespace SlotList

/-- The element after `w` in `l`. -/
def succIn : List SlotRef → SlotRef → Option SlotRef
  | [], _ => none
  | a :: l, w => if a = w then l.head? else succIn l w

/-- The element before `w` in `l`, given the one before `l` (`prev`). -/
def predAux : Option SlotRef → List SlotRef → SlotRef → Option SlotRef
  | _, [], _ => none
  | prev, a :: l, w => if a = w then prev else predAux (some a) l w

/-- The element before `w` in `l`. -/
def predIn (l : List SlotRef) (w : SlotRef) : Option SlotRef := predAux none l w

theorem succIn_of_not_mem : ∀ {l : List SlotRef} {w : SlotRef}, w ∉ l → succIn l w = none
  | [], _, _ => rfl
  | a :: l, w, h => by
    have ha : a ≠ w := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [succIn, if_neg ha]
    exact succIn_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))

theorem predAux_of_not_mem : ∀ {l : List SlotRef} {prev : Option SlotRef} {w : SlotRef},
    w ∉ l → predAux prev l w = none
  | [], _, _, _ => rfl
  | a :: l, prev, w, h => by
    have ha : a ≠ w := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [predAux, if_neg ha]
    exact predAux_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))

theorem predIn_of_not_mem {l : List SlotRef} {w : SlotRef} (h : w ∉ l) : predIn l w = none :=
  predAux_of_not_mem h

/-- Past the head, the element before `w` does not depend on what precedes the list. -/
theorem predAux_irrel : ∀ {l : List SlotRef} {prev prev' : Option SlotRef} {w : SlotRef},
    l.head? ≠ some w → predAux prev l w = predAux prev' l w
  | [], _, _, _, _ => rfl
  | a :: l, prev, prev', w, h => by
    have ha : a ≠ w := fun e => h (by simp [e])
    simp only [predAux, if_neg ha]

theorem predIn_cons (c : SlotRef) (l : List SlotRef) (w : SlotRef) :
    predIn (c :: l) w = if c = w then none else if l.head? = some w then some c else predIn l w := by
  unfold predIn
  simp only [predAux]
  by_cases hc : c = w
  · simp [hc]
  · rw [if_neg hc, if_neg hc]
    by_cases hh : l.head? = some w
    · rw [if_pos hh]
      cases l with
      | nil => cases hh
      | cons a l => simp at hh; subst hh; simp [predAux]
    · rw [if_neg hh]; exact predAux_irrel hh

theorem succIn_cons (c : SlotRef) (l : List SlotRef) (w : SlotRef) :
    succIn (c :: l) w = if c = w then l.head? else succIn l w := rfl

/-- The list without `n`. -/
abbrev drop (l : List SlotRef) (n : SlotRef) : List SlotRef := l.filter (fun x => decide (x ≠ n))

theorem drop_cons (a : SlotRef) (l : List SlotRef) (n : SlotRef) :
    drop (a :: l) n = if a = n then drop l n else a :: drop l n := by
  by_cases h : a = n <;> simp [drop, h]

theorem drop_of_not_mem : ∀ {l : List SlotRef} {n : SlotRef}, n ∉ l → drop l n = l
  | [], _, _ => rfl
  | a :: l, n, h => by
    have ha : a ≠ n := fun e => h (e ▸ List.mem_cons_self ..)
    rw [drop_cons, if_neg ha, drop_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))]

/-- Unlinking `n` from a duplicate-free list: the head becomes `n`'s successor
when `n` was the head. -/
theorem head_drop {l : List SlotRef} {n : SlotRef} (hnd : l.Nodup) :
    (drop l n).head? = if l.head? = some n then succIn l n else l.head? := by
  cases l with
  | nil => rfl
  | cons a l =>
    rw [drop_cons]
    by_cases ha : a = n
    · subst ha
      simp only [if_true, List.head?_cons, succIn]
      rw [drop_of_not_mem (List.nodup_cons.mp hnd).1]
    · simp [ha]

theorem succIn_mem : ∀ {l : List SlotRef} {w x : SlotRef}, succIn l w = some x → x ∈ l
  | [], _, _, h => by cases h
  | a :: l, w, x, h => by
    simp only [succIn] at h
    split at h
    · cases l with
      | nil => cases h
      | cons b l => simp at h; subst h; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (succIn_mem h)

/-- Unlinking `n`: the element whose successor was `n` takes `n`'s successor. -/
theorem succIn_drop : ∀ {l : List SlotRef} {n w : SlotRef}, l.Nodup → w ≠ n →
    succIn (drop l n) w = if succIn l w = some n then succIn l n else succIn l w
  | [], _, _, _, _ => rfl
  | a :: l, n, w, hnd, hw => by
    have ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    rw [drop_cons]
    by_cases ha : a = n
    · subst ha
      have hwl : succIn (a :: l) w = succIn l w := by simp [succIn, Ne.symm hw]
      rw [if_pos rfl, hwl, succIn_drop hnd' hw]
      simp only [succIn]
      by_cases hs : succIn l w = some a
      · exact absurd (succIn_mem hs) haL
      · rw [if_neg hs, if_neg hs]
    · rw [if_neg ha]
      show (if a = w then (drop l n).head? else succIn (drop l n) w) =
        if (if a = w then l.head? else succIn l w) = some n then
          (if a = n then l.head? else succIn l n)
        else (if a = w then l.head? else succIn l w)
      rw [if_neg ha]
      by_cases haw : a = w
      · simp only [if_pos haw]; exact head_drop hnd'
      · simp only [if_neg haw]; exact succIn_drop hnd' hw

theorem predAux_mem : ∀ {l : List SlotRef} {prev : Option SlotRef} {w x : SlotRef},
    predAux prev l w = some x → some x = prev ∨ x ∈ l
  | [], _, _, _, h => by cases h
  | a :: l, prev, w, x, h => by
    simp only [predAux] at h
    split at h
    · exact .inl h.symm
    · rcases predAux_mem h with h' | h'
      · cases h'; exact .inr (List.mem_cons_self ..)
      · exact .inr (List.mem_cons_of_mem _ h')

private theorem predAux_drop : ∀ {l : List SlotRef} {prev : Option SlotRef} {n w : SlotRef},
    l.Nodup → w ≠ n → prev ≠ some n →
    predAux prev (drop l n) w =
      if predAux prev l w = some n then predAux prev l n else predAux prev l w
  | [], _, _, _, _, _, _ => rfl
  | a :: l, prev, n, w, hnd, hw, hp => by
    have ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    rw [drop_cons]
    by_cases ha : a = n
    · subst ha
      rw [if_pos rfl, drop_of_not_mem haL]
      simp only [predAux, if_neg (Ne.symm hw)]
      by_cases hh : l.head? = some w
      · cases l with
        | nil => cases hh
        | cons b l =>
          simp at hh; subst hh
          simp [predAux]
      · have : predAux prev l w ≠ some a := fun e => by
          rw [predAux_irrel (prev' := none) hh] at e
          rcases predAux_mem e with e | e
          · cases e
          · exact haL e
        rw [predAux_irrel (prev := some a) (prev' := prev) hh, if_neg this]
    · rw [if_neg ha]
      simp only [predAux]
      by_cases haw : a = w
      · simp only [if_pos haw, if_neg ha]
        rw [if_neg hp]
      · simp only [if_neg haw, if_neg ha]
        exact predAux_drop hnd' hw (fun e => ha (Option.some.inj e))

/-- Unlinking `n`: the element whose predecessor was `n` takes `n`'s predecessor. -/
theorem predIn_drop {l : List SlotRef} {n w : SlotRef} (hnd : l.Nodup) (hw : w ≠ n) :
    predIn (drop l n) w = if predIn l w = some n then predIn l n else predIn l w :=
  predAux_drop hnd hw (by simp)

theorem predIn_mem {l : List SlotRef} {w x : SlotRef} (h : predIn l w = some x) : x ∈ l := by
  rcases predAux_mem h with h | h
  · cases h
  · exact h

private theorem succIn_ne_head : ∀ {h : SlotRef} {t : List SlotRef} {a : SlotRef},
    (h :: t).Nodup → succIn (h :: t) a ≠ some h := by
  intro h t a hnd e
  have ⟨hT, _⟩ := List.nodup_cons.mp hnd
  rw [succIn_cons] at e
  split at e
  · exact hT (List.mem_of_mem_head? e)
  · exact hT (succIn_mem e)

/-- In a duplicate-free list, `b` follows `a` exactly when `a` precedes `b`. -/
theorem succIn_eq_iff_predIn : ∀ {l : List SlotRef} {a b : SlotRef}, l.Nodup →
    (succIn l a = some b ↔ predIn l b = some a)
  | [], _, _, _ => by simp [succIn, predIn, predAux]
  | c :: l, a, b, hnd => by
    have ⟨hcL, hnd'⟩ := List.nodup_cons.mp hnd
    rw [succIn_cons, predIn_cons]
    by_cases hca : c = a
    · subst hca
      rw [if_pos rfl]
      by_cases hh : l.head? = some b
      · have hcb : c ≠ b := fun e => hcL (e ▸ List.mem_of_mem_head? hh)
        rw [if_neg hcb, if_pos hh]; simp [hh]
      · rw [if_neg hh]
        by_cases hcb : c = b
        · rw [if_pos hcb]
          exact ⟨fun e => absurd e hh, fun e => by cases e⟩
        · rw [if_neg hcb]
          exact ⟨fun e => absurd e hh, fun e => absurd (predIn_mem e) hcL⟩
    · rw [if_neg hca]
      by_cases hcb : c = b
      · subst hcb
        rw [if_pos rfl]
        exact ⟨fun e => absurd (succIn_mem e) hcL, fun e => by cases e⟩
      · rw [if_neg hcb]
        by_cases hh : l.head? = some b
        · rw [if_pos hh]
          constructor
          · intro e
            cases l with
            | nil => cases hh
            | cons d l =>
              simp at hh; subst hh
              exact absurd e (succIn_ne_head hnd')
          · intro e; exact absurd (Option.some.inj e) hca
        · rw [if_neg hh]; exact succIn_eq_iff_predIn hnd'

private theorem predAux_some_ne_none : ∀ {l : List SlotRef} {x n : SlotRef},
    n ∈ l → predAux (some x) l n ≠ none
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: l, x, n, h => by
    simp only [predAux]
    split
    · simp
    · exact predAux_some_ne_none ((List.mem_cons.mp h).resolve_left (Ne.symm ‹_›))

/-- A member has no predecessor exactly when it is the head. -/
theorem predIn_eq_none_iff {l : List SlotRef} {n : SlotRef} (h : n ∈ l) :
    predIn l n = none ↔ l.head? = some n := by
  cases l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l =>
    rw [predIn_cons]
    by_cases ha : a = n
    · simp [ha]
    · rw [if_neg ha]
      have hl : n ∈ l := (List.mem_cons.mp h).resolve_left (Ne.symm ha)
      simp only [List.head?_cons, Option.some.injEq, ha, iff_false]
      split
      · simp
      · unfold predIn
        rw [← predAux_irrel (prev := some a) ‹_›]
        exact predAux_some_ne_none hl

end SlotList
namespace CapDerivationTree

/-- Each slot is the child of at most one edge: a slot holds one parent link. -/
def childrenUnique (cdt : CapDerivationTree) : Prop :=
  (cdt.edges.map (·.child)).Nodup

end CapDerivationTree

namespace CapDerivationTree

private theorem nodup_map_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, hf => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hxa | hxl <;> rcases List.mem_cons.mp hy with hya | hyl
    · exact hxa.trans hya.symm
    · subst hxa; exact (h.1 (List.mem_map.mpr ⟨y, hyl, hf.symm⟩)).elim
    · subst hya; exact (h.1 (List.mem_map.mpr ⟨x, hxl, hf⟩)).elim
    · exact nodup_map_inj h.2 hxl hyl hf

theorem parentOf_eq_none_iff (cdt : CapDerivationTree) (r : SlotRef) :
    cdt.parentOf r = none ↔ ∀ e ∈ cdt.edges, e.child ≠ r := by
  unfold parentOf
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  simp [CapDerivationEdge.isChildOf]

theorem parentOf_of_edge {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    {e : CapDerivationEdge} (he : e ∈ cdt.edges) : cdt.parentOf e.child = some e.parent := by
  unfold parentOf
  cases hF : cdt.edges.find? (·.isChildOf e.child) with
  | none =>
    rw [List.find?_eq_none] at hF
    exact absurd (by simp [CapDerivationEdge.isChildOf]) (hF e he)
  | some e' =>
    have hm := List.mem_of_find?_eq_some hF
    have hc : e'.child = e.child := by
      have := List.find?_some hF; simpa [CapDerivationEdge.isChildOf] using this
    simp only [Option.map_some]
    congr 1
    -- two edges with one child are one edge
    unfold childrenUnique at hU
    rw [nodup_map_inj hU hm he hc]

theorem mem_childrenOf_iff_parentOf {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (p c : SlotRef) : c ∈ cdt.childrenOf p ↔ cdt.parentOf c = some p := by
  rw [mem_childrenOf]
  constructor
  · rintro ⟨e, he, rfl, rfl⟩; exact parentOf_of_edge hU he
  · intro h
    unfold parentOf at h
    cases hF : cdt.edges.find? (·.isChildOf c) with
    | none => rw [hF] at h; cases h
    | some e =>
      rw [hF] at h; cases h
      refine ⟨e, List.mem_of_find?_eq_some hF, rfl, ?_⟩
      have := List.find?_some hF; simpa [CapDerivationEdge.isChildOf] using this

end CapDerivationTree

namespace CapDerivationTree

theorem childrenOf_nodup {cdt : CapDerivationTree} (hU : cdt.childrenUnique) (p : SlotRef) :
    (cdt.childrenOf p).Nodup := by
  unfold childrenOf
  exact hU.sublist ((List.filter_sublist).map _)

theorem parentOf_addEdge (cdt : CapDerivationTree) (p c r : SlotRef) (op : DerivationOp) :
    (cdt.addEdge p c op).parentOf r = if r = c then some p else cdt.parentOf r := by
  unfold parentOf; rw [addEdge_edges]
  by_cases h : r = c
  · subst h; simp [CapDerivationEdge.isChildOf]
  · have h' : ¬ (c = r) := fun e => h e.symm
    simp [CapDerivationEdge.isChildOf, h, h']

theorem childrenOf_addEdge (cdt : CapDerivationTree) (p c q : SlotRef) (op : DerivationOp) :
    (cdt.addEdge p c op).childrenOf q = if q = p then c :: cdt.childrenOf q else cdt.childrenOf q := by
  unfold childrenOf; rw [addEdge_edges]
  by_cases h : q = p
  · subst h; simp [CapDerivationEdge.isParentOf]
  · have h' : ¬ (p = q) := fun e => h e.symm
    simp [CapDerivationEdge.isParentOf, h, h']

theorem parentOf_of_not_mentions {cdt : CapDerivationTree} {c : SlotRef} (h : ¬ cdt.mentions c) :
    cdt.parentOf c = none :=
  (parentOf_eq_none_iff cdt c).mpr fun e he hc => h ⟨e, he, .inr hc⟩

theorem childrenOf_of_not_mentions {cdt : CapDerivationTree} {c : SlotRef} (h : ¬ cdt.mentions c) :
    cdt.childrenOf c = [] := by
  rcases hL : cdt.childrenOf c with _ | ⟨x, l⟩
  · rfl
  · obtain ⟨e, he, hp, -⟩ := childrenOf_to_edge cdt c x (hL ▸ List.mem_cons_self ..)
    exact absurd ⟨e, he, .inl hp⟩ h

theorem not_mem_childrenOf_of_not_mentions {cdt : CapDerivationTree} {c : SlotRef}
    (h : ¬ cdt.mentions c) (q : SlotRef) : c ∉ cdt.childrenOf q := fun hm => by
  obtain ⟨e, he, -, hc⟩ := childrenOf_to_edge cdt q c hm
  exact h ⟨e, he, .inr hc⟩

end CapDerivationTree


namespace CapDerivationTree

theorem childrenUnique_sublist {cdt cdt' : CapDerivationTree} (h : cdt.childrenUnique)
    (hs : cdt'.edges.Sublist cdt.edges) : cdt'.childrenUnique :=
  h.sublist (hs.map _)

/-- Under unique children, the parent read is the edge relation. -/
theorem parentOf_eq_some_iff {cdt : CapDerivationTree} (hU : cdt.childrenUnique) (p r : SlotRef) :
    cdt.parentOf r = some p ↔ ∃ e ∈ cdt.edges, e.parent = p ∧ e.child = r := by
  rw [← mem_childrenOf_iff_parentOf hU, mem_childrenOf]

theorem removeNode_sublist (cdt : CapDerivationTree) (n : SlotRef) :
    (cdt.removeNode n).edges.Sublist cdt.edges := by
  rw [removeNode_edges]; exact List.filter_sublist

theorem parentOf_removeNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique) (n r : SlotRef) :
    (cdt.removeNode n).parentOf r =
      if r = n ∨ cdt.parentOf r = some n then none else cdt.parentOf r := by
  have hU' := childrenUnique_sublist hU (removeNode_sublist cdt n)
  split
  · next hc =>
    rw [parentOf_eq_none_iff]
    intro e he hec
    simp only [removeNode_edges, List.mem_filter, CapDerivationEdge.isParentOf,
      CapDerivationEdge.isChildOf, decide_eq_true_eq] at he
    obtain ⟨he, hp, hcn⟩ := he
    rcases hc with rfl | hc
    · exact hcn hec
    · have := (parentOf_eq_some_iff hU _ _).mpr ⟨e, he, rfl, hec⟩
      rw [hc] at this; exact hp (Option.some.inj this).symm
  · next hc =>
    have hc1 : r ≠ n := fun h => hc (.inl h)
    have hc2 : cdt.parentOf r ≠ some n := fun h => hc (.inr h)
    cases hP : cdt.parentOf r with
    | none =>
      rw [parentOf_eq_none_iff] at hP ⊢
      intro e he; rw [removeNode_edges] at he; exact hP e (List.mem_filter.mp he).1
    | some p =>
      obtain ⟨e, he, hep, hec⟩ := (parentOf_eq_some_iff hU p r).mp hP
      refine (parentOf_eq_some_iff hU' p r).mpr ⟨e, ?_, hep, hec⟩
      simp only [removeNode_edges, List.mem_filter, CapDerivationEdge.isParentOf,
        CapDerivationEdge.isChildOf, decide_eq_true_eq]
      refine ⟨he, fun h => hc2 (h ▸ hep ▸ hP), fun h => hc1 (hec ▸ h)⟩

theorem childrenOf_removeNode (cdt : CapDerivationTree) (n q : SlotRef) :
    (cdt.removeNode n).childrenOf q = if q = n then [] else SlotList.drop (cdt.childrenOf q) n := by
  unfold childrenOf SlotList.drop
  rw [removeNode_edges]
  rw [List.filter_filter]
  split
  · next hq =>
    subst hq
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    · intro e _; simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf]
      intro h; exact absurd h
  · next hq =>
    rw [List.filter_map]
    congr 1
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    simp only [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf, Function.comp]
    by_cases hp : e.parent = q
    · simp [hp, hq]
    · simp [hp]

end CapDerivationTree

/-- **The links encode the tree.**  Each slot's parent link is its parent in the
tree, its first-child link the newest of its children, and its next and previous
links its neighbours among its parent's children (newest first); a slot that is
no one's child has neither, and no slot is the child of two edges.  A slot the
tree does not name therefore holds no link at all. -/
structure LinksAgree (L : LinkView) (cdt : CapDerivationTree) : Prop where
  childrenUnique : cdt.childrenUnique
  parent : ∀ r, L r .parent = cdt.parentOf r
  firstChild : ∀ p, L p .firstChild = (cdt.childrenOf p).head?
  next : ∀ r, L r .next = (cdt.parentOf r).bind fun p => SlotList.succIn (cdt.childrenOf p) r
  prev : ∀ r, L r .prev = (cdt.parentOf r).bind fun p => SlotList.predIn (cdt.childrenOf p) r

/-- The agreement reads the tree only through its edges. -/
theorem LinksAgree.of_edges_eq {L : LinkView} {cdt cdt' : CapDerivationTree}
    (hE : cdt.edges = cdt'.edges) (h : LinksAgree L cdt) : LinksAgree L cdt' := by
  have hP : ∀ r, cdt'.parentOf r = cdt.parentOf r := fun r => by
    unfold CapDerivationTree.parentOf; rw [hE]
  have hC : ∀ r, cdt'.childrenOf r = cdt.childrenOf r := fun r => by
    unfold CapDerivationTree.childrenOf; rw [hE]
  have hU : cdt'.childrenUnique := by
    have := h.childrenUnique; unfold CapDerivationTree.childrenUnique at this ⊢; rwa [← hE]
  exact ⟨hU, fun r => by rw [hP, h.parent], fun p => by rw [hC, h.firstChild],
    fun r => by simp only [hP, hC, h.next], fun r => by simp only [hP, hC, h.prev]⟩

namespace LinkView

/-- The slots reached from `cur` along next links, at most `fuel` of them: the
executable reading of a sibling chain. -/
def walk (L : LinkView) : Nat → Option SlotRef → List SlotRef
  | 0, _ => []
  | _ + 1, none => []
  | n + 1, some w => w :: walk L n (L w .next)

/-- The walk reads only the next links of the slots it visits. -/
theorem walk_congr {L L' : LinkView} :
    ∀ (n : Nat) (a : Option SlotRef), (∀ w ∈ walk L n a, L' w .next = L w .next) →
      walk L' n a = walk L n a
  | 0, _, _ => rfl
  | _ + 1, none, _ => rfl
  | n + 1, some w, h => by
    simp only [walk] at h ⊢
    rw [h w (List.mem_cons_self ..),
      walk_congr n _ (fun v hv => h v (List.mem_cons_of_mem _ hv))]

/-- Each slot the walk visits is its start or some slot's next link. -/
theorem mem_walk {L : LinkView} :
    ∀ {n : Nat} {a : Option SlotRef} {w : SlotRef}, w ∈ walk L n a →
      a = some w ∨ ∃ v, L v .next = some w
  | 0, _, _, h => by cases h
  | _ + 1, none, _, h => by cases h
  | n + 1, some v, w, h => by
    simp only [walk, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl rfl
    · rcases mem_walk h with h | h
      · exact .inr ⟨v, h⟩
      · exact .inr h

/-- Following next links from a duplicate-free list's head reads the list, when
each element's next link is its successor and the fuel covers the list. -/
theorem walk_of_succ {L : LinkView} :
    ∀ {l : List SlotRef} {n : Nat}, l.Nodup → (∀ w ∈ l, L w .next = SlotList.succIn l w) →
      l.length ≤ n → walk L n l.head? = l
  | [], n, _, _, _ => by cases n <;> rfl
  | a :: l, n, hnd, hs, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.head?_cons, walk]
    have ha := hs a (List.mem_cons_self ..)
    simp only [SlotList.succIn_cons, if_true] at ha
    rw [ha]
    refine congrArg (a :: ·) (walk_of_succ hnd' (fun w hw => ?_) (by simp at hn; omega))
    have := hs w (List.mem_cons_of_mem _ hw)
    have haw : ¬ a = w := fun e => haL (e ▸ hw)
    rw [SlotList.succIn_cons, if_neg haw] at this
    exact this

end LinkView

/-- **The children walk reads the tree's children**, with any fuel at least
their number (the tree's edge count is one). -/
theorem LinksAgree.walk_children {L : LinkView} {cdt : CapDerivationTree} (h : LinksAgree L cdt)
    (p : SlotRef) {n : Nat} (hn : (cdt.childrenOf p).length ≤ n) :
    L.walk n (L p .firstChild) = cdt.childrenOf p := by
  rw [h.firstChild]
  refine LinkView.walk_of_succ (CapDerivationTree.childrenOf_nodup h.childrenUnique p)
    (fun w hw => ?_) hn
  rw [h.next, (CapDerivationTree.mem_childrenOf_iff_parentOf h.childrenUnique p w).mp hw]
  rfl

theorem CapDerivationTree.childrenOf_length_le (cdt : CapDerivationTree) (p : SlotRef) :
    (cdt.childrenOf p).length ≤ cdt.edges.length := by
  unfold childrenOf; rw [List.length_map]; exact List.length_filter_le _ _

namespace LinkView

/-- **Link a new first child** `c` under `p`, as `addEdge p c` adds it: `c`
takes `p` as parent and `p`'s old first child as next sibling, that sibling
takes `c` as previous, and `p`'s first child becomes `c`. -/
def addChild (L : LinkView) (p c : SlotRef) : LinkView :=
  let f0 := L p .firstChild
  let L1 := ((L.set c .parent (some p)).set c .next f0).set c .prev none
  let L2 := match f0 with
    | some x => L1.set x .prev (some c)
    | none => L1
  L2.set p .firstChild (some c)

theorem addChild_parent (L : LinkView) (p c r : SlotRef) :
    L.addChild p c r .parent = if r = c then some p else L r .parent := by
  unfold addChild; cases L p .firstChild <;> by_cases h : r = c <;> simp [set, h]

theorem addChild_firstChild (L : LinkView) (p c r : SlotRef) :
    L.addChild p c r .firstChild = if r = p then some c else L r .firstChild := by
  unfold addChild; cases L p .firstChild <;> by_cases h : r = p <;> simp [set, h]

theorem addChild_next (L : LinkView) (p c r : SlotRef) :
    L.addChild p c r .next = if r = c then L p .firstChild else L r .next := by
  unfold addChild; cases hf : L p .firstChild <;> by_cases h : r = c <;> simp [set, h]

theorem addChild_prev (L : LinkView) (p c r : SlotRef) :
    L.addChild p c r .prev =
      if L p .firstChild = some r then some c else if r = c then none else L r .prev := by
  unfold addChild
  cases hf : L p .firstChild with
  | none => by_cases h : r = c <;> simp [set, h]
  | some x =>
    by_cases hx : r = x
    · subst hx; simp [set]
    · have hx' : ¬ x = r := fun e => hx e.symm
      by_cases h : r = c
      · subst h; simp [set, hx, hx']
      · simp [set, h, hx, hx']

end LinkView


namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

/-- **Adding an edge to a slot with no parent**, with `addChild`'s link writes,
keeps the links agreeing.  `c` may have children of its own (a splice re-adds a
subtree); it must only be no one's child yet, and not `p`. -/
theorem addChild (h : LinksAgree L cdt) {p c : SlotRef} (op : DerivationOp)
    (hc : cdt.parentOf c = none) (hpc : p ≠ c) :
    LinksAgree (L.addChild p c) (cdt.addEdge p c op) := by
  have hU := h.childrenUnique
  have hNotChild : ∀ q, c ∉ cdt.childrenOf q := fun q hm => by
    rw [(mem_childrenOf_iff_parentOf hU q c).mp hm] at hc; cases hc
  have hcp : c ≠ p := fun e => hpc e.symm
  refine ⟨?_, fun r => ?_, fun q => ?_, fun r => ?_, fun r => ?_⟩
  · unfold CapDerivationTree.childrenUnique; rw [CapDerivationTree.addEdge_edges]
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hU⟩
    obtain ⟨e, he, hec⟩ := List.mem_map.mp hm
    exact hNotChild e.parent ((mem_childrenOf cdt _ _).mpr ⟨e, he, rfl, hec⟩)
  · rw [addChild_parent, parentOf_addEdge]
    split
    · rfl
    · exact h.parent r
  · rw [addChild_firstChild, childrenOf_addEdge]
    by_cases hq : q = p
    · simp [hq]
    · simp only [if_neg hq]; exact h.firstChild q
  · rw [addChild_next, parentOf_addEdge]
    by_cases hr : r = c
    · subst hr
      simp only [if_true, Option.bind_some, childrenOf_addEdge, SlotList.succIn_cons]
      exact h.firstChild p
    · simp only [if_neg hr]
      rw [h.next r]
      cases hP : cdt.parentOf r with
      | none => rfl
      | some q =>
        simp only [Option.bind_some, childrenOf_addEdge]
        split
        · rw [SlotList.succIn_cons, if_neg (Ne.symm hr)]
        · rfl
  · rw [addChild_prev, parentOf_addEdge, h.firstChild p]
    by_cases hr : r = c
    · subst hr
      have : (cdt.childrenOf p).head? ≠ some r := fun e => hNotChild p (List.mem_of_mem_head? e)
      simp only [if_neg this, if_true, Option.bind_some, childrenOf_addEdge, SlotList.predIn_cons]
    · simp only [if_neg hr]
      by_cases hhd : (cdt.childrenOf p).head? = some r
      · rw [if_pos hhd]
        have hmem := List.mem_of_mem_head? hhd
        rw [(mem_childrenOf_iff_parentOf hU p r).mp hmem]
        simp only [Option.bind_some, childrenOf_addEdge, if_true, SlotList.predIn_cons,
          if_neg (Ne.symm hr), if_pos hhd]
      · rw [if_neg hhd, h.prev r]
        cases hP : cdt.parentOf r with
        | none => rfl
        | some q =>
          simp only [Option.bind_some, childrenOf_addEdge]
          split
          · next hq =>
            subst hq
            rw [SlotList.predIn_cons, if_neg (Ne.symm hr), if_neg hhd]
          · rfl

end LinksAgree

namespace LinkView

/-- **Unlink `n` from its siblings**, as `removeNode n` drops its parent edge:
its previous sibling (or, when it was the first child, its parent) takes its next
sibling, that sibling takes its previous one, and `n` keeps no parent or
sibling link. -/
def unlinkChild (L : LinkView) (n : SlotRef) : LinkView :=
  let pr := L n .prev
  let nx := L n .next
  let L1 := match pr with
    | some x => L.set x .next nx
    | none => match L n .parent with
      | some p => L.set p .firstChild nx
      | none => L
  let L2 := match nx with
    | some y => L1.set y .prev pr
    | none => L1
  ((L2.set n .parent none).set n .next none).set n .prev none

/-- **Clear a slot's parent and sibling links**: an orphaned child of a removed node. -/
def orphan (L : LinkView) (c : SlotRef) : LinkView :=
  ((L.set c .parent none).set c .next none).set c .prev none

/-- **The link writes of `removeNode n`**, given `n`'s children `l`: unlink `n`,
orphan each child, and clear `n`'s first-child link. -/
def removeNodeLinks (L : LinkView) (n : SlotRef) (l : List SlotRef) : LinkView :=
  (l.foldl orphan (L.unlinkChild n)).set n .firstChild none

theorem unlinkChild_parent (L : LinkView) (n r : SlotRef) :
    L.unlinkChild n r .parent = if r = n then none else L r .parent := by
  unfold unlinkChild
  cases L n .prev <;> cases L n .next <;> cases L n .parent <;> by_cases h : r = n <;>
    simp [set, h]

theorem unlinkChild_firstChild (L : LinkView) (n r : SlotRef) :
    L.unlinkChild n r .firstChild =
      if L n .prev = none ∧ L n .parent = some r then L n .next else L r .firstChild := by
  unfold unlinkChild
  cases L n .prev <;> cases L n .next <;> cases hp : L n .parent <;> simp [set] <;>
    simp only [@eq_comm _ r]

theorem unlinkChild_next (L : LinkView) (n r : SlotRef) :
    L.unlinkChild n r .next =
      if r = n then none else if L n .prev = some r then L n .next else L r .next := by
  unfold unlinkChild
  by_cases h : r = n
  · subst h; cases L r .prev <;> cases L r .next <;> cases L r .parent <;> simp [set]
  · cases hpr : L n .prev <;> cases L n .next <;> cases L n .parent <;> simp [set, h] <;>
      simp only [@eq_comm _ r]

theorem unlinkChild_prev (L : LinkView) (n r : SlotRef) :
    L.unlinkChild n r .prev =
      if r = n then none else if L n .next = some r then L n .prev else L r .prev := by
  unfold unlinkChild
  by_cases h : r = n
  · subst h; cases L r .prev <;> cases L r .next <;> cases L r .parent <;> simp [set]
  · cases L n .prev <;> cases hnx : L n .next <;> cases L n .parent <;> simp [set, h] <;>
      simp only [@eq_comm _ r]

/-- Unlinking names no slot the links did not name. -/
theorem unlinkChild_target {L : LinkView} {n r : SlotRef} {f : LinkField} {x : SlotRef}
    (h : L.unlinkChild n r f = some x) : ∃ v g, L v g = some x := by
  cases f
  · rw [unlinkChild_parent] at h; split at h
    · cases h
    · exact ⟨_, _, h⟩
  · rw [unlinkChild_firstChild] at h; split at h <;> exact ⟨_, _, h⟩
  · rw [unlinkChild_next] at h; split at h
    · cases h
    · split at h <;> exact ⟨_, _, h⟩
  · rw [unlinkChild_prev] at h; split at h
    · cases h
    · split at h <;> exact ⟨_, _, h⟩

theorem foldl_orphan (l : List SlotRef) :
    ∀ (L : LinkView) (r : SlotRef) (f : LinkField),
      l.foldl orphan L r f = if f ≠ .firstChild ∧ r ∈ l then none else L r f := by
  induction l with
  | nil => intro L r f; simp
  | cons c l ih =>
    intro L r f
    rw [List.foldl_cons, ih]
    by_cases hr : r ∈ l
    · cases f <;> simp [hr, orphan, set]
    · by_cases hc : r = c
      · subst hc; cases f <;> simp [orphan, set, hr]
      · cases f <;> simp [orphan, set, hr, hc]

theorem orphan_apply (L : LinkView) (c r : SlotRef) (f : LinkField) :
    L.orphan c r f = if r = c ∧ f ≠ .firstChild then none else L r f := by
  unfold orphan; cases f <;> by_cases h : r = c <;> simp [set, h]

/-- Linking `c` overwrites every link orphaning it cleared. -/
theorem orphan_addChild (L : LinkView) (u c : SlotRef) :
    (L.orphan c).addChild u c = L.addChild u c := by
  funext r f
  have hu : (L.orphan c) u .firstChild = L u .firstChild := by rw [orphan_apply]; simp
  cases f
  · rw [addChild_parent, addChild_parent, orphan_apply]; by_cases hr : r = c <;> simp [hr]
  · rw [addChild_firstChild, addChild_firstChild, orphan_apply]; simp
  · rw [addChild_next, addChild_next, hu, orphan_apply]; by_cases hr : r = c <;> simp [hr]
  · rw [addChild_prev, addChild_prev, hu, orphan_apply]; by_cases hr : r = c <;> simp [hr]

/-- Orphaning a slot other than `c` and `u`'s first child commutes with linking `c` under `u`. -/
theorem orphan_addChild_comm (L : LinkView) {u c x : SlotRef} (hxc : x ≠ c)
    (hxf : L u .firstChild ≠ some x) :
    (L.orphan x).addChild u c = (L.addChild u c).orphan x := by
  funext r f
  have hu : (L.orphan x) u .firstChild = L u .firstChild := by rw [orphan_apply]; simp
  cases f
  · rw [addChild_parent, orphan_apply, orphan_apply, addChild_parent]
    by_cases hr : r = c
    · have : r ≠ x := fun e => hxc (e ▸ hr ▸ rfl)
      simp [hr, hxc.symm]
    · simp [hr]
  · rw [addChild_firstChild, orphan_apply, orphan_apply, addChild_firstChild]; simp
  · rw [addChild_next, hu, orphan_apply, orphan_apply, addChild_next]
    by_cases hr : r = c
    · simp [hr, Ne.symm hxc]
    · simp [hr]
  · rw [addChild_prev, hu, orphan_apply, orphan_apply, addChild_prev]
    by_cases hrx : r = x
    · subst hrx; simp [hxf, hxc]
    · simp [hrx]

theorem foldl_orphan_addChild_comm {u c : SlotRef} :
    ∀ (l : List SlotRef) (M : LinkView), c ∉ l → (∀ x ∈ l, M u .firstChild ≠ some x) →
      l.foldl orphan (M.addChild u c) = (l.foldl orphan M).addChild u c
  | [], _, _, _ => rfl
  | x :: l, M, hc, hx => by
    simp only [List.foldl_cons]
    have hxc : x ≠ c := fun e => hc (e ▸ List.mem_cons_self ..)
    rw [← orphan_addChild_comm M hxc (hx x (List.mem_cons_self ..))]
    refine foldl_orphan_addChild_comm l _ (fun h => hc (List.mem_cons_of_mem _ h)) (fun y hy => ?_)
    rw [orphan_apply]; simp only [ne_eq, not_true_eq_false, and_false, if_false]
    exact hx y (List.mem_cons_of_mem _ hy)

/-- **Linking each slot of `l` under `u` overwrites orphaning them first**, when
`l` has no duplicates and none is `u`'s first child to start with. -/
theorem foldl_addChild_foldl_orphan {u : SlotRef} :
    ∀ (l : List SlotRef) (M : LinkView), l.Nodup → (∀ x ∈ l, M u .firstChild ≠ some x) →
      l.foldl (fun L c => L.addChild u c) (l.foldl orphan M) =
        l.foldl (fun L c => L.addChild u c) M
  | [], _, _, _ => rfl
  | c :: l, M, hnd, hx => by
    have ⟨hcL, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    have hM : (M.orphan c) u .firstChild = M u .firstChild := by
      rw [orphan_apply]; simp
    rw [← foldl_orphan_addChild_comm l (M.orphan c) hcL (fun y hy => hM ▸ hx y (List.mem_cons_of_mem _ hy)),
      orphan_addChild]
    refine foldl_addChild_foldl_orphan l _ hnd' (fun y hy => ?_)
    rw [addChild_firstChild, if_pos rfl]
    exact fun e => hcL (Option.some.inj e ▸ hy)

/-- Setting another slot's first-child link commutes with linking under `u`. -/
theorem set_firstChild_addChild_comm (L : LinkView) {n u : SlotRef} (h : n ≠ u) (c : SlotRef)
    (v : Option SlotRef) :
    (L.set n .firstChild v).addChild u c = (L.addChild u c).set n .firstChild v := by
  funext r f
  have hu : (L.set n .firstChild v) u .firstChild = L u .firstChild := L.set_ne_slot _ _ _ h.symm
  cases f
  · rw [addChild_parent, set_ne_field _ _ _ _ (by decide), set_ne_field _ _ _ _ (by decide),
      addChild_parent]
  · rw [addChild_firstChild]
    by_cases hr : r = u
    · subst hr; rw [if_pos rfl, set_ne_slot _ _ _ _ h.symm, addChild_firstChild, if_pos rfl]
    · rw [if_neg hr]
      by_cases hn : r = n
      · subst hn; simp
      · rw [set_ne_slot _ _ _ _ hn, set_ne_slot _ _ _ _ hn, addChild_firstChild, if_neg hr]
  · rw [addChild_next, hu, set_ne_field _ _ _ _ (by decide), set_ne_field _ _ _ _ (by decide),
      addChild_next]
  · rw [addChild_prev, hu, set_ne_field _ _ _ _ (by decide), set_ne_field _ _ _ _ (by decide),
      addChild_prev]

theorem set_firstChild_foldl_addChild_comm {n u : SlotRef} (h : n ≠ u) (v : Option SlotRef) :
    ∀ (l : List SlotRef) (M : LinkView),
      l.foldl (fun L c => L.addChild u c) (M.set n .firstChild v) =
        (l.foldl (fun L c => L.addChild u c) M).set n .firstChild v
  | [], _ => rfl
  | c :: l, M => by
    simp only [List.foldl_cons]
    rw [set_firstChild_addChild_comm M h c v]
    exact set_firstChild_foldl_addChild_comm h v l _

end LinkView

namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

/-- **Removing a node**, with `removeNodeLinks`' writes over its children,
keeps the links agreeing. -/
theorem removeNode (h : LinksAgree L cdt) (n : SlotRef) :
    LinksAgree (L.removeNodeLinks n (cdt.childrenOf n)) (cdt.removeNode n) := by
  have hU := h.childrenUnique
  have hMem : ∀ p r, r ∈ cdt.childrenOf p ↔ cdt.parentOf r = some p := fun p r =>
    mem_childrenOf_iff_parentOf hU p r
  have hNd : ∀ p, (cdt.childrenOf p).Nodup := childrenOf_nodup hU
  refine ⟨childrenUnique_sublist hU (removeNode_sublist cdt n), fun r => ?_, fun q => ?_,
    fun r => ?_, fun r => ?_⟩
  · simp only [removeNodeLinks]
    rw [set_ne_field _ _ _ _ (by decide), foldl_orphan, unlinkChild_parent,
      parentOf_removeNode hU]
    by_cases h1 : r = n
    · simp [h1]
    · by_cases h2 : cdt.parentOf r = some n
      · simp [h1, h2, (hMem n r).mpr h2]
      · have : r ∉ cdt.childrenOf n := fun e => h2 ((hMem n r).mp e)
        simp [h1, h2, this, h.parent r]
  · simp only [removeNodeLinks]
    rw [childrenOf_removeNode]
    by_cases hq : q = n
    · subst hq; simp
    · rw [set_ne_slot _ _ _ _ hq, foldl_orphan, if_neg (by simp), unlinkChild_firstChild,
        if_neg hq, SlotList.head_drop (hNd q), h.prev n, h.parent n, h.next n, h.firstChild q]
      cases hP : cdt.parentOf n with
      | none =>
        have hh : (cdt.childrenOf q).head? ≠ some n := fun e => by
          have := (hMem q n).mp (List.mem_of_mem_head? e); rw [hP] at this; cases this
        simp [hh]
      | some p =>
        by_cases hpq : p = q
        · subst hpq
          have hm : n ∈ cdt.childrenOf p := (hMem p n).mpr hP
          by_cases hh : (cdt.childrenOf p).head? = some n
          · simp [hh, (SlotList.predIn_eq_none_iff hm).mpr hh]
          · have : SlotList.predIn (cdt.childrenOf p) n ≠ none := fun e =>
              hh ((SlotList.predIn_eq_none_iff hm).mp e)
            simp [hh, this]
        · have hh : (cdt.childrenOf q).head? ≠ some n := fun e => by
            have := (hMem q n).mp (List.mem_of_mem_head? e); rw [hP] at this
            exact hpq (Option.some.inj this)
          simp [hh, hpq]
  · simp only [removeNodeLinks]
    rw [set_ne_field _ _ _ _ (by decide), foldl_orphan, unlinkChild_next, parentOf_removeNode hU]
    by_cases h1 : r = n
    · simp [h1]
    · by_cases h2 : r ∈ cdt.childrenOf n
      · simp [h2, (hMem n r).mp h2]
      · have h2' : cdt.parentOf r ≠ some n := fun e => h2 ((hMem n r).mpr e)
        simp only [h1, h2, h2', and_false, or_self, if_false]
        rw [h.prev n, h.next n, h.next r]
        cases hR : cdt.parentOf r with
        | none =>
          have : ¬ ((cdt.parentOf n).bind fun p => SlotList.predIn (cdt.childrenOf p) n) = some r := by
            cases cdt.parentOf n with
            | none => simp
            | some p =>
              intro e
              have := (hMem p r).mp (SlotList.predIn_mem e); rw [hR] at this; cases this
          simp [this]
        | some p =>
          have hpn : p ≠ n := fun e => h2' (e ▸ hR)
          simp only [Option.bind_some, childrenOf_removeNode, if_neg hpn]
          rw [SlotList.succIn_drop (hNd p) h1]
          by_cases hs : SlotList.succIn (cdt.childrenOf p) r = some n
          · have hP : cdt.parentOf n = some p := (hMem p n).mp (SlotList.succIn_mem hs)
            rw [hP]; simp only [Option.bind_some]
            rw [if_pos ((SlotList.succIn_eq_iff_predIn (hNd p)).mp hs), if_pos hs]
          · rw [if_neg hs]
            have : ¬ ((cdt.parentOf n).bind fun p => SlotList.predIn (cdt.childrenOf p) n) = some r := by
              cases cdt.parentOf n with
              | none => simp
              | some p' =>
                intro e
                simp only [Option.bind_some] at e
                have := (hMem p' r).mp (SlotList.predIn_mem e); rw [hR] at this
                obtain rfl := Option.some.inj this
                exact hs ((SlotList.succIn_eq_iff_predIn (hNd p)).mpr e)
            rw [if_neg this]
  · simp only [removeNodeLinks]
    rw [set_ne_field _ _ _ _ (by decide), foldl_orphan, unlinkChild_prev, parentOf_removeNode hU]
    by_cases h1 : r = n
    · simp [h1]
    · by_cases h2 : r ∈ cdt.childrenOf n
      · simp [h2, (hMem n r).mp h2]
      · have h2' : cdt.parentOf r ≠ some n := fun e => h2 ((hMem n r).mpr e)
        simp only [h1, h2, h2', and_false, or_self, if_false]
        rw [h.prev n, h.next n, h.prev r]
        cases hR : cdt.parentOf r with
        | none =>
          have : ¬ ((cdt.parentOf n).bind fun p => SlotList.succIn (cdt.childrenOf p) n) = some r := by
            cases cdt.parentOf n with
            | none => simp
            | some p =>
              intro e
              have := (hMem p r).mp (SlotList.succIn_mem e); rw [hR] at this; cases this
          simp [this]
        | some p =>
          have hpn : p ≠ n := fun e => h2' (e ▸ hR)
          simp only [Option.bind_some, childrenOf_removeNode, if_neg hpn]
          rw [SlotList.predIn_drop (hNd p) h1]
          by_cases hs : SlotList.predIn (cdt.childrenOf p) r = some n
          · have hP : cdt.parentOf n = some p := (hMem p n).mp (SlotList.predIn_mem hs)
            rw [hP]; simp only [Option.bind_some]
            rw [if_pos ((SlotList.succIn_eq_iff_predIn (hNd p)).mpr hs), if_pos hs]
          · rw [if_neg hs]
            have : ¬ ((cdt.parentOf n).bind fun p => SlotList.succIn (cdt.childrenOf p) n) = some r := by
              cases cdt.parentOf n with
              | none => simp
              | some p' =>
                intro e
                simp only [Option.bind_some] at e
                have := (hMem p' r).mp (SlotList.succIn_mem e); rw [hR] at this
                obtain rfl := Option.some.inj this
                exact hs ((SlotList.succIn_eq_iff_predIn (hNd p)).mp e)
            rw [if_neg this]

end LinksAgree

namespace LinkView

/-- **The link writes of `spliceNode n`**, given `n`'s parent `up` and children
`l`: with a parent `u`, unlink `n`, link each child under `u` in chain order and
clear `n`'s first-child link; without one, remove `n`. -/
def spliceLinks (L : LinkView) (n : SlotRef) (up : Option SlotRef) (l : List SlotRef) : LinkView :=
  match up with
  | none => L.removeNodeLinks n l
  | some u => (l.foldl (fun L c => L.addChild u c) (L.unlinkChild n)).set n .firstChild none

/-- **The link writes of `moveNode old new`**, given `old`'s parent `up` and
children `l`: unlink `old`, link `new` under `up`, link each child under `new`
in chain order and clear `old`'s first-child link. -/
def moveLinks (L : LinkView) (old new : SlotRef) (up : Option SlotRef) (l : List SlotRef) :
    LinkView :=
  (l.foldl (fun (L : LinkView) c => L.addChild new c)
    (match up with
     | some u => (L.unlinkChild old).addChild u new
     | none => L.unlinkChild old)).set old .firstChild none

end LinkView

namespace LinksAgree

open CapDerivationTree LinkView

/-- **Adding a run of edges under one parent**, with one `addChild` each, keeps
the links agreeing when the children are distinct, parentless and not `p`. -/
theorem foldl_addChild (p : SlotRef) :
    ∀ (es : List CapDerivationEdge) {L : LinkView} {cdt : CapDerivationTree},
      LinksAgree L cdt → (es.map (·.child)).Nodup →
      (∀ e ∈ es, cdt.parentOf e.child = none ∧ p ≠ e.child) →
      LinksAgree ((es.map (·.child)).foldl (fun L c => L.addChild p c) L)
        (es.foldl (fun acc e => acc.addEdge p e.child e.op) cdt)
  | [], _, _, h, _, _ => h
  | e :: es, L, cdt, h, hnd, hc => by
    have ⟨heL, hnd'⟩ := List.nodup_cons.mp hnd
    have ⟨h1, h2⟩ := hc e (List.mem_cons_self ..)
    simp only [List.map_cons, List.foldl_cons]
    refine foldl_addChild p es (h.addChild e.op h1 h2) hnd' (fun e' he' => ?_)
    have hne : e'.child ≠ e.child := fun hq => heL (by
      have := List.mem_map_of_mem (f := (·.child)) he'; simp only at this; rw [hq] at this; exact this)
    rw [parentOf_addEdge, if_neg hne]
    exact hc e' (List.mem_cons_of_mem _ he')

private theorem filter_parent_children (cdt : CapDerivationTree) (n : SlotRef) :
    (cdt.edges.filter (·.isParentOf n)).map (·.child) = cdt.childrenOf n := rfl

private theorem find_child_parent (cdt : CapDerivationTree) (n : SlotRef) :
    (cdt.edges.find? (·.isChildOf n)).map (·.parent) = cdt.parentOf n := rfl

/-- Each edge from `n` names one of `n`'s children. -/
private theorem filter_parent_mem {cdt : CapDerivationTree} {n : SlotRef} {e : CapDerivationEdge}
    (he : e ∈ cdt.edges.filter (·.isParentOf n)) : e.child ∈ cdt.childrenOf n :=
  List.mem_map_of_mem he

/-- Splicing as removal followed by re-linking the children under the parent. -/
private theorem spliceNode_byRemoval {L : LinkView} {cdt : CapDerivationTree} (h : LinksAgree L cdt)
    (n : SlotRef) (hcyc : ∀ c ∈ cdt.childrenOf n, cdt.parentOf n ≠ some c) :
    LinksAgree (match cdt.parentOf n with
      | none => L.removeNodeLinks n (cdt.childrenOf n)
      | some u => (cdt.childrenOf n).foldl (fun L c => L.addChild u c)
          (L.removeNodeLinks n (cdt.childrenOf n))) (cdt.spliceNode n) := by
  have hU := h.childrenUnique
  have hR := h.removeNode n
  refine LinksAgree.of_edges_eq (CapDerivationTree.spliceNode_edges_fold cdt n).symm ?_
  rw [← find_child_parent]
  cases hf : cdt.edges.find? (·.isChildOf n) with
  | none => exact hR
  | some up =>
    simp only [Option.map_some]
    have := foldl_addChild up.parent (cdt.edges.filter (·.isParentOf n)) hR
      (by rw [filter_parent_children]; exact childrenOf_nodup hU n) (fun e he => ?_)
    · exact this
    have hm := filter_parent_mem he
    refine ⟨?_, fun hpc => hcyc _ hm ?_⟩
    · rw [parentOf_removeNode hU, if_pos (.inr ((mem_childrenOf_iff_parentOf hU n _).mp hm))]
    · rw [← find_child_parent, hf, ← hpc]; rfl

/-- Moving as removal followed by re-linking. -/
private theorem moveNode_byRemoval {L : LinkView} {cdt : CapDerivationTree} (h : LinksAgree L cdt)
    (old new : SlotRef) (hnew : ¬ cdt.mentions new) :
    LinksAgree ((cdt.childrenOf old).foldl (fun L c => L.addChild new c)
      (match cdt.parentOf old with
       | some u => (L.removeNodeLinks old (cdt.childrenOf old)).addChild u new
       | none => L.removeNodeLinks old (cdt.childrenOf old))) (cdt.moveNode old new) := by
  have hU := h.childrenUnique
  have hR := h.removeNode old
  have hNd := childrenOf_nodup hU old
  have hEdge : ∀ e ∈ cdt.edges.filter (·.isParentOf old),
      (cdt.removeNode old).parentOf e.child = none ∧ new ≠ e.child := fun e he => by
    have hm := filter_parent_mem he
    refine ⟨?_, fun hc => hnew ⟨e, (List.mem_filter.mp he).1, .inr hc.symm⟩⟩
    rw [parentOf_removeNode hU, if_pos (.inr ((mem_childrenOf_iff_parentOf hU old _).mp hm))]
  refine LinksAgree.of_edges_eq (CapDerivationTree.moveNode_edges_fold cdt old new).symm ?_
  rw [← find_child_parent]
  cases hf : cdt.edges.find? (·.isChildOf old) with
  | none => exact foldl_addChild new _ hR hNd hEdge
  | some up =>
    have hup := List.mem_of_find?_eq_some hf
    have hNew : (cdt.removeNode old).parentOf new = none := by
      rw [parentOf_removeNode hU, parentOf_of_not_mentions hnew]; split <;> rfl
    have hpn : up.parent ≠ new := fun e => hnew ⟨up, hup, .inl e⟩
    refine foldl_addChild new _ (hR.addChild up.op hNew hpn) hNd (fun e he => ?_)
    have ⟨h1, h2⟩ := hEdge e he
    exact ⟨by rw [parentOf_addEdge, if_neg (Ne.symm h2)]; exact h1, h2⟩

variable {L : LinkView} {cdt : CapDerivationTree}

/-- A slot with no self edge is not among its own children, and its previous
sibling is not one of them either. -/
theorem children_not_self_or_prev (h : LinksAgree L cdt) {n : SlotRef}
    (hs : cdt.parentOf n ≠ some n) :
    ∀ w ∈ cdt.childrenOf n, w ≠ n ∧ L n .prev ≠ some w := by
  have hU := h.childrenUnique
  intro w hw
  have hpw := (mem_childrenOf_iff_parentOf hU n w).mp hw
  refine ⟨fun e => hs (e ▸ hpw), fun e => ?_⟩
  rw [h.prev n] at e
  cases hP : cdt.parentOf n with
  | none => rw [hP] at e; cases e
  | some p =>
    rw [hP] at e
    have := (mem_childrenOf_iff_parentOf hU p w).mp (SlotList.predIn_mem e)
    rw [hpw] at this
    exact hs (Option.some.inj this ▸ hP)

/-- After unlinking `n`, its parent's first child is no child of `n`. -/
theorem unlink_parent_firstChild_ne (h : LinksAgree L cdt) {n u : SlotRef}
    (hu : cdt.parentOf n = some u) (hs : u ≠ n) :
    ∀ x ∈ cdt.childrenOf n, (L.unlinkChild n) u .firstChild ≠ some x := by
  have hU := h.childrenUnique
  intro x hx e
  have hxn := (mem_childrenOf_iff_parentOf hU n x).mp hx
  have hxu : x ∈ cdt.childrenOf u := by
    rw [unlinkChild_firstChild] at e
    split at e
    · rw [h.next n, hu] at e; exact SlotList.succIn_mem e
    · rw [h.firstChild u] at e; exact List.mem_of_mem_head? e
  rw [(mem_childrenOf_iff_parentOf hU u x).mp hxu] at hxn
  exact hs (Option.some.inj hxn)

/-- The walk from a slot's first child, with fuel the tree's edge count, reads its children. -/
theorem walk_firstChild (h : LinksAgree L cdt) (n : SlotRef) {k : Nat}
    (hk : cdt.edges.length ≤ k) : L.walk k (L n .firstChild) = cdt.childrenOf n :=
  h.walk_children n (Nat.le_trans (cdt.childrenOf_length_le n) hk)

/-- **Splicing a node out** keeps the links agreeing, when the tree has no edge
from `n` to itself or between `n` and a child of it in reverse (it is acyclic). -/
theorem spliceNode (h : LinksAgree L cdt) (n : SlotRef)
    (hcyc : ∀ c ∈ cdt.childrenOf n, cdt.parentOf n ≠ some c) (hs : cdt.parentOf n ≠ some n) :
    LinksAgree (L.spliceLinks n (cdt.parentOf n) (cdt.childrenOf n)) (cdt.spliceNode n) := by
  have hB := spliceNode_byRemoval h n hcyc
  cases hu : cdt.parentOf n with
  | none => rw [hu] at hB; exact hB
  | some u =>
    rw [hu] at hB
    have hun : u ≠ n := fun e => hs (e ▸ hu)
    simp only [spliceLinks]
    have e : (cdt.childrenOf n).foldl (fun L c => L.addChild u c)
        (L.removeNodeLinks n (cdt.childrenOf n)) =
        ((cdt.childrenOf n).foldl (fun L c => L.addChild u c) (L.unlinkChild n)).set n
          .firstChild none := by
      unfold removeNodeLinks
      rw [set_firstChild_foldl_addChild_comm (Ne.symm hun),
        foldl_addChild_foldl_orphan _ _ (childrenOf_nodup h.childrenUnique n)
          (h.unlink_parent_firstChild_ne hu hun)]
    rw [← e]; exact hB

/-- **Moving a node to a slot outside the tree** keeps the links agreeing. -/
theorem moveNode (h : LinksAgree L cdt) (old new : SlotRef) (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) (hs : cdt.parentOf old ≠ some old) :
    LinksAgree (L.moveLinks old new (cdt.parentOf old) (cdt.childrenOf old))
      (cdt.moveNode old new) := by
  have hU := h.childrenUnique
  have hB := moveNode_byRemoval h old new hnew
  have hNd := childrenOf_nodup hU old
  have hNewL : new ∉ cdt.childrenOf old := not_mem_childrenOf_of_not_mentions hnew old
  have hNewF : L new .firstChild = none := by
    rw [h.firstChild new, childrenOf_of_not_mentions hnew]; rfl
  have hNewP : cdt.parentOf old ≠ some new := fun e =>
    hnew ⟨_, ((parentOf_eq_some_iff hU new old).mp e).choose_spec.1,
      .inl ((parentOf_eq_some_iff hU new old).mp e).choose_spec.2.1⟩
  have hL1new : (L.unlinkChild old) new .firstChild = none := by
    rw [unlinkChild_firstChild, h.parent old, if_neg (fun hc => hNewP hc.2), hNewF]
  unfold moveLinks
  cases hu : cdt.parentOf old with
  | none =>
    rw [hu] at hB
    simp only at hB ⊢
    unfold removeNodeLinks at hB
    rw [set_firstChild_foldl_addChild_comm hon,
      foldl_addChild_foldl_orphan _ _ hNd (fun x _ => by rw [hL1new]; exact fun e => by cases e)] at hB
    exact hB
  | some u =>
    rw [hu] at hB
    simp only at hB ⊢
    have hun : u ≠ old := fun e => hs (e ▸ hu)
    have hnu : new ≠ u := fun e => hnew ⟨_, ((parentOf_eq_some_iff hU u old).mp hu).choose_spec.1,
      .inl (e ▸ ((parentOf_eq_some_iff hU u old).mp hu).choose_spec.2.1)⟩
    unfold removeNodeLinks at hB
    rw [set_firstChild_addChild_comm _ (Ne.symm hun), set_firstChild_foldl_addChild_comm hon,
      ← foldl_orphan_addChild_comm _ _ hNewL (h.unlink_parent_firstChild_ne hu (hun)),
      foldl_addChild_foldl_orphan _ _ hNd (fun x _ => by
        rw [addChild_firstChild, if_neg hnu, hL1new]; exact fun e => by cases e)] at hB
    exact hB

/-- **A tree with no edge agrees with links that are all empty**: the state a
boot or the default state starts from. -/
theorem of_no_edges {L' : LinkView} {t : CapDerivationTree} (hE : t.edges = [])
    (hL : ∀ r f, L' r f = none) : LinksAgree L' t := by
  have hn : ∀ r, ¬ t.mentions r := by
    rintro r ⟨e, he, -⟩; rw [hE] at he; cases he
  refine ⟨by unfold CapDerivationTree.childrenUnique; rw [hE]; exact List.nodup_nil,
    fun r => ?_, fun p => ?_, fun r => ?_, fun r => ?_⟩
  · rw [hL, CapDerivationTree.parentOf_of_not_mentions (hn r)]
  · rw [hL, CapDerivationTree.childrenOf_of_not_mentions (hn p)]; rfl
  · rw [hL, CapDerivationTree.parentOf_of_not_mentions (hn r)]; rfl
  · rw [hL, CapDerivationTree.parentOf_of_not_mentions (hn r)]; rfl

/-- **A slot the tree does not name holds no link.** -/
theorem none_of_not_mentions (h : LinksAgree L cdt) {r : SlotRef} (hn : ¬ cdt.mentions r)
    (f : LinkField) : L r f = none := by
  have hp := CapDerivationTree.parentOf_of_not_mentions hn
  cases f
  · rw [h.parent r, hp]
  · rw [h.firstChild r, CapDerivationTree.childrenOf_of_not_mentions hn]; rfl
  · rw [h.next r, hp]; rfl
  · rw [h.prev r, hp]; rfl

/-- **Every link names a slot the tree names.** -/
theorem target_mentions (h : LinksAgree L cdt) {r : SlotRef} {f : LinkField} {x : SlotRef}
    (hx : L r f = some x) : cdt.mentions x := by
  have child : ∀ p, x ∈ cdt.childrenOf p → cdt.mentions x := fun p hm => by
    obtain ⟨e, he, -, hc⟩ := (mem_childrenOf cdt p x).mp hm
    exact ⟨e, he, .inr hc⟩
  cases f
  · rw [h.parent r] at hx
    obtain ⟨e, he, hp, -⟩ := (parentOf_eq_some_iff h.childrenUnique x r).mp hx
    exact ⟨e, he, .inl hp⟩
  · rw [h.firstChild r] at hx; exact child r (List.mem_of_mem_head? hx)
  · rw [h.next r] at hx
    cases hP : cdt.parentOf r with
    | none => rw [hP] at hx; cases hx
    | some p => rw [hP] at hx; exact child p (SlotList.succIn_mem hx)
  · rw [h.prev r] at hx
    cases hP : cdt.parentOf r with
    | none => rw [hP] at hx; cases hx
    | some p => rw [hP] at hx; exact child p (SlotList.predIn_mem hx)

/-- An acyclic tree has no node that is its own parent. -/
theorem parentOf_ne_self_of_wf (h : LinksAgree L cdt) (hWF : cdt.edgeWellFounded) (n : SlotRef) :
    cdt.parentOf n ≠ some n := fun hp => by
  obtain ⟨e, he, hpe, hce⟩ := (parentOf_eq_some_iff h.childrenUnique n n).mp hp
  exact CapDerivationTree.edgeWellFounded_no_self_edge hWF he (hpe.trans hce.symm)

/-- An acyclic tree has no node whose parent is a child of it. -/
theorem parent_not_child_of_wf (h : LinksAgree L cdt) (hWF : cdt.edgeWellFounded) (n : SlotRef) :
    ∀ c ∈ cdt.childrenOf n, cdt.parentOf n ≠ some c := fun c hc hp => by
  obtain ⟨e₁, he₁, hp₁, hc₁⟩ := (mem_childrenOf cdt n c).mp hc
  obtain ⟨e₂, he₂, hp₂, hc₂⟩ := (parentOf_eq_some_iff h.childrenUnique c n).mp hp
  exact hWF n ⟨[n, c, n], by simp, rfl, rfl, fun i hi => by
    match i, hi with
    | 0, _ => exact ⟨e₁, he₁, hp₁, hc₁⟩
    | 1, _ => exact ⟨e₂, he₂, hp₂, hc₂⟩⟩

/-- **Splicing a node out of an acyclic tree** keeps the links agreeing. -/
theorem spliceNode_of_wf (h : LinksAgree L cdt) (hWF : cdt.edgeWellFounded) (n : SlotRef) :
    LinksAgree (L.spliceLinks n (cdt.parentOf n) (cdt.childrenOf n)) (cdt.spliceNode n) :=
  h.spliceNode n (h.parent_not_child_of_wf hWF n) (h.parentOf_ne_self_of_wf hWF n)

/-- **Moving a node of an acyclic tree to a slot outside it** keeps the links agreeing. -/
theorem moveNode_of_wf (h : LinksAgree L cdt) (hWF : cdt.edgeWellFounded) (old new : SlotRef)
    (hnew : ¬ cdt.mentions new) (hon : old ≠ new) :
    LinksAgree (L.moveLinks old new (cdt.parentOf old) (cdt.childrenOf old)) (cdt.moveNode old new) :=
  h.moveNode old new hnew hon (h.parentOf_ne_self_of_wf hWF old)

end LinksAgree
end SeLe4n.Model
