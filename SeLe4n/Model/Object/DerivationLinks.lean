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


/-- The element after `r` in `x ++ y`: after its first place in `x` when it is
in `x` (the head of `y` when that place is `x`'s last), else after it in `y`. -/
theorem succIn_append : ∀ (x y : List SlotRef) (r : SlotRef),
    succIn (x ++ y) r = if r ∈ x then (succIn x r).or y.head? else succIn y r
  | [], y, r => by simp
  | a :: x, y, r => by
    rw [List.cons_append, succIn_cons, succIn_cons]
    by_cases ha : a = r
    · subst ha; simp [List.head?_append]
    · rw [if_neg ha, if_neg ha, succIn_append x y r]
      have : (r ∈ a :: x) ↔ r ∈ x := by simp [Ne.symm ha]
      simp only [this]

/-- The element before `r` in `x ++ y`, given the one before the list. -/
theorem predAux_append : ∀ (p : Option SlotRef) (x y : List SlotRef) (r : SlotRef),
    predAux p (x ++ y) r = if r ∈ x then predAux p x r else predAux (x.getLast?.or p) y r
  | p, [], y, r => by simp
  | p, a :: x, y, r => by
    rw [List.cons_append]; simp only [predAux]
    by_cases ha : a = r
    · subst ha; simp
    · rw [if_neg ha, if_neg ha, predAux_append (some a) x y r]
      have : (r ∈ a :: x) ↔ r ∈ x := by simp [Ne.symm ha]
      simp only [this]
      congr 1
      rw [List.getLast?_cons]
      cases x.getLast? <;> rfl

theorem predIn_append (x y : List SlotRef) (r : SlotRef) :
    predIn (x ++ y) r = if r ∈ x then predIn x r else predAux x.getLast? y r := by
  unfold predIn; rw [predAux_append]; simp

/-- Past a list whose head is not `r`, the element before `r` is its own. -/
theorem predAux_of_head_ne {l : List SlotRef} {r : SlotRef} (p : Option SlotRef)
    (h : l.head? ≠ some r) : predAux p l r = predIn l r :=
  predAux_irrel h

theorem predAux_of_head {l : List SlotRef} {r : SlotRef} (p : Option SlotRef)
    (h : l.head? = some r) : predAux p l r = p := by
  cases l with
  | nil => cases h
  | cons a l => simp at h; subst h; simp [predAux]

/-- The neighbours of `n` in `a ++ n :: b`, when `n` is not in `a`. -/
theorem succIn_mid {a b : List SlotRef} {n : SlotRef} (h : n ∉ a) :
    succIn (a ++ n :: b) n = b.head? := by
  rw [succIn_append, if_neg h, succIn_cons, if_pos rfl]

theorem predIn_mid {a b : List SlotRef} {n : SlotRef} (h : n ∉ a) :
    predIn (a ++ n :: b) n = a.getLast? := by
  rw [predIn_append, if_neg h]; simp [predAux]

/-- A member has no successor only at the end. -/
theorem succIn_eq_none_iff : ∀ {l : List SlotRef} {r : SlotRef}, l.Nodup → r ∈ l →
    (succIn l r = none ↔ l.getLast? = some r)
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: l, r, hnd, h => by
    have ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    rw [succIn_cons, List.getLast?_cons]
    by_cases ha : a = r
    · subst ha
      rw [if_pos rfl]
      cases l with
      | nil => simp
      | cons b l =>
        simp only [List.head?_cons, reduceCtorEq, false_iff]
        intro e
        obtain ⟨z, hz⟩ : ∃ z, (b :: l).getLast? = some z := ⟨_, List.getLast?_cons⟩
        rw [hz] at e; simp only [Option.getD_some, Option.some.injEq] at e; subst e
        exact haL (List.mem_of_getLast? hz)
    · rw [if_neg ha]
      have hl : r ∈ l := (List.mem_cons.mp h).resolve_left (Ne.symm ha)
      rw [succIn_eq_none_iff hnd' hl]
      cases hL : l.getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hL; subst hL; cases hl
      | some z => simp

/-- Renaming the members of a list, injectively at `r`, renames `r`'s successor. -/
theorem succIn_map (f : SlotRef → SlotRef) : ∀ {l : List SlotRef} {r : SlotRef},
    (∀ x ∈ l, f x = f r → x = r) → succIn (l.map f) (f r) = (succIn l r).map f
  | [], _, _ => rfl
  | a :: l, r, h => by
    rw [List.map_cons, succIn_cons, succIn_cons]
    by_cases ha : a = r
    · subst ha; simp [List.head?_map]
    · have hf : f a ≠ f r := fun e => ha (h a (List.mem_cons_self ..) e)
      rw [if_neg hf, if_neg ha]
      exact succIn_map f (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem predAux_map (f : SlotRef → SlotRef) : ∀ {l : List SlotRef} {p : Option SlotRef} {r : SlotRef},
    (∀ x ∈ l, f x = f r → x = r) → predAux (p.map f) (l.map f) (f r) = (predAux p l r).map f
  | [], _, _, _ => rfl
  | a :: l, p, r, h => by
    rw [List.map_cons]; simp only [predAux]
    by_cases ha : a = r
    · subst ha; simp
    · have hf : f a ≠ f r := fun e => ha (h a (List.mem_cons_self ..) e)
      rw [if_neg hf, if_neg ha]
      exact predAux_map f (p := some a) (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem predIn_map (f : SlotRef → SlotRef) {l : List SlotRef} {r : SlotRef}
    (h : ∀ x ∈ l, f x = f r → x = r) : predIn (l.map f) (f r) = (predIn l r).map f :=
  predAux_map f (p := none) h

/-- In a duplicate-free list nothing follows or precedes itself. -/
theorem succIn_ne_self : ∀ {l : List SlotRef} {r : SlotRef}, l.Nodup → succIn l r ≠ some r
  | [], _, _ => by simp [succIn]
  | a :: l, r, hnd => by
    have ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    rw [succIn_cons]
    split
    · next ha => subst ha; exact fun e => haL (List.mem_of_mem_head? e)
    · exact succIn_ne_self hnd'

theorem predIn_ne_self {l : List SlotRef} {r : SlotRef} (hnd : l.Nodup) : predIn l r ≠ some r :=
  fun e => succIn_ne_self hnd ((succIn_eq_iff_predIn hnd).mpr e)

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
  (parentOf_eq_none_iff cdt c).mpr fun e he hc => h (.inl ⟨e, he, .inr hc⟩)

theorem childrenOf_of_not_mentions {cdt : CapDerivationTree} {c : SlotRef} (h : ¬ cdt.mentions c) :
    cdt.childrenOf c = [] := by
  rcases hL : cdt.childrenOf c with _ | ⟨x, l⟩
  · rfl
  · obtain ⟨e, he, hp, -⟩ := childrenOf_to_edge cdt c x (hL ▸ List.mem_cons_self ..)
    exact absurd (.inl ⟨e, he, .inl hp⟩) h

theorem not_mem_childrenOf_of_not_mentions {cdt : CapDerivationTree} {c : SlotRef}
    (h : ¬ cdt.mentions c) (q : SlotRef) : c ∉ cdt.childrenOf q := fun hm => by
  obtain ⟨e, he, -, hc⟩ := childrenOf_to_edge cdt q c hm
  exact h (.inl ⟨e, he, .inr hc⟩)

end CapDerivationTree


namespace CapDerivationTree

theorem childrenUnique_sublist {cdt cdt' : CapDerivationTree} (h : cdt.childrenUnique)
    (hs : cdt'.edges.Sublist cdt.edges) : cdt'.childrenUnique :=
  h.sublist (hs.map _)

/-- Under unique children, the parent read is the edge relation. -/
theorem parentOf_eq_some_iff {cdt : CapDerivationTree} (hU : cdt.childrenUnique) (p r : SlotRef) :
    cdt.parentOf r = some p ↔ ∃ e ∈ cdt.edges, e.parent = p ∧ e.child = r := by
  rw [← mem_childrenOf_iff_parentOf hU, mem_childrenOf]

end CapDerivationTree


/-! ### Sibling chains

A slot with a parent has its parent's children for siblings; a slot with no
parent has the root chain that lists it, or itself alone when no chain does. -/

namespace SlotList

/-- The chain of `cs` that holds `r`, or `[r]` when none does. -/
def chainOf (cs : List (List SlotRef)) (r : SlotRef) : List SlotRef :=
  (cs.find? fun c => decide (r ∈ c)).getD [r]

/-- Two chains of a duplicate-free family that share a member are one chain. -/
theorem chain_eq_of_mem : ∀ {cs : List (List SlotRef)}, cs.flatten.Nodup →
    ∀ {C D : List SlotRef} {x : SlotRef}, C ∈ cs → D ∈ cs → x ∈ C → x ∈ D → C = D
  | [], _, _, _, _, hC, _, _, _ => absurd hC List.not_mem_nil
  | F :: cs, hnd, C, D, x, hC, hD, hxC, hxD => by
    rw [List.flatten_cons, List.nodup_append] at hnd
    obtain ⟨-, hnd', hdis⟩ := hnd
    rcases List.mem_cons.mp hC with hCF | hC' <;> rcases List.mem_cons.mp hD with hDF | hD'
    · rw [hCF, hDF]
    · rw [hCF] at hxC; exact absurd rfl (hdis x hxC x (List.mem_flatten.mpr ⟨D, hD', hxD⟩))
    · rw [hDF] at hxD; exact absurd rfl (hdis x hxD x (List.mem_flatten.mpr ⟨C, hC', hxC⟩))
    · exact chain_eq_of_mem hnd' hC' hD' hxC hxD

theorem chainOf_of_mem {cs : List (List SlotRef)} (hnd : cs.flatten.Nodup) {C : List SlotRef}
    {r : SlotRef} (hC : C ∈ cs) (hr : r ∈ C) : chainOf cs r = C := by
  unfold chainOf
  cases hF : cs.find? (fun c => decide (r ∈ c)) with
  | none =>
    rw [List.find?_eq_none] at hF
    exact absurd (decide_eq_true hr) (hF C hC)
  | some D =>
    have hD := List.mem_of_find?_eq_some hF
    have hrD : r ∈ D := by have := List.find?_some hF; simpa using this
    exact chain_eq_of_mem hnd hD hC hrD hr

theorem chainOf_of_not_mem {cs : List (List SlotRef)} {r : SlotRef} (h : r ∉ cs.flatten) :
    chainOf cs r = [r] := by
  unfold chainOf
  rw [show cs.find? (fun c => decide (r ∈ c)) = none from List.find?_eq_none.mpr fun C hC hr =>
    h (List.mem_flatten.mpr ⟨C, hC, of_decide_eq_true hr⟩)]
  rfl

theorem chainOf_cases (cs : List (List SlotRef)) (r : SlotRef) :
    (∃ C ∈ cs, r ∈ C ∧ chainOf cs r = C) ∨ (r ∉ cs.flatten ∧ chainOf cs r = [r]) := by
  unfold chainOf
  cases hF : cs.find? (fun c => decide (r ∈ c)) with
  | none =>
    refine .inr ⟨fun hm => ?_, rfl⟩
    obtain ⟨C, hC, hr⟩ := List.mem_flatten.mp hm
    exact absurd (decide_eq_true hr) (List.find?_eq_none.mp hF C hC)
  | some D =>
    exact .inl ⟨D, List.mem_of_find?_eq_some hF, by have := List.find?_some hF; simpa using this, rfl⟩

theorem mem_chainOf_self (cs : List (List SlotRef)) (r : SlotRef) : r ∈ chainOf cs r := by
  rcases chainOf_cases cs r with ⟨C, -, hr, e⟩ | ⟨-, e⟩ <;> rw [e]
  · exact hr
  · exact List.mem_singleton_self r

theorem chainOf_nodup {cs : List (List SlotRef)} (hnd : cs.flatten.Nodup) (r : SlotRef) :
    (chainOf cs r).Nodup := by
  rcases chainOf_cases cs r with ⟨C, hC, -, e⟩ | ⟨-, e⟩ <;> rw [e]
  · exact hnd.sublist (List.sublist_flatten_of_mem hC)
  · simp

theorem mem_chainOf {cs : List (List SlotRef)} {r x : SlotRef} (h : x ∈ chainOf cs r) :
    x ∈ cs.flatten ∨ x = r := by
  rcases chainOf_cases cs r with ⟨C, hC, -, e⟩ | ⟨-, e⟩ <;> rw [e] at h
  · exact .inl (List.mem_flatten.mpr ⟨C, hC, h⟩)
  · exact .inr (List.mem_singleton.mp h)

theorem chainOf_eq_of_mem {cs : List (List SlotRef)} (hnd : cs.flatten.Nodup) {r x : SlotRef}
    (h : x ∈ chainOf cs r) : chainOf cs x = chainOf cs r := by
  rcases chainOf_cases cs r with ⟨C, hC, -, e⟩ | ⟨-, e⟩ <;> rw [e] at h ⊢
  · exact chainOf_of_mem hnd hC h
  · rw [List.mem_singleton.mp h]; exact e

end SlotList

namespace CapDerivationTree

/-- **The root chain holding `r`**: the chain of `rootChains` that lists it, or
`[r]` when none does. -/
noncomputable def rootChain (cdt : CapDerivationTree) (r : SlotRef) : List SlotRef :=
  SlotList.chainOf cdt.rootChains r

/-- **The siblings of `r`, `r` among them**, in link order: its parent's
children, or its root chain when it has no parent. -/
noncomputable def siblingsOf (cdt : CapDerivationTree) (r : SlotRef) : List SlotRef :=
  match cdt.parentOf r with
  | some p => cdt.childrenOf p
  | none => cdt.rootChain r

theorem siblingsOf_of_parent {cdt : CapDerivationTree} {r p : SlotRef}
    (h : cdt.parentOf r = some p) : cdt.siblingsOf r = cdt.childrenOf p := by
  unfold siblingsOf; rw [h]

theorem siblingsOf_of_root {cdt : CapDerivationTree} {r : SlotRef}
    (h : cdt.parentOf r = none) : cdt.siblingsOf r = cdt.rootChain r := by
  unfold siblingsOf; rw [h]

/-- No slot of a root chain has a parent. -/
def rootsParentless (cdt : CapDerivationTree) : Prop :=
  ∀ r ∈ cdt.rootChains.flatten, cdt.parentOf r = none

theorem mem_siblingsOf_self {cdt : CapDerivationTree} (hU : cdt.childrenUnique) (r : SlotRef) :
    r ∈ cdt.siblingsOf r := by
  unfold siblingsOf
  cases hP : cdt.parentOf r with
  | some p => exact (mem_childrenOf_iff_parentOf hU p r).mpr hP
  | none => exact SlotList.mem_chainOf_self _ r

theorem siblingsOf_nodup {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (hnd : cdt.rootChains.flatten.Nodup) (r : SlotRef) : (cdt.siblingsOf r).Nodup := by
  unfold siblingsOf
  cases cdt.parentOf r with
  | some p => exact childrenOf_nodup hU p
  | none => exact SlotList.chainOf_nodup hnd r

/-- A sibling's siblings are one's own. -/
theorem siblingsOf_eq_of_mem {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (hnd : cdt.rootChains.flatten.Nodup) (hR : cdt.rootsParentless) {r x : SlotRef}
    (h : x ∈ cdt.siblingsOf r) : cdt.siblingsOf x = cdt.siblingsOf r := by
  unfold siblingsOf at h ⊢
  cases hP : cdt.parentOf r with
  | some p =>
    rw [hP] at h
    rw [(mem_childrenOf_iff_parentOf hU p x).mp h]
  | none =>
    rw [hP] at h
    have hx : cdt.parentOf x = none := by
      rcases SlotList.mem_chainOf h with hm | rfl
      · exact hR x hm
      · exact hP
    rw [hx]; exact SlotList.chainOf_eq_of_mem hnd h

end CapDerivationTree


/-- **The links encode the tree, in seL4's order.**  Each slot's parent link is
its parent in the tree, its first-child link the newest of its children, and its
next and previous links its neighbours among its siblings (`siblingsOf`): its
parent's children, newest first, or, for a slot with no parent, its root chain.
No slot is the child of two edges, the root chains list each slot at most once,
and none of them has a parent.  A slot the tree does not name therefore holds no
link at all. -/
structure LinksAgree (L : LinkView) (cdt : CapDerivationTree) : Prop where
  childrenUnique : cdt.childrenUnique
  rootsNodup : cdt.rootChains.flatten.Nodup
  rootsParentless : cdt.rootsParentless
  parent : ∀ r, L r .parent = cdt.parentOf r
  firstChild : ∀ p, L p .firstChild = (cdt.childrenOf p).head?
  next : ∀ r, L r .next = SlotList.succIn (cdt.siblingsOf r) r
  prev : ∀ r, L r .prev = SlotList.predIn (cdt.siblingsOf r) r

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

theorem CapDerivationTree.childrenOf_length_le (cdt : CapDerivationTree) (p : SlotRef) :
    (cdt.childrenOf p).length ≤ cdt.edges.length := by
  unfold childrenOf; rw [List.length_map]; exact List.length_filter_le _ _

namespace LinksAgree

open CapDerivationTree

variable {L : LinkView} {cdt : CapDerivationTree}

theorem siblingsOf_nodup (h : LinksAgree L cdt) (r : SlotRef) : (cdt.siblingsOf r).Nodup :=
  CapDerivationTree.siblingsOf_nodup h.childrenUnique h.rootsNodup r

theorem mem_siblingsOf_self (h : LinksAgree L cdt) (r : SlotRef) : r ∈ cdt.siblingsOf r :=
  CapDerivationTree.mem_siblingsOf_self h.childrenUnique r

theorem siblingsOf_eq_of_mem (h : LinksAgree L cdt) {r x : SlotRef} (hx : x ∈ cdt.siblingsOf r) :
    cdt.siblingsOf x = cdt.siblingsOf r :=
  CapDerivationTree.siblingsOf_eq_of_mem h.childrenUnique h.rootsNodup h.rootsParentless hx

/-- A child's siblings are its parent's children. -/
theorem siblingsOf_of_mem_children (h : LinksAgree L cdt) {p r : SlotRef}
    (hr : r ∈ cdt.childrenOf p) : cdt.siblingsOf r = cdt.childrenOf p :=
  siblingsOf_of_parent ((mem_childrenOf_iff_parentOf h.childrenUnique p r).mp hr)

/-- **`x` follows `r` exactly when `r` precedes `x`.** -/
theorem next_eq_some_iff (h : LinksAgree L cdt) (r x : SlotRef) :
    L r .next = some x ↔ L x .prev = some r := by
  rw [h.next, h.prev]
  constructor
  · intro e
    rw [h.siblingsOf_eq_of_mem (SlotList.succIn_mem e)]
    exact (SlotList.succIn_eq_iff_predIn (h.siblingsOf_nodup r)).mp e
  · intro e
    rw [h.siblingsOf_eq_of_mem (SlotList.predIn_mem e)]
    exact (SlotList.succIn_eq_iff_predIn (h.siblingsOf_nodup x)).mpr e

/-- **`x` is `p`'s first child** exactly when `p` is its parent and nothing precedes it. -/
theorem firstChild_eq_some_iff (h : LinksAgree L cdt) (p x : SlotRef) :
    L p .firstChild = some x ↔ L x .parent = some p ∧ L x .prev = none := by
  rw [h.firstChild, h.parent, h.prev]
  constructor
  · intro e
    have hx := List.mem_of_mem_head? e
    refine ⟨(mem_childrenOf_iff_parentOf h.childrenUnique p x).mp hx, ?_⟩
    rw [h.siblingsOf_of_mem_children hx]
    exact (SlotList.predIn_eq_none_iff hx).mpr e
  · rintro ⟨e1, e2⟩
    have hx := (mem_childrenOf_iff_parentOf h.childrenUnique p x).mpr e1
    rw [h.siblingsOf_of_mem_children hx] at e2
    exact (SlotList.predIn_eq_none_iff hx).mp e2

theorem parent_eq_some_iff (h : LinksAgree L cdt) (r p : SlotRef) :
    L r .parent = some p ↔ r ∈ cdt.childrenOf p := by
  rw [h.parent, mem_childrenOf_iff_parentOf h.childrenUnique]

/-- **The children walk reads the tree's children**, with any fuel at least
their number (the tree's edge count is one). -/
theorem walk_children (h : LinksAgree L cdt) (p : SlotRef) {n : Nat}
    (hn : (cdt.childrenOf p).length ≤ n) : L.walk n (L p .firstChild) = cdt.childrenOf p := by
  rw [h.firstChild]
  refine LinkView.walk_of_succ (childrenOf_nodup h.childrenUnique p) (fun w hw => ?_) hn
  rw [h.next, h.siblingsOf_of_mem_children hw]

/-- The walk from a slot's first child, with fuel the tree's edge count, reads its children. -/
theorem walk_firstChild (h : LinksAgree L cdt) (n : SlotRef) {k : Nat}
    (hk : cdt.edges.length ≤ k) : L.walk k (L n .firstChild) = cdt.childrenOf n :=
  h.walk_children n (Nat.le_trans (cdt.childrenOf_length_le n) hk)

/-- A slot outside the tree has itself alone for siblings. -/
theorem siblingsOf_of_not_mentions {r : SlotRef} (hn : ¬ cdt.mentions r) :
    cdt.siblingsOf r = [r] := by
  rw [siblingsOf_of_root (parentOf_of_not_mentions hn)]
  exact SlotList.chainOf_of_not_mem (not_root_of_not_mentions hn)

/-- **A slot the tree does not name holds no link.** -/
theorem none_of_not_mentions (h : LinksAgree L cdt) {r : SlotRef} (hn : ¬ cdt.mentions r)
    (f : LinkField) : L r f = none := by
  cases f
  · rw [h.parent r, parentOf_of_not_mentions hn]
  · rw [h.firstChild r, childrenOf_of_not_mentions hn]; rfl
  · rw [h.next r, siblingsOf_of_not_mentions hn]; simp [SlotList.succIn]
  · rw [h.prev r, siblingsOf_of_not_mentions hn]; simp [SlotList.predIn, SlotList.predAux]

/-- A slot's sibling other than itself is a slot the tree names. -/
theorem mentions_of_sibling {r x : SlotRef} (hx : x ∈ cdt.siblingsOf r) (hxr : x ≠ r) :
    cdt.mentions x := by
  unfold siblingsOf at hx
  cases hP : cdt.parentOf r with
  | some p =>
    rw [hP] at hx
    obtain ⟨e, he, -, hc⟩ := (mem_childrenOf cdt p x).mp hx
    exact .inl ⟨e, he, .inr hc⟩
  | none =>
    rw [hP] at hx
    rcases SlotList.mem_chainOf hx with hm | e
    · exact .inr hm
    · exact absurd e hxr

/-- A slot's successor or predecessor is not itself. -/
theorem next_ne_self (h : LinksAgree L cdt) (r : SlotRef) : L r .next ≠ some r := by
  rw [h.next]; exact SlotList.succIn_ne_self (h.siblingsOf_nodup r)

theorem prev_ne_self (h : LinksAgree L cdt) (r : SlotRef) : L r .prev ≠ some r := by
  rw [h.prev]; exact SlotList.predIn_ne_self (h.siblingsOf_nodup r)

/-- **Every link names a slot the tree names.** -/
theorem target_mentions (h : LinksAgree L cdt) {r : SlotRef} {f : LinkField} {x : SlotRef}
    (hx : L r f = some x) : cdt.mentions x := by
  cases f
  · rw [h.parent r] at hx
    obtain ⟨e, he, hp, -⟩ := (parentOf_eq_some_iff h.childrenUnique x r).mp hx
    exact .inl ⟨e, he, .inl hp⟩
  · rw [h.firstChild r] at hx
    obtain ⟨e, he, -, hc⟩ := (mem_childrenOf cdt r x).mp (List.mem_of_mem_head? hx)
    exact .inl ⟨e, he, .inr hc⟩
  · have hne : x ≠ r := fun e => h.next_ne_self r (e ▸ hx)
    rw [h.next r] at hx
    exact mentions_of_sibling (SlotList.succIn_mem hx) hne
  · have hne : x ≠ r := fun e => h.prev_ne_self r (e ▸ hx)
    rw [h.prev r] at hx
    exact mentions_of_sibling (SlotList.predIn_mem hx) hne

/-- **An empty tree agrees with links that are all empty**: the state the
default state starts from. -/
theorem of_empty {L' : LinkView} {t : CapDerivationTree} (hE : t.edges = [])
    (hR : t.rootChains = []) (hL : ∀ r f, L' r f = none) : LinksAgree L' t := by
  have hn : ∀ r, ¬ t.mentions r := by
    rintro r (⟨e, he, -⟩ | hr)
    · rw [hE] at he; cases he
    · rw [hR] at hr; cases hr
  refine ⟨by unfold CapDerivationTree.childrenUnique; rw [hE]; exact List.nodup_nil,
    (by rw [hR]; exact List.nodup_nil), (fun r hr => by rw [hR] at hr; cases hr),
    fun r => ?_, fun p => ?_, fun r => ?_, fun r => ?_⟩
  · rw [hL, parentOf_of_not_mentions (hn r)]
  · rw [hL, childrenOf_of_not_mentions (hn p)]; rfl
  · rw [hL, siblingsOf_of_not_mentions (hn r)]; simp [SlotList.succIn]
  · rw [hL, siblingsOf_of_not_mentions (hn r)]; simp [SlotList.predIn, SlotList.predAux]

/-- An acyclic tree has no node that is its own parent. -/
theorem parentOf_ne_self_of_wf (h : LinksAgree L cdt) (hWF : cdt.edgeWellFounded) (n : SlotRef) :
    cdt.parentOf n ≠ some n := fun hp => by
  obtain ⟨e, he, hpe, hce⟩ := (parentOf_eq_some_iff h.childrenUnique n n).mp hp
  exact edgeWellFounded_no_self_edge hWF he (hpe.trans hce.symm)

end LinksAgree

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

/-- **Adding an edge to a slot outside the tree**, with `addChild`'s link
writes, keeps the links agreeing: the new slot becomes its source's first
child, which is right after the source in the tree's preorder. -/
theorem addChild (h : LinksAgree L cdt) {p c : SlotRef} (op : DerivationOp)
    (hc : ¬ cdt.mentions c) (hpc : p ≠ c) :
    LinksAgree (L.addChild p c) (cdt.addEdge p c op) := by
  have hU := h.childrenUnique
  have hcN : cdt.parentOf c = none := parentOf_of_not_mentions hc
  have hNotChild : ∀ q, c ∉ cdt.childrenOf q := not_mem_childrenOf_of_not_mentions hc
  have hcR : c ∉ cdt.rootChains.flatten := not_root_of_not_mentions hc
  have hcp : c ≠ p := fun e => hpc e.symm
  have hU' : (cdt.addEdge p c op).childrenUnique := by
    unfold CapDerivationTree.childrenUnique; rw [CapDerivationTree.addEdge_edges]
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hU⟩
    obtain ⟨e, he, hec⟩ := List.mem_map.mp hm
    exact hNotChild e.parent ((mem_childrenOf cdt _ _).mpr ⟨e, he, rfl, hec⟩)
  -- the siblings after the add
  have hRC : ∀ r, (cdt.addEdge p c op).rootChain r = cdt.rootChain r := fun r => rfl
  have hSibC : (cdt.addEdge p c op).siblingsOf c = c :: cdt.childrenOf p := by
    rw [siblingsOf_of_parent (by rw [parentOf_addEdge, if_pos rfl]), childrenOf_addEdge, if_pos rfl]
  have hSib : ∀ r, r ≠ c → (cdt.addEdge p c op).siblingsOf r =
      if cdt.parentOf r = some p then c :: cdt.childrenOf p else cdt.siblingsOf r := by
    intro r hr
    unfold siblingsOf
    rw [parentOf_addEdge, if_neg hr]
    cases hP : cdt.parentOf r with
    | none => simp [hRC]
    | some q =>
      simp only [childrenOf_addEdge, Option.some.injEq]
      by_cases hq : q = p
      · simp [hq]
      · simp [hq]
  refine ⟨hU', h.rootsNodup, fun r hr => ?_, fun r => ?_, fun q => ?_, fun r => ?_, fun r => ?_⟩
  · have hrc : r ≠ c := fun e => hcR (e ▸ hr)
    rw [parentOf_addEdge, if_neg hrc]; exact h.rootsParentless r hr
  · rw [addChild_parent, parentOf_addEdge]
    split
    · rfl
    · exact h.parent r
  · rw [addChild_firstChild, childrenOf_addEdge]
    by_cases hq : q = p
    · simp [hq]
    · simp only [if_neg hq]; exact h.firstChild q
  · rw [addChild_next]
    by_cases hr : r = c
    · subst hr
      rw [if_pos rfl, hSibC, SlotList.succIn_cons, if_pos rfl]
      exact h.firstChild p
    · rw [if_neg hr, hSib r hr, h.next r]
      split
      · next hP => rw [SlotList.succIn_cons, if_neg (Ne.symm hr), siblingsOf_of_parent hP]
      · rfl
  · rw [addChild_prev, h.firstChild p]
    by_cases hr : r = c
    · subst hr
      have : (cdt.childrenOf p).head? ≠ some r := fun e => hNotChild p (List.mem_of_mem_head? e)
      rw [if_neg this, if_pos rfl, hSibC, SlotList.predIn_cons, if_pos rfl]
    · rw [if_neg hr, hSib r hr]
      by_cases hhd : (cdt.childrenOf p).head? = some r
      · rw [if_pos hhd]
        have hmem := List.mem_of_mem_head? hhd
        rw [if_pos ((mem_childrenOf_iff_parentOf hU p r).mp hmem), SlotList.predIn_cons,
          if_neg (Ne.symm hr), if_pos hhd]
      · rw [if_neg hhd, h.prev r]
        split
        · next hP =>
          rw [SlotList.predIn_cons, if_neg (Ne.symm hr), if_neg hhd, siblingsOf_of_parent hP]
        · rfl

end LinksAgree

namespace LinkView

/-- **Link `r` after `t` in a root chain** (`t` the chain's last slot, if any),
as `appendRoot r` lays it: `r` takes `t` as previous and `t` takes `r` as next. -/
def appendRoot (L : LinkView) (t : Option SlotRef) (r : SlotRef) : LinkView :=
  match t with
  | some x => (L.set r .prev (some x)).set x .next (some r)
  | none => L

theorem appendRoot_apply (L : LinkView) (t : Option SlotRef) (r x : SlotRef) (f : LinkField) :
    L.appendRoot t r x f =
      if f = .prev ∧ x = r ∧ t.isSome then t
      else if f = .next ∧ some x = t then some r else L x f := by
  unfold appendRoot
  cases t with
  | none => simp
  | some y =>
    simp only [set]
    by_cases h1 : x = y <;> by_cases h2 : x = r <;> cases f <;> simp [h1, h2]

end LinkView


namespace CapDerivationTree

/-- The first root chain (empty when there is none) — where `appendRoot` lays its slot. -/
noncomputable def firstChain (cdt : CapDerivationTree) : List SlotRef :=
  cdt.rootChains.head?.getD []

theorem appendRoot_rootChains_eq (cdt : CapDerivationTree) (r : SlotRef) :
    (cdt.appendRoot r).rootChains = (cdt.firstChain ++ [r]) :: cdt.rootChains.tail := by
  rw [appendRoot_rootChains]; unfold firstChain
  cases cdt.rootChains <;> rfl

theorem rootChains_flatten_eq (cdt : CapDerivationTree) :
    cdt.rootChains.flatten = cdt.firstChain ++ cdt.rootChains.tail.flatten := by
  unfold firstChain; cases cdt.rootChains <;> simp

theorem rootChain_of_mem_firstChain {cdt : CapDerivationTree} (hnd : cdt.rootChains.flatten.Nodup)
    {x : SlotRef} (hx : x ∈ cdt.firstChain) : cdt.rootChain x = cdt.firstChain := by
  unfold firstChain at hx ⊢; unfold rootChain
  cases hCs : cdt.rootChains with
  | nil => rw [hCs] at hx; cases hx
  | cons D T =>
    rw [hCs] at hx hnd
    simp only [List.head?_cons, Option.getD_some] at hx ⊢
    exact SlotList.chainOf_of_mem hnd (List.mem_cons_self ..) hx

theorem parentOf_appendRoot (cdt : CapDerivationTree) (r x : SlotRef) :
    (cdt.appendRoot r).parentOf x = cdt.parentOf x := rfl

theorem childrenOf_appendRoot (cdt : CapDerivationTree) (r x : SlotRef) :
    (cdt.appendRoot r).childrenOf x = cdt.childrenOf x := rfl

end CapDerivationTree

namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

/-- **Appending a slot outside the tree to the first root chain**, linked after
the chain's last slot `t`, keeps the links agreeing: how boot lays its
capabilities in one chain. -/
theorem appendRoot (h : LinksAgree L cdt) {r : SlotRef} (hr : ¬ cdt.mentions r)
    {t : Option SlotRef} (ht : t = cdt.firstChain.getLast?) :
    LinksAgree (L.appendRoot t r) (cdt.appendRoot r) := by
  have hrR : r ∉ cdt.rootChains.flatten := not_root_of_not_mentions hr
  have hFl := cdt.rootChains_flatten_eq
  have hND := h.rootsNodup
  rw [hFl] at hND hrR
  have hrD : r ∉ cdt.firstChain := fun hm => hrR (List.mem_append_left _ hm)
  have hC := appendRoot_rootChains_eq cdt r
  have hND' : (cdt.appendRoot r).rootChains.flatten.Nodup := by
    rw [hC, List.flatten_cons, List.append_assoc]
    refine (List.Perm.nodup_iff ?_).mpr (List.nodup_cons.mpr ⟨hrR, hND⟩)
    refine (List.perm_middle (l₁ := cdt.firstChain) (a := r)).trans ?_
    simp
  have hDmem : cdt.firstChain ++ [r] ∈ (cdt.appendRoot r).rootChains := by
    rw [hC]; exact List.mem_cons_self ..
  -- the root chain of a parentless slot, after the append
  have hRC : ∀ x, (cdt.appendRoot r).rootChain x =
      if x = r ∨ x ∈ cdt.firstChain then cdt.firstChain ++ [r] else cdt.rootChain x := by
    intro x
    unfold rootChain
    split
    · next hx =>
      refine SlotList.chainOf_of_mem hND' hDmem ?_
      rcases hx with rfl | hx
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ hx
    · next hx =>
      have hxr : x ≠ r := fun e => hx (.inl e)
      have hxD : x ∉ cdt.firstChain := fun e => hx (.inr e)
      rcases SlotList.chainOf_cases cdt.rootChains x with ⟨E, hE, hxE, e⟩ | ⟨hxn, e⟩
      · rw [e]
        have hEt : E ∈ cdt.rootChains.tail := by
          unfold firstChain at hxD
          cases hCs : cdt.rootChains with
          | nil => rw [hCs] at hE; cases hE
          | cons D T =>
            rw [hCs] at hE hxD
            rcases List.mem_cons.mp hE with rfl | hE
            · exact absurd hxE hxD
            · exact hE
        exact SlotList.chainOf_of_mem hND' (by rw [hC]; exact List.mem_cons_of_mem _ hEt) hxE
      · rw [e]
        refine SlotList.chainOf_of_not_mem fun hm => ?_
        rw [hC, List.flatten_cons] at hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact hxD hm
          · exact hxr (List.mem_singleton.mp hm)
        · rw [hFl] at hxn; exact hxn (List.mem_append_right _ hm)
  have hSib : ∀ x, (cdt.appendRoot r).siblingsOf x =
      if cdt.parentOf x = none ∧ (x = r ∨ x ∈ cdt.firstChain) then cdt.firstChain ++ [r]
      else cdt.siblingsOf x := by
    intro x
    unfold siblingsOf
    rw [parentOf_appendRoot]
    cases hP : cdt.parentOf x with
    | some p => simp [childrenOf_appendRoot]
    | none => simp only [true_and]; rw [hRC]
  have hrN : cdt.parentOf r = none := parentOf_of_not_mentions hr
  have hDpl : ∀ x ∈ cdt.firstChain, cdt.parentOf x = none := fun x hx =>
    h.rootsParentless x (by rw [hFl]; exact List.mem_append_left _ hx)
  have hDnd : (cdt.firstChain ++ [r]).Nodup := by
    rw [hC, List.flatten_cons] at hND'; exact hND'.sublist (List.sublist_append_left ..)
  have hDnd0 : cdt.firstChain.Nodup := hDnd.sublist (List.sublist_append_left ..)
  have htD : ∀ x, t = some x → x ∈ cdt.firstChain := fun x e => by
    rw [ht] at e; exact List.mem_of_getLast? e
  refine ⟨h.childrenUnique, hND', fun x hx => ?_, fun x => ?_, fun p => ?_, fun x => ?_, fun x => ?_⟩
  · rw [parentOf_appendRoot]
    rw [hC, List.flatten_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hDpl x hx
      · rw [List.mem_singleton.mp hx]; exact hrN
    · exact h.rootsParentless x (by rw [hFl]; exact List.mem_append_right _ hx)
  · rw [appendRoot_apply, parentOf_appendRoot]; simp only [reduceCtorEq, false_and, if_false]
    exact h.parent x
  · rw [appendRoot_apply, childrenOf_appendRoot]; simp only [reduceCtorEq, false_and, if_false]
    exact h.firstChild p
  · rw [appendRoot_apply, hSib]
    simp only [reduceCtorEq, false_and, if_false, true_and]
    by_cases hx : cdt.parentOf x = none ∧ (x = r ∨ x ∈ cdt.firstChain)
    · rw [if_pos hx]
      rcases hx.2 with rfl | hxD
      · have : ¬ some x = t := fun e => hrD (htD x e.symm)
        rw [if_neg this, h.none_of_not_mentions hr, SlotList.succIn_append, if_neg hrD]
        simp [SlotList.succIn]
      · rw [SlotList.succIn_append, if_pos hxD]
        by_cases htx : t = some x
        · rw [if_pos htx.symm, (SlotList.succIn_eq_none_iff hDnd0 hxD).mpr (ht ▸ htx)]; rfl
        · rw [if_neg (fun e => htx e.symm), h.next, siblingsOf_of_root hx.1]
          have hRx : cdt.rootChain x = cdt.firstChain := rootChain_of_mem_firstChain h.rootsNodup hxD
          rw [hRx]
          have hne : SlotList.succIn cdt.firstChain x ≠ none := fun e =>
            htx (by rw [ht]; exact ((SlotList.succIn_eq_none_iff hDnd0 hxD).mp e))
          cases hS : SlotList.succIn cdt.firstChain x with
          | none => exact absurd hS hne
          | some y => rfl
    · rw [if_neg hx]
      have htx : ¬ some x = t := fun e => hx ⟨hDpl x (htD x e.symm), .inr (htD x e.symm)⟩
      rw [if_neg htx]; exact h.next x
  · rw [appendRoot_apply, hSib]
    simp only [true_and]
    by_cases hx : cdt.parentOf x = none ∧ (x = r ∨ x ∈ cdt.firstChain)
    · rw [if_pos hx]
      rcases hx.2 with rfl | hxD
      · rw [SlotList.predIn_append, if_neg hrD, SlotList.predAux_of_head _ rfl, ← ht]
        cases t with
        | none => simp only [Option.isSome_none, and_false, if_false, reduceCtorEq]
                  exact h.none_of_not_mentions hr .prev
        | some y => simp
      · have hxr : x ≠ r := fun e => hrD (e ▸ hxD)
        simp only [hxr, false_and, if_false, reduceCtorEq]
        rw [SlotList.predIn_append, if_pos hxD, h.prev, siblingsOf_of_root hx.1]
        rw [rootChain_of_mem_firstChain h.rootsNodup hxD]
    · rw [if_neg hx]
      have hxr : x ≠ r := fun e => hx ⟨e ▸ hrN, .inl e⟩
      simp only [hxr, false_and, if_false, reduceCtorEq]
      exact h.prev x

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

/-- **Clear all four links of `n`.** -/
def clearLinks (L : LinkView) (n : SlotRef) : LinkView :=
  (((L.set n .parent none).set n .firstChild none).set n .next none).set n .prev none

theorem clearLinks_apply (L : LinkView) (n r : SlotRef) (f : LinkField) :
    L.clearLinks n r f = if r = n then none else L r f := by
  unfold clearLinks
  by_cases h : r = n
  · subst h; cases f <;> simp [set]
  · simp [set, h]

end LinkView


/-! ### The tree after a splice

`spliceNode n` puts `n`'s children in `n`'s place among its siblings, so each
slot's siblings after it are its siblings before it, with `n` replaced by its
children wherever `n` was. -/

namespace CapDerivationTree

/-- The children of `q` an edge list names, in order. -/
def kidsIn (es : List CapDerivationEdge) (q : SlotRef) : List SlotRef :=
  (es.filter (·.isParentOf q)).map (·.child)

theorem childrenOf_eq_kidsIn (cdt : CapDerivationTree) (q : SlotRef) :
    cdt.childrenOf q = kidsIn cdt.edges q := rfl

theorem kidsIn_append (l₁ l₂ : List CapDerivationEdge) (q : SlotRef) :
    kidsIn (l₁ ++ l₂) q = kidsIn l₁ q ++ kidsIn l₂ q := by
  simp [kidsIn, List.filter_append]

theorem kidsIn_cons (e : CapDerivationEdge) (l : List CapDerivationEdge) (q : SlotRef) :
    kidsIn (e :: l) q = if e.parent = q then e.child :: kidsIn l q else kidsIn l q := by
  unfold kidsIn
  by_cases h : e.parent = q
  · simp [CapDerivationEdge.isParentOf, h]
  · simp [CapDerivationEdge.isParentOf, h]

theorem kidsIn_withoutNodeEdges_self (l : List CapDerivationEdge) (n : SlotRef) :
    kidsIn (withoutNodeEdges l n) n = [] := by
  unfold kidsIn withoutNodeEdges
  rw [List.filter_filter, List.filter_eq_nil_iff.mpr]
  · rfl
  · intro e _
    simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf]
    intro h; exact absurd h

theorem kidsIn_withoutNodeEdges {l : List CapDerivationEdge} {n q : SlotRef} (hq : q ≠ n)
    (hl : ∀ e ∈ l, e.child ≠ n) : kidsIn (withoutNodeEdges l n) q = kidsIn l q := by
  unfold kidsIn withoutNodeEdges
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro e he
  have hc := hl e he
  by_cases hp : e.parent = q
  · have : e.parent ≠ n := fun h => hq (hp ▸ h)
    simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf, hp, hq, hc]
  · simp [CapDerivationEdge.isParentOf, hp]

theorem kidsIn_reparentEdges (u : SlotRef) (l : List CapDerivationEdge) (q : SlotRef) :
    kidsIn (reparentEdges u l) q = if u = q then l.map (·.child) else [] := by
  unfold kidsIn reparentEdges
  by_cases h : u = q
  · subst h
    simp only [CapDerivationEdge.isParentOf, List.filter_map, Function.comp_def, decide_true,
      if_true, List.map_map]
    rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
  · rw [if_neg h, List.filter_eq_nil_iff.mpr]
    · rfl
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨e', -, rfl⟩ := he
      simp [CapDerivationEdge.isParentOf, h]

theorem mem_kidsIn {l : List CapDerivationEdge} {q x : SlotRef} :
    x ∈ kidsIn l q ↔ ∃ e ∈ l, e.parent = q ∧ e.child = x := by
  simp only [kidsIn, List.mem_map, List.mem_filter, CapDerivationEdge.isParentOf,
    decide_eq_true_eq, and_assoc]

/-- The tree's first parent edge of `n`, when it has one: the edges split
around it, none before it naming `n` as child. -/
theorem find_parent_split {cdt : CapDerivationTree} {n : SlotRef} {up : CapDerivationEdge}
    (hF : cdt.edges.find? (·.isChildOf n) = some up) :
    up.child = n ∧ ∃ pre post, cdt.edges = pre ++ up :: post ∧ ∀ e ∈ pre, e.child ≠ n := by
  obtain ⟨hu, pre, post, he, hpre⟩ := List.find?_eq_some_iff_append.mp hF
  refine ⟨by simpa [CapDerivationEdge.isChildOf] using hu, pre, post, he, fun e he' => ?_⟩
  have := hpre e he'
  simpa [CapDerivationEdge.isChildOf] using this

/-- Under unique children, nothing after a slot's parent edge names it as child. -/
theorem post_child_ne {cdt : CapDerivationTree} (hU : cdt.childrenUnique) {n : SlotRef}
    {pre post : List CapDerivationEdge} {up : CapDerivationEdge} (he : cdt.edges = pre ++ up :: post)
    (hu : up.child = n) : ∀ e ∈ post, e.child ≠ n := by
  intro e he' hc
  unfold childrenUnique at hU
  rw [he, List.map_append, List.map_cons, List.nodup_append] at hU
  have := (List.nodup_cons.mp hU.2.1).1
  exact this (List.mem_map.mpr ⟨e, he', hc.trans hu.symm⟩)

theorem parentOf_eq_of_find {cdt : CapDerivationTree} {n : SlotRef} {up : CapDerivationEdge}
    (hF : cdt.edges.find? (·.isChildOf n) = some up) : cdt.parentOf n = some up.parent := by
  unfold parentOf; rw [hF]; rfl

theorem not_mem_childrenOf_self {cdt : CapDerivationTree} (hU : cdt.childrenUnique) {n : SlotRef}
    (hs : cdt.parentOf n ≠ some n) : n ∉ cdt.childrenOf n := fun h =>
  hs ((mem_childrenOf_iff_parentOf hU n n).mp h)

/-- **The children after a splice**: none for `n`; for every other slot, its
children with `n` replaced in place by `n`'s children. -/
theorem childrenOf_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique) {n : SlotRef}
    (hs : cdt.parentOf n ≠ some n) (q : SlotRef) :
    (cdt.spliceNode n).childrenOf q =
      if q = n then [] else replaceSlot n (cdt.childrenOf n) (cdt.childrenOf q) := by
  rw [childrenOf_eq_kidsIn, spliceNode_edges_eq]
  unfold spliceEdges
  cases hF : cdt.edges.find? (·.isChildOf n) with
  | none =>
    have hno : ∀ e ∈ cdt.edges, e.child ≠ n := fun e he hc => by
      have := List.find?_eq_none.mp hF e he
      simp [CapDerivationEdge.isChildOf, hc] at this
    rw [spliceEdgesFrom_of_no_parent _ _ _ hno]
    split
    · next hq => subst hq; exact kidsIn_withoutNodeEdges_self _ _
    · next hq =>
      rw [kidsIn_withoutNodeEdges hq hno, replaceSlot_of_not_mem]
      · rfl
      · intro hm
        obtain ⟨e, he, -, hc⟩ := mem_kidsIn.mp hm
        exact hno e he hc
  | some up =>
    obtain ⟨hu, pre, post, he, hpre⟩ := find_parent_split hF
    have hpost := post_child_ne hU he hu
    have hP := parentOf_eq_of_find hF
    have hun : up.parent ≠ n := fun e => hs (by rw [hP, e])
    have hpreN : n ∉ kidsIn pre q := fun hm => by
      obtain ⟨e, he', -, hc⟩ := mem_kidsIn.mp hm; exact hpre e he' hc
    have hpn : n ∉ kidsIn post q := fun hm => by
      obtain ⟨e, he', -, hc⟩ := mem_kidsIn.mp hm; exact hpost e he' hc
    rw [he, spliceEdgesFrom_split _ _ pre up post hpre hu, kidsIn_append, kidsIn_append,
      kidsIn_reparentEdges, ← he]
    by_cases hq : q = n
    · rw [hq, if_pos rfl, kidsIn_withoutNodeEdges_self, kidsIn_withoutNodeEdges_self, if_neg hun]; rfl
    · rw [if_neg hq, kidsIn_withoutNodeEdges hq hpre, kidsIn_withoutNodeEdges hq hpost,
        childrenOf_eq_kidsIn cdt q, he, kidsIn_append, kidsIn_cons, replaceSlot_append,
        replaceSlot_of_not_mem hpreN, ← he]
      by_cases hq' : up.parent = q
      · rw [if_pos hq', if_pos hq', hu, replaceSlot_cons_self, replaceSlot_of_not_mem hpn]
        simp [childrenOf, kidsIn, List.append_assoc]
      · rw [if_neg hq', if_neg hq', replaceSlot_of_not_mem hpn]; simp


/-- A run of edges none of which names `n` as child, with `n`'s child edges
taken out, then put back, is the run up to order. -/
private theorem withoutNode_perm {l : List CapDerivationEdge} {n : SlotRef}
    (hl : ∀ e ∈ l, e.child ≠ n) :
    ((withoutNodeEdges l n).map (·.child) ++ (l.filter (·.isParentOf n)).map (·.child)).Perm
      (l.map (·.child)) := by
  have e : withoutNodeEdges l n = l.filter (fun e => !e.isParentOf n) := by
    unfold withoutNodeEdges
    apply List.filter_congr
    intro x hx
    have : x.isChildOf n = false := by simp [CapDerivationEdge.isChildOf, hl x hx]
    simp [this]
  rw [e, ← List.map_append]
  exact (List.perm_append_comm.trans (List.filter_append_perm _ l)).map _

theorem reparentEdges_map_child (u : SlotRef) (l : List CapDerivationEdge) :
    (reparentEdges u l).map (·.child) = l.map (·.child) := by
  simp [reparentEdges, Function.comp_def]

/-- **The splice keeps children unique.** -/
theorem childrenUnique_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    {n : SlotRef} (hs : cdt.parentOf n ≠ some n) : (cdt.spliceNode n).childrenUnique := by
  unfold childrenUnique; rw [spliceNode_edges_eq]
  unfold spliceEdges
  cases hF : cdt.edges.find? (·.isChildOf n) with
  | none =>
    have hno : ∀ e ∈ cdt.edges, e.child ≠ n := fun e he hc => by
      have := List.find?_eq_none.mp hF e he
      simp [CapDerivationEdge.isChildOf, hc] at this
    rw [spliceEdgesFrom_of_no_parent _ _ _ hno]
    exact hU.sublist (List.filter_sublist.map _)
  | some up =>
    obtain ⟨hu, pre, post, he, hpre⟩ := find_parent_split hF
    have hpost := post_child_ne hU he hu
    have hun : up.parent ≠ n := fun e => hs (by rw [parentOf_eq_of_find hF, e])
    have hK : cdt.edges.filter (·.isParentOf n) =
        pre.filter (·.isParentOf n) ++ post.filter (·.isParentOf n) := by
      rw [he, List.filter_append, List.filter_cons]
      have : up.isParentOf n = false := by simp [CapDerivationEdge.isParentOf, hun]
      simp [this]
    rw [he, spliceEdgesFrom_split _ _ pre up post hpre hu, ← he, hK]
    unfold childrenUnique at hU
    rw [he, List.map_append, List.map_cons, hu] at hU
    have hU2 := (List.perm_middle.nodup_iff.mp hU)
    have hU3 := (List.nodup_cons.mp hU2).2
    refine (List.Perm.nodup_iff ?_).mpr hU3
    simp only [List.map_append, reparentEdges_map_child]
    have h1 := withoutNode_perm hpre
    have h2 := withoutNode_perm hpost
    have : ((withoutNodeEdges pre n).map (·.child) ++ ((pre.filter (·.isParentOf n)).map (·.child) ++
        (post.filter (·.isParentOf n)).map (·.child)) ++ (withoutNodeEdges post n).map (·.child)) =
        ((withoutNodeEdges pre n).map (·.child) ++ (pre.filter (·.isParentOf n)).map (·.child)) ++
        ((post.filter (·.isParentOf n)).map (·.child) ++ (withoutNodeEdges post n).map (·.child)) := by
      simp [List.append_assoc]
    rw [this]
    exact h1.append (List.perm_append_comm.trans h2)

/-- **The parent after a splice**: none for `n`; `n`'s parent for its children;
every other slot's own. -/
theorem parentOf_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique) {n : SlotRef}
    (hs : cdt.parentOf n ≠ some n) (r : SlotRef) :
    (cdt.spliceNode n).parentOf r =
      if r = n then none else if r ∈ cdt.childrenOf n then cdt.parentOf n else cdt.parentOf r := by
  have hU' := childrenUnique_spliceNode hU hs
  have hnK := not_mem_childrenOf_self hU hs
  apply Option.ext
  intro p
  rw [← mem_childrenOf_iff_parentOf hU', childrenOf_spliceNode hU hs]
  by_cases hpn : p = n
  · rw [hpn, if_pos rfl]
    simp only [List.not_mem_nil, false_iff]
    intro e
    split at e
    · cases e
    · split at e
      · exact hs e
      · next hr => exact hr ((mem_childrenOf_iff_parentOf hU _ _).mpr e)
  · rw [if_neg hpn, mem_replaceSlot]
    by_cases hrn : r = n
    · subst hrn
      simp only [if_true, ne_eq, not_true_eq_false, and_false, false_or, reduceCtorEq, iff_false,
        not_and]
      intro _ h; exact hnK h
    · rw [if_neg hrn]
      by_cases hrK : r ∈ cdt.childrenOf n
      · rw [if_pos hrK, mem_childrenOf_iff_parentOf hU, mem_childrenOf_iff_parentOf hU,
          (mem_childrenOf_iff_parentOf hU _ _).mp hrK]
        constructor
        · rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact absurd (Option.some.inj h) (Ne.symm hpn)
          · exact h
        · intro h; exact .inr ⟨h, hrK⟩
      · rw [if_neg hrK, mem_childrenOf_iff_parentOf hU]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd h hrK
        · intro h; exact .inl ⟨h, hrn⟩

/-- Whether `n` has a parent edge is whether it has a parent. -/
theorem hasParentEdge_eq_true_iff (cdt : CapDerivationTree) (n : SlotRef) :
    hasParentEdge cdt.edges n = true ↔ cdt.parentOf n ≠ none := by
  rw [ne_eq, parentOf_eq_none_iff, ← hasParentEdge_eq_false_iff]
  cases hasParentEdge cdt.edges n <;> simp

/-- **The root chains after a splice**: unchanged when `n` has a parent; the
chains `spliceRootChains` lays when it has none. -/
theorem spliceNode_rootChains_of_parent {cdt : CapDerivationTree} (hR : cdt.rootsParentless)
    {n : SlotRef} (hp : cdt.parentOf n ≠ none) :
    (cdt.spliceNode n).rootChains = cdt.rootChains := by
  rw [spliceNode_rootChains, if_pos ((hasParentEdge_eq_true_iff cdt n).mpr hp)]
  conv => rhs; rw [← List.map_id cdt.rootChains]
  apply List.map_congr_left
  intro c hc
  exact replaceSlot_of_not_mem fun hn => hp (hR n (List.mem_flatten.mpr ⟨c, hc, hn⟩))

theorem spliceNode_rootChains_of_root {cdt : CapDerivationTree} {n : SlotRef}
    (hp : cdt.parentOf n = none) :
    (cdt.spliceNode n).rootChains = spliceRootChains cdt.rootChains n (cdt.childrenOf n) := by
  rw [spliceNode_rootChains, if_neg]
  rw [hasParentEdge_eq_true_iff]; exact fun h => h hp

theorem flatten_map_replaceSlot (n : SlotRef) (m : List SlotRef) :
    ∀ cs : List (List SlotRef), (cs.map (replaceSlot n m)).flatten = replaceSlot n m cs.flatten
  | [] => rfl
  | c :: cs => by
    rw [List.map_cons, List.flatten_cons, List.flatten_cons, replaceSlot_append,
      flatten_map_replaceSlot n m cs]

/-- Replacing a member of a duplicate-free list by a duplicate-free run that
shares nothing with it keeps it duplicate-free, and splits it around the run. -/
theorem replaceSlot_split {l : List SlotRef} {n : SlotRef} (hnd : l.Nodup) (hn : n ∈ l) :
    ∃ a b, l = a ++ n :: b ∧ n ∉ a ∧ n ∉ b ∧ ∀ m, replaceSlot n m l = a ++ m ++ b := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hn
  have hnd' := List.perm_middle.nodup_iff.mp hnd
  have hna : n ∉ a := fun h => (List.nodup_cons.mp hnd').1 (List.mem_append_left _ h)
  have hnb : n ∉ b := fun h => (List.nodup_cons.mp hnd').1 (List.mem_append_right _ h)
  refine ⟨a, b, rfl, hna, hnb, fun m => ?_⟩
  rw [replaceSlot_append, replaceSlot_cons_self, replaceSlot_of_not_mem hna,
    replaceSlot_of_not_mem hnb, List.append_assoc]

theorem replaceSlot_nodup {l m : List SlotRef} {n : SlotRef} (hnd : l.Nodup) (hm : m.Nodup)
    (hdis : ∀ x ∈ m, x ∉ l) : (replaceSlot n m l).Nodup := by
  by_cases hn : n ∈ l
  · obtain ⟨a, b, rfl, -, -, e⟩ := replaceSlot_split hnd hn
    rw [e]
    have hab := (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hnd)).2
    have hp : (a ++ m ++ b).Perm (m ++ (a ++ b)) := by
      have := (List.perm_append_comm (l₁ := a) (l₂ := m)).append_right b
      simpa [List.append_assoc] using this
    refine hp.nodup_iff.mpr (List.nodup_append.mpr ⟨hm, hab, fun x hx y hy e => ?_⟩)
    subst e
    exact hdis x hx (by
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ hy
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy))
  · rw [replaceSlot_of_not_mem hn]; exact hnd


/-- `n`'s siblings with `n` replaced, in place, by its children: the siblings of
each of them after the splice. -/
noncomputable def spliceSiblings (cdt : CapDerivationTree) (n : SlotRef) : List SlotRef :=
  replaceSlot n (cdt.childrenOf n) (cdt.siblingsOf n)

/-- A child of `n` is in no root chain. -/
theorem child_not_root {cdt : CapDerivationTree} (hU : cdt.childrenUnique) (hR : cdt.rootsParentless)
    {n x : SlotRef} (hx : x ∈ cdt.childrenOf n) : x ∉ cdt.rootChains.flatten := fun hm => by
  have := hR x hm
  rw [(mem_childrenOf_iff_parentOf hU n x).mp hx] at this; cases this

theorem rootsNodup_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (hnd : cdt.rootChains.flatten.Nodup) (hR : cdt.rootsParentless) (n : SlotRef) :
    (cdt.spliceNode n).rootChains.flatten.Nodup := by
  have hKd : ∀ x ∈ cdt.childrenOf n, x ∉ cdt.rootChains.flatten := fun x hx =>
    child_not_root hU hR hx
  by_cases hp : cdt.parentOf n = none
  · rw [spliceNode_rootChains_of_root hp]
    unfold spliceRootChains
    split
    · rw [flatten_map_replaceSlot]
      exact replaceSlot_nodup hnd (childrenOf_nodup hU n) hKd
    · split
      · exact hnd
      · rw [List.flatten_append, List.flatten_singleton]
        exact List.nodup_append.mpr ⟨hnd, childrenOf_nodup hU n,
          fun a ha b hb e => hKd b hb (e ▸ ha)⟩
  · rw [spliceNode_rootChains_of_parent hR hp]; exact hnd

theorem rootsParentless_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (hR : cdt.rootsParentless) {n : SlotRef} (hs : cdt.parentOf n ≠ some n) :
    (cdt.spliceNode n).rootsParentless := by
  intro x hx
  rw [parentOf_spliceNode hU hs]
  split
  · rfl
  · next hxn =>
    by_cases hp : cdt.parentOf n = none
    · rw [spliceNode_rootChains_of_root hp] at hx
      rcases mem_flatten_spliceRootChains hx with ⟨hx, -⟩ | hx
      · rw [if_neg (child_not_root hU hR · hx)]; exact hR x hx
      · rw [if_pos hx]; exact hp
    · rw [spliceNode_rootChains_of_parent hR hp] at hx
      rw [if_neg (child_not_root hU hR · hx)]; exact hR x hx

/-- After the splice `n` is no one's sibling. -/
theorem siblingsOf_spliceNode_self {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (hR : cdt.rootsParentless) {n : SlotRef} (hs : cdt.parentOf n ≠ some n) :
    (cdt.spliceNode n).siblingsOf n = [n] := by
  rw [siblingsOf_of_root (by rw [parentOf_spliceNode hU hs, if_pos rfl])]
  unfold rootChain
  refine SlotList.chainOf_of_not_mem fun hm => ?_
  by_cases hp : cdt.parentOf n = none
  · rw [spliceNode_rootChains_of_root hp] at hm
    rcases mem_flatten_spliceRootChains hm with ⟨-, h⟩ | h
    · exact h rfl
    · exact not_mem_childrenOf_self hU hs h
  · rw [spliceNode_rootChains_of_parent hR hp] at hm
    exact hp (hR n hm)

/-- **The siblings after a splice**: `n`'s siblings, with `n` replaced in place
by its children, for each of them; every other slot's own. -/
theorem siblingsOf_spliceNode {cdt : CapDerivationTree} (hU : cdt.childrenUnique)
    (hnd : cdt.rootChains.flatten.Nodup) (hR : cdt.rootsParentless) {n : SlotRef}
    (hs : cdt.parentOf n ≠ some n) {r : SlotRef} (hr : r ≠ n) :
    (cdt.spliceNode n).siblingsOf r =
      if r ∈ cdt.spliceSiblings n then cdt.spliceSiblings n else cdt.siblingsOf r := by
  have hU' := childrenUnique_spliceNode hU hs
  have hnd' := rootsNodup_spliceNode hU hnd hR n
  have hP' : (cdt.spliceNode n).parentOf r =
      if r ∈ cdt.childrenOf n then cdt.parentOf n else cdt.parentOf r := by
    rw [parentOf_spliceNode hU hs, if_neg hr]
  have hChq : ∀ q, q ≠ n → cdt.parentOf n ≠ some q →
      (cdt.spliceNode n).childrenOf q = cdt.childrenOf q := fun q hq hnq => by
    rw [childrenOf_spliceNode hU hs, if_neg hq, replaceSlot_of_not_mem]
    exact fun hm => hnq ((mem_childrenOf_iff_parentOf hU q n).mp hm)
  have hnS : n ∈ cdt.siblingsOf n := mem_siblingsOf_self hU n
  have hKS : ∀ x ∈ cdt.childrenOf n, x ∈ cdt.spliceSiblings n := fun x hx =>
    mem_replaceSlot.mpr (.inr ⟨hnS, hx⟩)
  -- the parent case of `r` outside the spliced run
  have hOut : r ∉ cdt.spliceSiblings n → ∀ q, cdt.parentOf r = some q →
      (cdt.spliceNode n).siblingsOf r = cdt.siblingsOf r := by
    intro hrS q hq
    have hrK : r ∉ cdt.childrenOf n := fun h => hrS (hKS r h)
    have hqn : q ≠ n := fun e => hrK ((mem_childrenOf_iff_parentOf hU n r).mpr (e ▸ hq))
    have hnq : cdt.parentOf n ≠ some q := fun e => by
      apply hrS
      refine mem_replaceSlot.mpr (.inl ⟨?_, hr⟩)
      rw [siblingsOf_of_parent e]; exact (mem_childrenOf_iff_parentOf hU q r).mpr hq
    rw [siblingsOf_of_parent (by rw [hP', if_neg hrK]; exact hq), siblingsOf_of_parent hq,
      hChq q hqn hnq]
  cases hp : cdt.parentOf n with
  | some u =>
    have hun : u ≠ n := fun e => hs (e ▸ hp)
    have hS' : cdt.spliceSiblings n = (cdt.spliceNode n).childrenOf u := by
      unfold spliceSiblings
      rw [siblingsOf_of_parent hp, childrenOf_spliceNode hU hs, if_neg hun]
    by_cases hrS : r ∈ cdt.spliceSiblings n
    · rw [if_pos hrS, hS']
      rw [hS'] at hrS
      exact siblingsOf_of_parent ((mem_childrenOf_iff_parentOf hU' u r).mp hrS)
    · rw [if_neg hrS]
      cases hq : cdt.parentOf r with
      | some q => exact hOut hrS q hq
      | none =>
        have hrK : r ∉ cdt.childrenOf n := fun h => hrS (hKS r h)
        rw [siblingsOf_of_root (by rw [hP', if_neg hrK]; exact hq), siblingsOf_of_root hq]
        unfold rootChain
        rw [spliceNode_rootChains_of_parent hR (by rw [hp]; exact Option.some_ne_none u)]
  | none =>
    have hC := spliceNode_rootChains_of_root (cdt := cdt) hp
    have hSn : cdt.siblingsOf n = cdt.rootChain n := siblingsOf_of_root hp
    -- the spliced run is a chain after the splice
    have hMem : r ∈ cdt.spliceSiblings n → cdt.spliceSiblings n ∈ (cdt.spliceNode n).rootChains := by
      intro hrS
      rw [hC]; unfold spliceRootChains
      split
      · next hnC =>
        rcases SlotList.chainOf_cases cdt.rootChains n with ⟨D, hD, -, e⟩ | ⟨h, -⟩
        · refine List.mem_map.mpr ⟨D, hD, ?_⟩
          unfold spliceSiblings; rw [hSn]; unfold rootChain; rw [e]
        · exact absurd hnC h
      · next hnC =>
        have hS : cdt.spliceSiblings n = cdt.childrenOf n := by
          unfold spliceSiblings; rw [hSn]; unfold rootChain
          rw [SlotList.chainOf_of_not_mem hnC]; simp [replaceSlot]
        split
        · next hK => rw [hS, hK] at hrS; cases hrS
        · rw [hS]; exact List.mem_append_right _ (List.mem_singleton_self _)
    by_cases hrS : r ∈ cdt.spliceSiblings n
    · rw [if_pos hrS]
      have hpr : (cdt.spliceNode n).parentOf r = none := by
        rw [hP']
        split
        · exact hp
        · next hrK =>
          rcases mem_replaceSlot.mp hrS with ⟨hrS', -⟩ | ⟨-, hrK'⟩
          · rw [hSn] at hrS'
            rcases SlotList.mem_chainOf hrS' with hm | e
            · exact hR r hm
            · exact absurd e hr
          · exact absurd hrK' hrK
      rw [siblingsOf_of_root hpr]
      exact SlotList.chainOf_of_mem hnd' (hMem hrS) hrS
    · rw [if_neg hrS]
      cases hq : cdt.parentOf r with
      | some q => exact hOut hrS q hq
      | none =>
        have hrK : r ∉ cdt.childrenOf n := fun h => hrS (hKS r h)
        rw [siblingsOf_of_root (by rw [hP', if_neg hrK]; exact hq), siblingsOf_of_root hq]
        unfold rootChain
        rcases SlotList.chainOf_cases cdt.rootChains r with ⟨E, hE, hrE, e⟩ | ⟨hrn, e⟩
        · rw [e]
          refine SlotList.chainOf_of_mem hnd' ?_ hrE
          rw [hC]; unfold spliceRootChains
          split
          · refine List.mem_map.mpr ⟨E, hE, replaceSlot_of_not_mem fun hnE => hrS ?_⟩
            refine mem_replaceSlot.mpr (.inl ⟨?_, hr⟩)
            rw [hSn]; unfold rootChain; rw [SlotList.chainOf_of_mem hnd hE hnE]; exact hrE
          · split
            · exact hE
            · exact List.mem_append_left _ hE
        · rw [e]
          refine SlotList.chainOf_of_not_mem fun hm => ?_
          rw [hC] at hm
          rcases mem_flatten_spliceRootChains hm with ⟨hm, -⟩ | hm
          · exact hrn hm
          · exact hrK hm


end CapDerivationTree

namespace LinkView

/-- **The links after splicing `n` out**, slot by slot, given `n`'s children
`K`: `n` holds none; each of `K` has `n`'s parent; `K` sits between `n`'s
previous and next siblings (`n`'s parent's first child, when `n` was it); every
other link is as it was. -/
def spliceView (L : LinkView) (n : SlotRef) (K : List SlotRef) : LinkView := fun r f =>
  if r = n then none
  else match f with
    | .parent => if r ∈ K then L n .parent else L r .parent
    | .firstChild =>
      if L n .prev = none ∧ L n .parent = some r then K.head?.or (L n .next) else L r .firstChild
    | .next =>
      if K.getLast? = some r then L n .next
      else if L n .prev = some r then K.head?.or (L n .next) else L r .next
    | .prev =>
      if K.head? = some r then L n .prev
      else if L n .next = some r then K.getLast?.or (L n .prev) else L r .prev

end LinkView

namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

/-- `n`'s children are not its siblings. -/
theorem children_not_siblings (h : LinksAgree L cdt) {n : SlotRef}
    (hs : cdt.parentOf n ≠ some n) {x : SlotRef} (hx : x ∈ cdt.childrenOf n) :
    x ∉ cdt.siblingsOf n := fun hS => by
  have e1 := h.siblingsOf_of_mem_children hx
  have e2 := h.siblingsOf_eq_of_mem hS
  rw [e1] at e2
  exact not_mem_childrenOf_self h.childrenUnique hs (e2 ▸ h.mem_siblingsOf_self n)

/-- **Splicing a node out** keeps the links agreeing: its children take its
place among its siblings, in their order, and its parent's first child is the
first of them when it was the first. -/
theorem spliceNode (h : LinksAgree L cdt) (n : SlotRef)
    (hs : cdt.parentOf n ≠ some n) :
    LinksAgree (L.spliceView n (cdt.childrenOf n)) (cdt.spliceNode n) := by
  have hU := h.childrenUnique
  have hnd := h.rootsNodup
  have hR := h.rootsParentless
  have hSnd := h.siblingsOf_nodup n
  obtain ⟨a, b, hSab, hna, hnb, hrep⟩ :=
    replaceSlot_split hSnd (h.mem_siblingsOf_self n)
  have hS' : cdt.spliceSiblings n = a ++ cdt.childrenOf n ++ b := hrep _
  have hpr : L n .prev = a.getLast? := by rw [h.prev, hSab, SlotList.predIn_mid hna]
  have hnx : L n .next = b.head? := by rw [h.next, hSab, SlotList.succIn_mid hna]
  have hab : ∀ x ∈ a, x ∉ b := fun x hxa hxb => by
    rw [hSab] at hSnd
    exact (List.nodup_append.mp hSnd).2.2 x hxa x (List.mem_cons_of_mem _ hxb) rfl
  have hKS : ∀ x ∈ cdt.childrenOf n, x ∉ a ∧ x ∉ b := fun x hx => by
    have := h.children_not_siblings hs hx
    rw [hSab] at this
    exact ⟨fun h' => this (List.mem_append_left _ h'),
      fun h' => this (List.mem_append_right _ (List.mem_cons_of_mem _ h'))⟩
  have hKnd := childrenOf_nodup hU n
  have hand : a.Nodup := by
    rw [hSab] at hSnd; exact hSnd.sublist (List.sublist_append_left ..)
  have hsibA : ∀ x ∈ a, cdt.siblingsOf x = a ++ n :: b := fun x hx => by
    rw [← hSab]; exact h.siblingsOf_eq_of_mem (by rw [hSab]; exact List.mem_append_left _ hx)
  have hsibB : ∀ x ∈ b, cdt.siblingsOf x = a ++ n :: b := fun x hx => by
    rw [← hSab]
    exact h.siblingsOf_eq_of_mem (by rw [hSab]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx))
  have hsibK : ∀ x ∈ cdt.childrenOf n, cdt.siblingsOf x = cdt.childrenOf n := fun x hx =>
    h.siblingsOf_of_mem_children hx
  have hprA : ∀ x, a.getLast? = some x → x ∈ a := fun x e => List.mem_of_getLast? e
  have hdK : ∀ x, (cdt.childrenOf n).head? = some x → x ∈ cdt.childrenOf n :=
    fun x e => List.mem_of_mem_head? e
  have hrep' : ∀ m, replaceSlot n m (a ++ n :: b) = a ++ m ++ b := fun m => by
    rw [← hSab]; exact hrep m
  have hnxB : ∀ x, b.head? = some x → x ∈ b := fun x e => List.mem_of_mem_head? e
  refine ⟨childrenUnique_spliceNode hU hs, rootsNodup_spliceNode hU hnd hR n,
    rootsParentless_spliceNode hU hR hs, fun r => ?_, fun p => ?_, fun r => ?_, fun r => ?_⟩
  · -- parent
    show (if r = n then none else if r ∈ cdt.childrenOf n then L n .parent else L r .parent) = _
    rw [parentOf_spliceNode hU hs, h.parent, h.parent]
  · -- first child
    show (if p = n then none else if L n .prev = none ∧ L n .parent = some p then
      (cdt.childrenOf n).head?.or (L n .next) else L p .firstChild) = _
    rw [childrenOf_spliceNode hU hs]
    by_cases hpn : p = n
    · rw [if_pos hpn, if_pos hpn]; rfl
    · rw [if_neg hpn, if_neg hpn, h.parent, hpr, hnx, h.firstChild]
      by_cases hup : cdt.parentOf n = some p
      · have hSp : cdt.childrenOf p = a ++ n :: b := by rw [← siblingsOf_of_parent hup, hSab]
        rw [hSp, hrep']
        by_cases ha : a = []
        · subst ha; simp [List.head?_append, hup]
        · have : a.getLast? ≠ none := fun e => ha (List.getLast?_eq_none_iff.mp e)
          simp only [this, false_and, if_false, List.head?_append, List.append_assoc]
          cases a with
          | nil => exact absurd rfl ha
          | cons x a => rfl
      · simp only [hup, and_false, if_false]
        rw [replaceSlot_of_not_mem fun hm => hup ((mem_childrenOf_iff_parentOf hU p n).mp hm)]
  · -- next
    show (if r = n then none else if (cdt.childrenOf n).getLast? = some r then L n .next
      else if L n .prev = some r then (cdt.childrenOf n).head?.or (L n .next) else L r .next) = _
    by_cases hrn : r = n
    · rw [if_pos hrn, hrn, siblingsOf_spliceNode_self hU hR hs]; simp [SlotList.succIn]
    · rw [if_neg hrn, siblingsOf_spliceNode hU hnd hR hs hrn, hS', hpr, hnx]
      by_cases hrS : r ∈ a ++ cdt.childrenOf n ++ b
      · rw [if_pos hrS, List.append_assoc, SlotList.succIn_append]
        rcases List.mem_append.mp hrS with hr' | hrb
        · rcases List.mem_append.mp hr' with hra | hrK
          · have hrK : r ∉ cdt.childrenOf n := fun hk => (hKS r hk).1 hra
            rw [if_neg (fun e => hrK (List.mem_of_getLast? e)), if_pos hra]
            by_cases hl : a.getLast? = some r
            · rw [if_pos hl, (SlotList.succIn_eq_none_iff hand hra).mpr hl, List.head?_append]; rfl
            · rw [if_neg hl, h.next, hsibA r hra, SlotList.succIn_append, if_pos hra]
              cases hsa : SlotList.succIn a r with
              | none => exact absurd ((SlotList.succIn_eq_none_iff hand hra).mp hsa) hl
              | some y => rfl
          · have hra := (hKS r hrK).1
            rw [if_neg hra, SlotList.succIn_append, if_pos hrK]
            by_cases hl : (cdt.childrenOf n).getLast? = some r
            · rw [if_pos hl, (SlotList.succIn_eq_none_iff hKnd hrK).mpr hl]; rfl
            · rw [if_neg hl, if_neg (fun e => hra (hprA r e)), h.next, hsibK r hrK]
              cases hsa : SlotList.succIn (cdt.childrenOf n) r with
              | none => exact absurd ((SlotList.succIn_eq_none_iff hKnd hrK).mp hsa) hl
              | some y => rfl
        · have hra : r ∉ a := fun e => hab r e hrb
          have hrK : r ∉ cdt.childrenOf n := fun hk => (hKS r hk).2 hrb
          rw [if_neg hra, SlotList.succIn_append, if_neg hrK,
            if_neg (fun e => hrK (List.mem_of_getLast? e)), if_neg (fun e => hra (hprA r e)),
            h.next, hsibB r hrb, SlotList.succIn_append, if_neg hra, SlotList.succIn_cons,
            if_neg (Ne.symm hrn)]
      · rw [if_neg hrS]
        have hrK : r ∉ cdt.childrenOf n := fun hk =>
          hrS (List.mem_append_left _ (List.mem_append_right _ hk))
        rw [if_neg (fun e => hrK (List.mem_of_getLast? e)),
          if_neg (fun e => hrS (List.mem_append_left _ (List.mem_append_left _ (hprA r e)))),
          h.next]
  · -- prev
    show (if r = n then none else if (cdt.childrenOf n).head? = some r then L n .prev
      else if L n .next = some r then (cdt.childrenOf n).getLast?.or (L n .prev) else L r .prev) = _
    by_cases hrn : r = n
    · rw [if_pos hrn, hrn, siblingsOf_spliceNode_self hU hR hs]; simp [SlotList.predIn, SlotList.predAux]
    · rw [if_neg hrn, siblingsOf_spliceNode hU hnd hR hs hrn, hS', hpr, hnx]
      by_cases hrS : r ∈ a ++ cdt.childrenOf n ++ b
      · rw [if_pos hrS, List.append_assoc, SlotList.predIn_append]
        rcases List.mem_append.mp hrS with hr' | hrb
        · rcases List.mem_append.mp hr' with hra | hrK
          · have hrK : r ∉ cdt.childrenOf n := fun hk => (hKS r hk).1 hra
            rw [if_pos hra, if_neg (fun e => hrK (hdK r e)),
              if_neg (fun e => hab r hra (hnxB r e)), h.prev, hsibA r hra,
              SlotList.predIn_append, if_pos hra]
          · have hra := (hKS r hrK).1
            have hrb := (hKS r hrK).2
            rw [if_neg hra, SlotList.predAux_append, if_pos hrK]
            by_cases hl : (cdt.childrenOf n).head? = some r
            · rw [if_pos hl, SlotList.predAux_of_head _ hl]
            · rw [if_neg hl, if_neg (fun e => hrb (hnxB r e)), SlotList.predAux_of_head_ne _ hl,
                h.prev, hsibK r hrK]
        · have hra : r ∉ a := fun e => hab r e hrb
          have hrK : r ∉ cdt.childrenOf n := fun hk => (hKS r hk).2 hrb
          rw [if_neg hra, SlotList.predAux_append, if_neg hrK,
            if_neg (fun e => hrK (hdK r e)), h.prev, hsibB r hrb,
            SlotList.predIn_append, if_neg hra]
          simp only [SlotList.predAux, if_neg (Ne.symm hrn)]
          by_cases hl : b.head? = some r
          · rw [if_pos hl, SlotList.predAux_of_head _ hl]
          · rw [if_neg hl, SlotList.predAux_of_head_ne _ hl, SlotList.predAux_of_head_ne _ hl]
      · rw [if_neg hrS]
        have hrK : r ∉ cdt.childrenOf n := fun hk =>
          hrS (List.mem_append_left _ (List.mem_append_right _ hk))
        rw [if_neg (fun e => hrK (hdK r e)),
          if_neg (fun e => hrS (List.mem_append_right _ (hnxB r e))), h.prev]

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
    LinksAgree (L.spliceView n (cdt.childrenOf n)) (cdt.spliceNode n) :=
  h.spliceNode n (h.parentOf_ne_self_of_wf hWF n)

end LinksAgree


namespace LinkView

/-- **Re-parent a run of children and close it onto `nx`**: each of `K` takes
`up` as parent, and the last of them takes `nx` as next, `nx` taking it as
previous.  The link writes of a splice's child run, in run order. -/
def spliceRun (up nx : Option SlotRef) : List SlotRef → LinkView → LinkView
  | [], L => L
  | [x], L =>
    let L1 := (L.set x .parent up).set x .next nx
    match nx with
    | some y => L1.set y .prev (some x)
    | none => L1
  | x :: y :: rest, L => spliceRun up nx (y :: rest) (L.set x .parent up)

theorem spliceRun_parent (up nx : Option SlotRef) :
    ∀ (K : List SlotRef) (L : LinkView) (r : SlotRef),
      spliceRun up nx K L r .parent = if r ∈ K then up else L r .parent
  | [], _, _ => by simp [spliceRun]
  | [x], L, r => by
    unfold spliceRun
    cases nx <;> by_cases h : r = x <;> simp [set, h]
  | x :: y :: rest, L, r => by
    unfold spliceRun
    rw [spliceRun_parent up nx (y :: rest)]
    by_cases h : r = x
    · subst h; simp [set]
    · simp [set, h]

theorem spliceRun_firstChild (up nx : Option SlotRef) :
    ∀ (K : List SlotRef) (L : LinkView) (r : SlotRef),
      spliceRun up nx K L r .firstChild = L r .firstChild
  | [], _, _ => rfl
  | [x], L, r => by unfold spliceRun; cases nx <;> simp [set]
  | x :: y :: rest, L, r => by
    unfold spliceRun; rw [spliceRun_firstChild up nx (y :: rest)]; simp [set]

theorem spliceRun_next (up nx : Option SlotRef) :
    ∀ (K : List SlotRef) (L : LinkView) (r : SlotRef),
      spliceRun up nx K L r .next = if K.getLast? = some r then nx else L r .next
  | [], _, _ => by simp [spliceRun]
  | [x], L, r => by
    unfold spliceRun
    by_cases h : r = x
    · subst h; cases nx <;> simp [set]
    · have h' : x ≠ r := Ne.symm h
      cases nx <;> simp [set, h, h']
  | x :: y :: rest, L, r => by
    unfold spliceRun
    rw [spliceRun_next up nx (y :: rest)]
    have : (x :: y :: rest).getLast? = (y :: rest).getLast? := by
      simp [List.getLast?_cons]
    rw [this]; simp [set]

theorem spliceRun_prev (up nx : Option SlotRef) :
    ∀ (K : List SlotRef) (L : LinkView) (r : SlotRef),
      spliceRun up nx K L r .prev = if nx = some r ∧ K ≠ [] then K.getLast? else L r .prev
  | [], _, _ => by simp [spliceRun]
  | [x], L, r => by
    unfold spliceRun
    cases nx with
    | none => simp [set]
    | some y =>
      by_cases h : r = y
      · subst h; simp
      · have h' : y ≠ r := Ne.symm h
        simp [set, h, h']
  | x :: y :: rest, L, r => by
    unfold spliceRun
    rw [spliceRun_prev up nx (y :: rest)]
    have : (x :: y :: rest).getLast? = (y :: rest).getLast? := by
      simp [List.getLast?_cons]
    rw [this]; simp [set]

/-- **The link writes of `spliceNode n`**, given `n`'s children `K`: with none,
unlink `n`; else the first of `K` takes `n`'s previous sibling as previous, that
sibling (or, when `n` was first, `n`'s parent) takes it as next (first child),
the run is re-parented and closed onto `n`'s next sibling, and `n`'s links are
cleared. -/
def spliceLinks (L : LinkView) (n : SlotRef) (K : List SlotRef) : LinkView :=
  match K with
  | [] => L.unlinkChild n
  | c :: _ =>
    let L1 := L.set c .prev (L n .prev)
    let L2 := match L n .prev with
      | some p => L1.set p .next (some c)
      | none => match L n .parent with
        | some u => L1.set u .firstChild (some c)
        | none => L1
    (L2.spliceRun (L n .parent) (L n .next) K).clearLinks n

end LinkView

namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

/-- **The splice's link writes give the spliced links.** -/
theorem spliceLinks_eq (h : LinksAgree L cdt) {n : SlotRef} (hs : cdt.parentOf n ≠ some n) :
    L.spliceLinks n (cdt.childrenOf n) = L.spliceView n (cdt.childrenOf n) := by
  have hup : L n .parent ≠ some n := by rw [h.parent]; exact hs
  have hnxK : ∀ x, L n .next = some x → x ∉ cdt.childrenOf n := fun x e hx => by
    rw [h.next] at e
    exact h.children_not_siblings hs hx (SlotList.succIn_mem e)
  funext r f
  cases hK : cdt.childrenOf n with
  | nil =>
    have hfc : L n .firstChild = none := by rw [h.firstChild, hK]; rfl
    show L.unlinkChild n r f = (if r = n then none else _)
    cases f
    · rw [unlinkChild_parent]; simp
    · rw [unlinkChild_firstChild]
      by_cases hrn : r = n
      · subst hrn; simp only [if_true]
        rw [if_neg (fun hc => hup hc.2)]; exact hfc
      · simp [hrn]
    · rw [unlinkChild_next]; simp
    · rw [unlinkChild_prev]; simp
  | cons c K' =>
    show ((match L n .prev with
      | some p => (L.set c .prev (L n .prev)).set p .next (some c)
      | none => match L n .parent with
        | some u => (L.set c .prev (L n .prev)).set u .firstChild (some c)
        | none => L.set c .prev (L n .prev)).spliceRun (L n .parent) (L n .next) (c :: K')).clearLinks
          n r f = (if r = n then none else _)
    rw [clearLinks_apply]
    by_cases hrn : r = n
    · rw [if_pos hrn, if_pos hrn]
    · rw [if_neg hrn, if_neg hrn]
      have hcK : c ∈ cdt.childrenOf n := by rw [hK]; exact List.mem_cons_self ..
      cases f
      · rw [spliceRun_parent]
        split
        · rfl
        · cases L n .prev <;> cases L n .parent <;> simp [LinkView.set]
      · rw [spliceRun_firstChild]
        cases hp : L n .prev with
        | some p => simp [LinkView.set]
        | none =>
          cases hu : L n .parent with
          | none => simp [LinkView.set]
          | some u =>
            by_cases hru : r = u
            · subst hru; simp [LinkView.set]
            · have h' : u ≠ r := Ne.symm hru
              simp [LinkView.set, hru, h']
      · rw [spliceRun_next]
        split
        · rfl
        · cases hp : L n .prev with
          | none => cases L n .parent <;> simp [LinkView.set]
          | some p =>
            by_cases hrp : r = p
            · subst hrp; simp [LinkView.set]
            · have h' : p ≠ r := Ne.symm hrp
              simp [LinkView.set, hrp, h']
      · rw [spliceRun_prev]
        have hne : (c :: K') ≠ [] := List.cons_ne_nil _ _
        by_cases hrc : r = c
        · subst hrc
          have : L n .next ≠ some r := fun e => hnxK r e hcK
          simp only [List.head?_cons, if_true, this, false_and, if_false]
          cases L n .prev <;> cases L n .parent <;> simp [LinkView.set]
        · have : (c :: K').head? ≠ some r := by simp [Ne.symm hrc]
          rw [if_neg this]
          by_cases hnx : L n .next = some r
          · rw [if_pos ⟨hnx, hne⟩, if_pos hnx]
            cases hl : (c :: K').getLast? with
            | none => simp at hl
            | some z => rfl
          · rw [if_neg (fun hc => hnx hc.1), if_neg hnx]
            cases L n .prev <;> cases L n .parent <;> simp [LinkView.set, hrc]

/-- **Splicing a node out**, with its link writes, keeps the links agreeing. -/
theorem spliceNode_links (h : LinksAgree L cdt) (n : SlotRef) (hs : cdt.parentOf n ≠ some n) :
    LinksAgree (L.spliceLinks n (cdt.childrenOf n)) (cdt.spliceNode n) := by
  rw [h.spliceLinks_eq hs]; exact h.spliceNode n hs

end LinksAgree


/-! ### The tree after a move

`moveNode old new` renames `old` to `new` everywhere, so `new` has `old`'s
parent, children and siblings, each renamed, and `old` is outside the tree. -/

namespace CapDerivationTree

section rename

variable {old new : SlotRef}

theorem renameSlot_ne_old (hon : old ≠ new) (x : SlotRef) : renameSlot old new x ≠ old := by
  unfold renameSlot; split
  · exact Ne.symm hon
  · assumption

theorem renameSlot_back_ne_new (hon : old ≠ new) (x : SlotRef) : renameSlot new old x ≠ new := by
  unfold renameSlot; split
  · exact hon
  · assumption

theorem renameSlot_forth {r : SlotRef} (h : r ≠ old) :
    renameSlot old new (renameSlot new old r) = r := by
  unfold renameSlot
  by_cases hn : r = new
  · subst hn; simp
  · simp [hn, h]

theorem renameSlot_inj {x y : SlotRef} (hx : x ≠ new) (hy : y ≠ new)
    (h : renameSlot old new x = renameSlot old new y) : x = y := by
  rw [← renameSlot_back (old := old) hx, ← renameSlot_back (old := old) hy, h]

/-- `ρ x = r` exactly when `x = σ r`, for `x ≠ new` and `r ≠ old`. -/
theorem renameSlot_eq_iff {x r : SlotRef} (hx : x ≠ new) (hr : r ≠ old) :
    renameSlot old new x = r ↔ x = renameSlot new old r := by
  constructor
  · rintro rfl; exact (renameSlot_back hx).symm
  · rintro rfl; exact renameSlot_forth hr

end rename

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..),
      find?_congr (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hnd => by
    have ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hnd'⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    exact haL (h b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e ▸ hb)

section move

variable {cdt : CapDerivationTree} {old new : SlotRef}

/-- **The children after a move**: none for `old`; for every other slot, the
children of its name before the move (`new`'s are `old`'s), renamed. -/
theorem childrenOf_moveNode (hnew : ¬ cdt.mentions new) (hon : old ≠ new) (q : SlotRef) :
    (cdt.moveNode old new).childrenOf q =
      if q = old then [] else (cdt.childrenOf (renameSlot new old q)).map (renameSlot old new) := by
  rw [childrenOf_eq_kidsIn, moveNode_edges_eq]
  unfold kidsIn moveEdges
  rw [List.filter_map, List.map_map]
  split
  · next hq =>
    subst hq
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    · intro e _
      simp [renameEdge, CapDerivationEdge.isParentOf, renameSlot_ne_old hon]
  · next hq =>
    rw [childrenOf_eq_kidsIn]; unfold kidsIn
    rw [List.map_map]
    have : List.filter ((fun x => x.isParentOf q) ∘ renameEdge old new) cdt.edges =
        List.filter (fun x => x.isParentOf (renameSlot new old q)) cdt.edges := by
      apply List.filter_congr
      intro e he
      have hp := (not_edge_of_not_mentions hnew e he).1
      simp only [Function.comp_def, renameEdge, CapDerivationEdge.isParentOf]
      exact decide_eq_decide.mpr (renameSlot_eq_iff hp hq)
    rw [this]; rfl

/-- **The parent after a move**: none for `old`; for every other slot, the
parent of its name before the move, renamed. -/
theorem parentOf_moveNode (hnew : ¬ cdt.mentions new) (hon : old ≠ new) (r : SlotRef) :
    (cdt.moveNode old new).parentOf r =
      if r = old then none else (cdt.parentOf (renameSlot new old r)).map (renameSlot old new) := by
  unfold parentOf
  rw [moveNode_edges_eq]; unfold moveEdges
  rw [List.find?_map, Option.map_map]
  split
  · next hr =>
    subst hr
    rw [show List.find? _ cdt.edges = none from List.find?_eq_none.mpr fun e _ => by
      simp [renameEdge, CapDerivationEdge.isChildOf, renameSlot_ne_old hon]]
    rfl
  · next hr =>
    rw [Option.map_map]
    rw [find?_congr (q := (·.isChildOf (renameSlot new old r))) fun e he => by
      have hc := (not_edge_of_not_mentions hnew e he).2
      simp only [Function.comp_def, renameEdge, CapDerivationEdge.isChildOf]
      exact decide_eq_decide.mpr (renameSlot_eq_iff hc hr)]
    rfl

theorem childrenUnique_moveNode (hU : cdt.childrenUnique) (hnew : ¬ cdt.mentions new) :
    (cdt.moveNode old new).childrenUnique := by
  unfold childrenUnique; rw [moveNode_edges_eq]; unfold moveEdges
  rw [List.map_map]
  have : (cdt.edges.map ((·.child) ∘ renameEdge old new)) =
      (cdt.edges.map (·.child)).map (renameSlot old new) := by
    rw [List.map_map]; rfl
  rw [this]
  refine nodup_map_of_inj (fun x hx y hy e => ?_) hU
  obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ey, hey, rfl⟩ := List.mem_map.mp hy
  exact renameSlot_inj (not_edge_of_not_mentions hnew ex hex).2
    (not_edge_of_not_mentions hnew ey hey).2 e

theorem moveNode_rootChains_flatten (cdt : CapDerivationTree) (old new : SlotRef) :
    (cdt.moveNode old new).rootChains.flatten = cdt.rootChains.flatten.map (renameSlot old new) := by
  rw [moveNode_rootChains, List.map_flatten]

theorem rootsNodup_moveNode (hnd : cdt.rootChains.flatten.Nodup) (hnew : ¬ cdt.mentions new) :
    (cdt.moveNode old new).rootChains.flatten.Nodup := by
  have hR' : ∀ y ∈ cdt.rootChains.flatten, y ≠ new := fun y hy e => hnew (.inr (e ▸ hy))
  rw [moveNode_rootChains_flatten]
  refine nodup_map_of_inj (fun x hx y hy e => ?_) hnd
  exact renameSlot_inj (hR' x hx) (hR' y hy) e

theorem rootsParentless_moveNode (hR : cdt.rootsParentless) (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) : (cdt.moveNode old new).rootsParentless := by
  have hR' : ∀ y ∈ cdt.rootChains.flatten, y ≠ new := fun y hy e => hnew (.inr (e ▸ hy))
  intro x hx
  rw [moveNode_rootChains_flatten] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rw [parentOf_moveNode hnew hon, if_neg (renameSlot_ne_old hon y),
    renameSlot_back (hR' y hy), hR y hy]
  rfl

/-- **The siblings after a move**: `old` alone for `old`; for every other slot,
the siblings of its name before the move, renamed. -/
theorem siblingsOf_moveNode (hU : cdt.childrenUnique) (hnd : cdt.rootChains.flatten.Nodup)
    (hnew : ¬ cdt.mentions new) (hon : old ≠ new) (r : SlotRef) :
    (cdt.moveNode old new).siblingsOf r =
      if r = old then [old] else (cdt.siblingsOf (renameSlot new old r)).map (renameSlot old new) := by
  have hnd' := rootsNodup_moveNode (old := old) hnd hnew
  have hFl := moveNode_rootChains_flatten cdt old new
  have hR' : ∀ y ∈ cdt.rootChains.flatten, y ≠ new := fun y hy e => hnew (.inr (e ▸ hy))
  split
  · next hr =>
    subst hr
    rw [siblingsOf_of_root (by rw [parentOf_moveNode hnew hon, if_pos rfl])]
    unfold rootChain
    refine SlotList.chainOf_of_not_mem fun hm => ?_
    rw [hFl] at hm
    obtain ⟨y, -, e⟩ := List.mem_map.mp hm
    exact renameSlot_ne_old hon y e
  · next hr =>
    unfold siblingsOf
    rw [parentOf_moveNode hnew hon, if_neg hr]
    cases hP : cdt.parentOf (renameSlot new old r) with
    | some p =>
      simp only [Option.map_some]
      have hpn : p ≠ new := fun e => by
        obtain ⟨e', he', hp', -⟩ := (parentOf_eq_some_iff hU p _).mp hP
        exact hnew (.inl ⟨e', he', .inl (hp'.trans e)⟩)
      rw [childrenOf_moveNode hnew hon, if_neg (renameSlot_ne_old hon p), renameSlot_back hpn]
    | none =>
      simp only [Option.map_none]
      unfold rootChain
      rcases SlotList.chainOf_cases cdt.rootChains (renameSlot new old r) with
        ⟨D, hD, hsD, e⟩ | ⟨hn, e⟩
      · rw [e]
        refine SlotList.chainOf_of_mem hnd' (by rw [moveNode_rootChains]; exact List.mem_map_of_mem hD) ?_
        exact List.mem_map.mpr ⟨_, hsD, renameSlot_forth hr⟩
      · rw [e, List.map_singleton, renameSlot_forth hr]
        refine SlotList.chainOf_of_not_mem fun hm => ?_
        rw [hFl] at hm
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
        rw [renameSlot_back (hR' y hy)] at hn
        exact hn hy

end move

end CapDerivationTree

namespace LinkView

/-- **The links after moving `old` to `new`**, slot by slot: `old` holds none;
every other slot holds the links of its name before the move (`new`'s are
`old`'s), each naming `new` where it named `old`. -/
def renameView (L : LinkView) (old new : SlotRef) : LinkView := fun r f =>
  if r = old then none
  else (L (CapDerivationTree.renameSlot new old r) f).map (CapDerivationTree.renameSlot old new)

end LinkView

namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

/-- **Moving a node to a slot outside the tree** keeps the links agreeing: the
moved slot takes the old one's place, its neighbours and children naming it. -/
theorem moveNode (h : LinksAgree L cdt) (old new : SlotRef) (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) : LinksAgree (L.renameView old new) (cdt.moveNode old new) := by
  have hU := h.childrenUnique
  have hnd := h.rootsNodup
  -- renaming is injective on a slot's siblings, for every name but `old`
  have hInj : ∀ r, ∀ x ∈ cdt.siblingsOf (renameSlot new old r),
      renameSlot old new x = renameSlot old new (renameSlot new old r) → x = renameSlot new old r := by
    intro r x hx e
    have hs : renameSlot new old r ≠ new := renameSlot_back_ne_new hon r
    have hxn : x ≠ new := fun hxe => by
      by_cases hxs : x = renameSlot new old r
      · exact hs (hxs ▸ hxe)
      · exact hnew (hxe ▸ mentions_of_sibling hx hxs)
    exact renameSlot_inj hxn hs e
  refine ⟨childrenUnique_moveNode hU hnew, rootsNodup_moveNode hnd hnew,
    rootsParentless_moveNode h.rootsParentless hnew hon, fun r => ?_, fun p => ?_, fun r => ?_,
    fun r => ?_⟩
  · show (if r = old then none else _) = _
    rw [parentOf_moveNode hnew hon, h.parent]
  · show (if p = old then none else _) = _
    rw [childrenOf_moveNode hnew hon]
    split
    · rfl
    · rw [h.firstChild, List.head?_map]
  · show (if r = old then none else _) = _
    rw [siblingsOf_moveNode hU hnd hnew hon]
    split
    · next hr => subst hr; simp [SlotList.succIn]
    · next hr =>
      rw [h.next]
      have e := (SlotList.succIn_map _ (hInj r)).symm
      rwa [renameSlot_forth hr] at e
  · show (if r = old then none else _) = _
    rw [siblingsOf_moveNode hU hnd hnew hon]
    split
    · next hr => subst hr; simp [SlotList.predIn, SlotList.predAux]
    · next hr =>
      rw [h.prev]
      have e := (SlotList.predIn_map _ (hInj r)).symm
      rwa [renameSlot_forth hr] at e

/-- **Moving a node of an acyclic tree to a slot outside it** keeps the links agreeing. -/
theorem moveNode_of_wf (h : LinksAgree L cdt) (old new : SlotRef) (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) : LinksAgree (L.renameView old new) (cdt.moveNode old new) :=
  h.moveNode old new hnew hon

end LinksAgree


namespace LinkView

/-- **The link writes of `moveNode old new`**, given `old`'s children `K`: `new`
takes `old`'s four links; `old`'s previous sibling (or, when `old` was first,
its parent) and next sibling name `new` instead; each child takes `new` as
parent; `old`'s links are cleared. -/
def moveLinks (L : LinkView) (old new : SlotRef) (K : List SlotRef) : LinkView :=
  let up := L old .parent
  let pr := L old .prev
  let nx := L old .next
  let L1 := (((L.set new .parent up).set new .firstChild (L old .firstChild)).set new .next nx).set
    new .prev pr
  let L2 := match pr with
    | some p => L1.set p .next (some new)
    | none => match up with
      | some u => L1.set u .firstChild (some new)
      | none => L1
  let L3 := match nx with
    | some x => L2.set x .prev (some new)
    | none => L2
  (K.foldl (fun L x => L.set x .parent (some new)) L3).clearLinks old

theorem foldl_set_parent (v : Option SlotRef) :
    ∀ (K : List SlotRef) (L : LinkView) (r : SlotRef) (f : LinkField),
      K.foldl (fun L x => L.set x .parent v) L r f = if f = .parent ∧ r ∈ K then v else L r f
  | [], _, _, _ => by simp
  | x :: K, L, r, f => by
    rw [List.foldl_cons, foldl_set_parent v K]
    by_cases hf : f = .parent
    · subst hf
      by_cases hr : r = x
      · subst hr; simp [set]
      · simp [set, hr]
    · simp [set, hf]

theorem moveLinks_apply (L : LinkView) (old new : SlotRef) (K : List SlotRef)
    (hN : ∀ f, L old f ≠ some new) (r : SlotRef) (f : LinkField) :
    L.moveLinks old new K r f =
      if r = old then none
      else if f = .parent ∧ r ∈ K then some new
      else if r = new then L old f
      else if f = .next ∧ L old .prev = some r then some new
      else if f = .firstChild ∧ L old .prev = none ∧ L old .parent = some r then some new
      else if f = .prev ∧ L old .next = some r then some new
      else L r f := by
  unfold moveLinks
  simp only [clearLinks_apply, foldl_set_parent]
  by_cases hro : r = old
  · simp [hro]
  rw [if_neg hro, if_neg hro]
  by_cases hk : f = .parent ∧ r ∈ K
  · rw [if_pos hk, if_pos hk]
  rw [if_neg hk, if_neg hk]
  have hP := hN .prev
  have hX := hN .next
  have hU := hN .parent
  cases hp : L old .prev <;> cases hx : L old .next <;> cases hu : L old .parent <;>
    by_cases hrn : r = new <;> cases f <;> simp_all [set] <;> grind

end LinkView

namespace LinksAgree

open CapDerivationTree LinkView

variable {L : LinkView} {cdt : CapDerivationTree}

theorem map_renameSlot (old new : SlotRef) (v : Option SlotRef) :
    v.map (renameSlot old new) = if v = some old then some new else v := by
  cases v with
  | none => rfl
  | some y =>
    unfold renameSlot
    by_cases h : y = old
    · subst h; simp
    · simp [h]

/-- **The move's link writes give the moved links.** -/
theorem moveLinks_eq (h : LinksAgree L cdt) {old new : SlotRef} (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) (hs : cdt.parentOf old ≠ some old) :
    L.moveLinks old new (cdt.childrenOf old) = L.renameView old new := by
  have hU := h.childrenUnique
  have hNoNew : ∀ r f, L r f ≠ some new := fun r f e => hnew (h.target_mentions e)
  have hnK : new ∉ cdt.childrenOf old := not_mem_childrenOf_of_not_mentions hnew old
  have hOld : ∀ f, L old f ≠ some old := by
    intro f
    cases f
    · rw [h.parent]; exact hs
    · rw [h.firstChild]; intro e
      exact not_mem_childrenOf_self hU hs (List.mem_of_mem_head? e)
    · exact h.next_ne_self old
    · exact h.prev_ne_self old
  funext r f
  rw [moveLinks_apply _ _ _ _ (fun f e => hNoNew old f e)]
  unfold renameView
  by_cases hro : r = old
  · simp [hro]
  rw [if_neg hro, if_neg hro]
  by_cases hrn : r = new
  · subst hrn
    have hσ : renameSlot r old r = old := by simp [renameSlot]
    rw [hσ, map_renameSlot, if_neg (hOld f), if_neg (fun hc => hnK hc.2), if_pos rfl]
  · have hσ : renameSlot new old r = r := by simp [renameSlot, hrn]
    rw [hσ, map_renameSlot, if_neg hrn]
    cases f
    · simp only [true_and, reduceCtorEq, false_and, if_false]
      simp only [h.parent_eq_some_iff]
    · simp only [true_and, reduceCtorEq, false_and, if_false]
      simp only [h.firstChild_eq_some_iff r old, and_comm]
    · simp only [true_and, reduceCtorEq, false_and, if_false]
      simp only [h.next_eq_some_iff r old]
    · simp only [true_and, reduceCtorEq, false_and, if_false]
      simp only [← h.next_eq_some_iff old r]

/-- **Moving a node to a slot outside the tree**, with its link writes, keeps
the links agreeing. -/
theorem moveNode_links (h : LinksAgree L cdt) (old new : SlotRef) (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) (hs : cdt.parentOf old ≠ some old) :
    LinksAgree (L.moveLinks old new (cdt.childrenOf old)) (cdt.moveNode old new) := by
  rw [h.moveLinks_eq hnew hon hs]; exact h.moveNode old new hnew hon

end LinksAgree

end SeLe4n.Model
