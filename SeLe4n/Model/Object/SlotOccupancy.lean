-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# A slot array's occupied slots, linked through the slots

WS-ZA ZA5.4 part 26.  A CNode links its occupied slots into one doubly linked
list held in its own words (`CNode.occ`, two words per slot, and
`CNode.occHead`), as its derivation links are held: no list is allocated, a
slot is linked in when it is filled and unlinked when it is emptied, each in
`O(1)` writes, and a walk of the occupied slots (the zombie loop of a CNode's
final delete) visits only those, never every slot index.

Word `2 * i` of the link array is slot `i`'s next occupied slot and word
`2 * i + 1` its previous one, each `0` for none and `j + 1` for slot `j`
(`code`).  The list is a ghost (`Encodes`): the links agree with a list `L` of
slot indices that holds no index twice and holds exactly the occupied slots, and
the head word is the code of `L`'s first slot.  This module states that
agreement over any array of optional cells and proves that the in-place link
(`linkWords`, at the head), unlink (`unlinkWords`, anywhere) and the build of
the links from an array (`buildWords`) keep it.
-/

namespace SeLe4n.Model.SlotOccupancy

/-- The word coding an optional slot index: `0` for none, `i + 1` for slot `i`. -/
@[inline] def code : Option Nat → Nat
  | none => 0
  | some i => i + 1

@[simp] theorem code_none : code none = 0 := rfl
@[simp] theorem code_some (i : Nat) : code (some i) = i + 1 := rfl

/-- Slot `i`'s next-occupied word. -/
@[inline] def nextWord (occ : Array Nat) (i : Nat) : Nat := occ.getD (2 * i) 0

/-- Slot `i`'s previous-occupied word. -/
@[inline] def prevWord (occ : Array Nat) (i : Nat) : Nat := occ.getD (2 * i + 1) 0

/-- **The links of the list `L` from a slot whose code is `p`**: each slot's
previous word names the slot before it (`p` for the first), and its next word the
slot after it (`0` after the last). -/
def Chain (occ : Array Nat) : Nat → List Nat → Prop
  | _, [] => True
  | p, a :: rest => prevWord occ a = p ∧ nextWord occ a = code rest.head? ∧ Chain occ (a + 1) rest

/-- Whether entry `i` of the cell array holds something. -/
@[inline] def occupied {α : Type} (cells : Array (Option α)) (i : Nat) : Bool :=
  (cells.getD i none).isSome

/-- **The links and the head word encode the occupied slots as the list `L`**:
`L` holds no slot twice and exactly the occupied slots, the head word is the code
of its first slot, and the links follow it (`Chain`). -/
structure EncodesBy (P : Nat → Bool) (occ : Array Nat) (head : Nat) (L : List Nat) : Prop where
  nodup : L.Nodup
  mem : ∀ i, i ∈ L ↔ P i = true
  head_eq : head = code L.head?
  chain : Chain occ 0 L

/-- `EncodesBy` over the occupied entries of a cell array. -/
abbrev Encodes {α : Type} (cells : Array (Option α)) (occ : Array Nat) (head : Nat)
    (L : List Nat) : Prop :=
  EncodesBy (occupied cells) occ head L

theorem occupied_lt {α : Type} {cells : Array (Option α)} {i : Nat}
    (h : occupied cells i = true) : i < cells.size := by
  unfold occupied at h
  rw [Array.getD_eq_getD_getElem?] at h
  if hi : i < cells.size then exact hi
  else
    rw [Array.getElem?_eq_none (by omega)] at h
    simp at h

theorem Encodes.lt {α : Type} {cells : Array (Option α)} {occ : Array Nat} {head : Nat}
    {L : List Nat} (h : Encodes cells occ head L) {i : Nat} (hi : i ∈ L) : i < cells.size :=
  occupied_lt ((EncodesBy.mem h i).1 hi)

/-- **Reading a word of an array written in place.** -/
theorem getD_setIfInBounds (a : Array Nat) (j v k : Nat) :
    (a.setIfInBounds j v).getD k 0 = if j = k ∧ j < a.size then v else a.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hjk : j = k
  · subst hjk
    by_cases hs : j < a.size
    · simp [hs]
    · simp [hs]
  · simp [hjk]

@[simp] theorem size_setIfInBounds' (a : Array Nat) (j v : Nat) :
    (a.setIfInBounds j v).size = a.size := Array.size_setIfInBounds

/-- **The links of `L` read only the words of `L`'s slots**: another array that
agrees with `occ` on them carries the same chain. -/
theorem Chain.frame {occ occ' : Array Nat} :
    ∀ {p : Nat} {L : List Nat}, Chain occ p L →
      (∀ a ∈ L, nextWord occ' a = nextWord occ a ∧ prevWord occ' a = prevWord occ a) →
      Chain occ' p L
  | _, [], _, _ => trivial
  | _, a :: rest, ⟨h1, h2, h3⟩, hA => by
    obtain ⟨hn, hp⟩ := hA a (List.mem_cons_self ..)
    exact ⟨hp.trans h1, hn.trans h2,
      Chain.frame h3 (fun b hb => hA b (List.mem_cons_of_mem _ hb))⟩

/-- **A slot's own words, read off the chain**: the slot `i` after the prefix
`l1` has the code of `l1`'s last slot (or `p`) before it and the code of the
first slot of `l2` after it. -/
theorem Chain.words_at {occ : Array Nat} :
    ∀ {p : Nat} (l1 : List Nat) {i : Nat} {l2 : List Nat}, Chain occ p (l1 ++ i :: l2) →
      prevWord occ i = ((l1.getLast?).map (· + 1)).getD p ∧ nextWord occ i = code l2.head?
  | _, [], _, _, ⟨h1, h2, _⟩ => ⟨h1, h2⟩
  | _, a :: l1, i, l2, ⟨_, _, h3⟩ => by
    have := Chain.words_at l1 h3
    refine ⟨?_, this.2⟩
    rw [this.1]
    cases l1 with
    | nil => rfl
    | cons b l1' => simp [List.getLast?_cons]

theorem getD_set_same {a : Array Nat} {j : Nat} (v : Nat) (h : j < a.size) :
    (a.setIfInBounds j v).getD j 0 = v := by
  rw [getD_setIfInBounds, if_pos ⟨rfl, h⟩]

theorem getD_set_ne (a : Array Nat) {j k : Nat} (v : Nat) (h : j ≠ k) :
    (a.setIfInBounds j v).getD k 0 = a.getD k 0 := by
  rw [getD_setIfInBounds, if_neg (fun e => h e.1)]

-- ============================================================================
-- Linking a slot in at the head
-- ============================================================================

/-- **Link slot `i` in at the head of the list** whose head word is `head`: `i`'s
next word is the old head, its previous word none, and the old head's previous
word names `i`.  Three words written in place; the new head word is `i + 1`. -/
@[inline] def linkWords (occ : Array Nat) (head i : Nat) : Array Nat :=
  let o1 := (occ.setIfInBounds (2 * i) head).setIfInBounds (2 * i + 1) 0
  if head = 0 then o1 else o1.setIfInBounds (2 * (head - 1) + 1) (i + 1)

theorem size_linkWords (occ : Array Nat) (head i : Nat) :
    (linkWords occ head i).size = occ.size := by
  unfold linkWords; split <;> simp

theorem linkWords_next_self (occ : Array Nat) (head i : Nat) (h : 2 * i + 1 < occ.size) :
    nextWord (linkWords occ head i) i = head := by
  unfold nextWord linkWords
  split
  · rw [getD_set_ne _ _ (by omega), getD_set_same _ (by omega)]
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega), getD_set_same _ (by omega)]

theorem linkWords_prev_self (occ : Array Nat) (head i : Nat) (h : 2 * i + 1 < occ.size)
    (hh : head ≠ i + 1) : prevWord (linkWords occ head i) i = 0 := by
  unfold prevWord linkWords
  split
  · rw [getD_set_same _ (by simp; omega)]
  · rw [getD_set_ne _ _ (by omega), getD_set_same _ (by simp; omega)]

theorem linkWords_prev_head (occ : Array Nat) (head i : Nat) (h0 : head ≠ 0)
    (h : 2 * (head - 1) + 1 < occ.size) : prevWord (linkWords occ head i) (head - 1) = i + 1 := by
  unfold prevWord linkWords
  rw [if_neg h0, getD_set_same _ (by simp; omega)]

theorem linkWords_next_ne (occ : Array Nat) (head i a : Nat) (ha : a ≠ i) :
    nextWord (linkWords occ head i) a = nextWord occ a := by
  unfold nextWord linkWords
  split
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega)]
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega)]

theorem linkWords_prev_ne (occ : Array Nat) (head i a : Nat) (ha : a ≠ i) (hb : a + 1 ≠ head) :
    prevWord (linkWords occ head i) a = prevWord occ a := by
  unfold prevWord linkWords
  split
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega)]
  · rw [getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega), getD_set_ne _ _ (by omega)]

/-- **The link keeps the agreement**, with slot `i` newly occupied. -/
theorem EncodesBy.link {P P' : Nat → Bool} {occ : Array Nat} {head : Nat} {L : List Nat}
    (h : EncodesBy P occ head L) {i : Nat} (hi : P i = false)
    (hB : ∀ x, P' x = true → 2 * x + 1 < occ.size)
    (hc : ∀ j, P' j = (decide (j = i) || P j)) :
    EncodesBy P' (linkWords occ head i) (i + 1) (i :: L) := by
  have hiL : i ∉ L := fun hm => by rw [(h.mem i).1 hm] at hi; cases hi
  refine ⟨List.nodup_cons.2 ⟨hiL, h.nodup⟩, fun j => ?_, rfl, ?_⟩
  · rw [hc j, List.mem_cons, h.mem j]; by_cases e : j = i <;> simp [e]
  have hsI : 2 * i + 1 < occ.size := hB i (by rw [hc]; simp)
  cases hL : L with
  | nil =>
    have hh : head = 0 := by rw [h.head_eq, hL]; rfl
    exact ⟨linkWords_prev_self occ head i hsI (by omega),
      (linkWords_next_self occ head i hsI).trans (by rw [hh]; rfl), trivial⟩
  | cons b r =>
    rw [hL] at hiL
    have hhd : head = b + 1 := by rw [h.head_eq, hL]; rfl
    have hbr : b ∉ r := (List.nodup_cons.1 (hL ▸ h.nodup)).1
    have hbi : b ≠ i := fun e => hiL (e ▸ List.mem_cons_self ..)
    have hbs : 2 * b + 1 < occ.size :=
      hB b (by rw [hc, (h.mem b).1 (hL ▸ List.mem_cons_self ..)]; simp)
    have hC := h.chain
    rw [hL] at hC
    obtain ⟨-, h2, h3⟩ := hC
    refine ⟨linkWords_prev_self occ head i hsI (by omega),
      (linkWords_next_self occ head i hsI).trans (by rw [hhd]; rfl), ?_, ?_, ?_⟩
    · have := linkWords_prev_head occ head i (by omega) (by omega)
      rw [hhd, Nat.add_sub_cancel] at this; rw [hhd]; exact this
    · rw [linkWords_next_ne _ _ _ _ hbi]; exact h2
    · refine Chain.frame h3 (fun c hc => ?_)
      have hci : c ≠ i := fun e => hiL (e ▸ List.mem_cons_of_mem _ hc)
      have hcb : c ≠ b := fun e => hbr (e ▸ hc)
      exact ⟨linkWords_next_ne _ _ _ _ hci, linkWords_prev_ne _ _ _ _ hci (by omega)⟩

-- ============================================================================
-- Unlinking a slot anywhere in the list
-- ============================================================================

/-- **The head word once slot `i` is unlinked**: the slot after `i` when `i` has
none before it (it was the head), else the head as it was. -/
@[inline] def unlinkHead (occ : Array Nat) (head i : Nat) : Nat :=
  if prevWord occ i = 0 then nextWord occ i else head

/-- **Unlink slot `i`**: the slot before it now names the slot after it as its
next, and the slot after it names the slot before it as its previous.  At most
two words written in place; `i`'s own words are left, as no reading of the list
reaches them. -/
@[inline] def unlinkWords (occ : Array Nat) (i : Nat) : Array Nat :=
  let n := nextWord occ i
  let p := prevWord occ i
  let o1 := if p = 0 then occ else occ.setIfInBounds (2 * (p - 1)) n
  if n = 0 then o1 else o1.setIfInBounds (2 * (n - 1) + 1) p

theorem size_unlinkWords (occ : Array Nat) (i : Nat) :
    (unlinkWords occ i).size = occ.size := by
  unfold unlinkWords; dsimp only; split <;> split <;> simp

theorem nextWord_set (a : Array Nat) (j v k : Nat) :
    nextWord (a.setIfInBounds j v) k = if j = 2 * k ∧ j < a.size then v else nextWord a k :=
  getD_setIfInBounds a j v (2 * k)

theorem prevWord_set (a : Array Nat) (j v k : Nat) :
    prevWord (a.setIfInBounds j v) k = if j = 2 * k + 1 ∧ j < a.size then v else prevWord a k :=
  getD_setIfInBounds a j v (2 * k + 1)

theorem unlinkWords_next (occ : Array Nat) (i a : Nat)
    (hP : prevWord occ i ≠ 0 → 2 * (prevWord occ i - 1) < occ.size) :
    nextWord (unlinkWords occ i) a =
      if a + 1 = prevWord occ i then nextWord occ i else nextWord occ a := by
  unfold unlinkWords
  dsimp only
  generalize hn : nextWord occ i = n
  generalize hp : prevWord occ i = p at hP
  have hO : ∀ o : Array Nat, nextWord (if n = 0 then o else o.setIfInBounds (2 * (n - 1) + 1) p) a =
      nextWord o a := by
    intro o; split
    · rfl
    · rw [nextWord_set, if_neg (by omega)]
  rw [hO]
  by_cases h0 : p = 0
  · rw [if_pos h0, if_neg (by omega)]
  · rw [if_neg h0, nextWord_set]
    by_cases e : a + 1 = p
    · rw [if_pos ⟨by omega, hP h0⟩, if_pos e]
    · rw [if_neg (by omega), if_neg e]

theorem unlinkWords_prev (occ : Array Nat) (i a : Nat)
    (hN : nextWord occ i ≠ 0 → 2 * (nextWord occ i - 1) + 1 < occ.size) :
    prevWord (unlinkWords occ i) a =
      if a + 1 = nextWord occ i then prevWord occ i else prevWord occ a := by
  unfold unlinkWords
  dsimp only
  generalize hn : nextWord occ i = n at hN
  generalize hp : prevWord occ i = p
  have hS : (if p = 0 then occ else occ.setIfInBounds (2 * (p - 1)) n).size = occ.size := by
    split <;> simp
  have hO : prevWord (if p = 0 then occ else occ.setIfInBounds (2 * (p - 1)) n) a =
      prevWord occ a := by
    split
    · rfl
    · rw [prevWord_set, if_neg (by omega)]
  by_cases h0 : n = 0
  · rw [if_pos h0, hO, if_neg (by omega)]
  · rw [if_neg h0, prevWord_set, hS]
    by_cases e : a + 1 = n
    · rw [if_pos ⟨by omega, hN h0⟩, if_pos e]
    · rw [if_neg (by omega), if_neg e, hO]

/-- **The links of the list with slot `i` spliced out.**  On a chain through
`l1 ++ i :: l2` that holds no slot twice and whose words lie in the array, the
unlinked array carries the chain through `l1 ++ l2`. -/
theorem Chain.unlink {occ : Array Nat} {i : Nat} {l2 : List Nat}
    (hN : nextWord occ i = code l2.head?)
    (hB : ∀ x, x ∈ i :: l2 → 2 * x + 1 < occ.size) :
    ∀ (l1 : List Nat) (p : Nat), Chain occ p (l1 ++ i :: l2) → (l1 ++ i :: l2).Nodup →
      (∀ x ∈ l1, 2 * x + 1 < occ.size) →
      prevWord occ i = ((l1.getLast?).map (· + 1)).getD p →
      (∀ x ∈ i :: l2, x + 1 ≠ p) → (p ≠ 0 → 2 * (p - 1) + 1 < occ.size) →
      Chain (unlinkWords occ i) p (l1 ++ l2) := by
  have hNb : nextWord occ i ≠ 0 → 2 * (nextWord occ i - 1) + 1 < occ.size := by
    intro h0; cases hl : l2 with
    | nil => rw [hN, hl] at h0; exact absurd rfl h0
    | cons b r => rw [hN, hl]; simpa using hB b (by rw [hl]; exact .tail _ (.head _))
  intro l1
  induction l1 with
  | nil =>
    intro p hC hND _ hP hp hpB
    obtain ⟨h1, -, h3⟩ := hC
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none] at hP
    have hPb : prevWord occ i ≠ 0 → 2 * (prevWord occ i - 1) < occ.size := by
      intro h0; rw [hP] at h0 ⊢; have := hpB h0; omega
    cases l2 with
    | nil => trivial
    | cons b r =>
      have hbr : b ∉ r := (List.nodup_cons.1 (List.nodup_cons.1 hND).2).1
      have hib : i ≠ b := fun e => (List.nodup_cons.1 hND).1 (e ▸ .head _)
      obtain ⟨g1, g2, g3⟩ := h3
      refine ⟨?_, ?_, ?_⟩
      · rw [unlinkWords_prev _ _ _ hNb, if_pos (by rw [hN]; rfl), hP]
      · rw [unlinkWords_next _ _ _ hPb, if_neg (by rw [hP]; exact hp b (.tail _ (.head _))), g2]
      · refine Chain.frame g3 (fun c hc => ?_)
        have hci : c ≠ i := fun e => (List.nodup_cons.1 hND).1 (e ▸ .tail _ hc)
        have hcb : c ≠ b := fun e => hbr (e ▸ hc)
        refine ⟨?_, ?_⟩
        · rw [unlinkWords_next _ _ _ hPb, if_neg (by rw [hP]; exact hp c (.tail _ (.tail _ hc)))]
        · rw [unlinkWords_prev _ _ _ hNb, if_neg (by rw [hN]; simp; omega)]
  | cons a l1 ih =>
    intro p hC hND hBa hP hp _
    obtain ⟨h1, h2, h3⟩ := hC
    have hai : a ≠ i := fun e => (List.nodup_cons.1 hND).1 (e ▸ List.mem_append_right _ (.head _))
    have haL2 : a ∉ l2 := fun hm => (List.nodup_cons.1 hND).1 (List.mem_append_right _ (.tail _ hm))
    have hND' : (l1 ++ i :: l2).Nodup := (List.nodup_cons.1 hND).2
    have hP' : prevWord occ i = ((l1.getLast?).map (· + 1)).getD (a + 1) := by
      rw [hP]; cases l1 with
      | nil => rfl
      | cons b l1' => simp [List.getLast?_cons]
    have hPb : prevWord occ i ≠ 0 → 2 * (prevWord occ i - 1) < occ.size := by
      intro h0
      cases hl : l1.getLast? with
      | none => rw [hP', hl]; simp; have := hBa a (.head _); omega
      | some z =>
        rw [hP', hl]; simp
        have := hBa z (.tail _ (List.mem_of_getLast? hl)); omega
    refine ⟨?_, ?_, ih (a + 1) h3 hND' (fun x hx => hBa x (.tail _ hx)) hP' (fun x hx e => ?_)
      (fun _ => by simpa using hBa a (.head _))⟩
    · rw [unlinkWords_prev _ _ _ hNb, if_neg ?_, h1]
      rw [hN]; intro e
      cases hl : l2 with
      | nil => rw [hl] at e; simp at e
      | cons b r => rw [hl] at e haL2; simp at e; exact haL2 (e ▸ .head _)
    · rw [unlinkWords_next _ _ _ hPb]
      cases l1 with
      | nil =>
        rw [if_pos (by rw [hP]; rfl), hN]; rfl
      | cons b l1' =>
        have hab : ∀ z, (b :: l1').getLast? = some z → a + 1 ≠ z + 1 := by
          intro z hz e
          have : a = z := by omega
          subst this
          exact (List.nodup_cons.1 hND).1 (List.mem_append_left _ (List.mem_of_getLast? hz))
        cases hz : (b :: l1').getLast? with
        | none => simp at hz
        | some z =>
          rw [hP', hz, if_neg (by simpa using hab z hz), h2]; rfl
    · have : x = a := by omega
      subst this
      rcases List.mem_cons.1 hx with rfl | hx2
      · exact hai rfl
      · exact haL2 hx2

/-- **The unlink keeps the agreement**, with slot `i` newly empty. -/
theorem EncodesBy.unlink {P P' : Nat → Bool} {occ : Array Nat} {head : Nat} {L : List Nat}
    (h : EncodesBy P occ head L) {i : Nat} (hi : P i = true)
    (hB0 : ∀ x, P x = true → 2 * x + 1 < occ.size)
    (hc : ∀ j, P' j = (!decide (j = i) && P j)) :
    EncodesBy P' (unlinkWords occ i) (unlinkHead occ head i) (L.erase i) := by
  have hiL : i ∈ L := (h.mem i).2 hi
  obtain ⟨l1, l2, hL⟩ := List.append_of_mem hiL
  have hND : (l1 ++ i :: l2).Nodup := hL ▸ h.nodup
  have hi1 : i ∉ l1 := fun hm => (List.nodup_append.1 hND).2.2 i hm i (.head _) rfl
  have hE : L.erase i = l1 ++ l2 := by
    rw [hL, List.erase_append_right _ hi1, List.erase_cons_head]
  have hB : ∀ x ∈ L, 2 * x + 1 < occ.size := fun x hx => hB0 x ((h.mem x).1 hx)
  have hC := h.chain
  rw [hL] at hC
  obtain ⟨hP, hN⟩ := Chain.words_at l1 hC
  rw [hE]
  refine ⟨hND.sublist (List.Sublist.append_left (List.sublist_cons_self i l2) l1), fun j => ?_,
    ?_, ?_⟩
  · rw [hc j, ← hE, (h.nodup).mem_erase_iff, h.mem j]
    by_cases e : j = i <;> simp [e]
  · unfold unlinkHead
    cases l1 with
    | nil =>
      simp only [List.getLast?_nil, Option.map_none, Option.getD_none] at hP
      rw [if_pos hP, hN]; rfl
    | cons a l1' =>
      have hne : prevWord occ i ≠ 0 := by
        rw [hP]; cases hz : (a :: l1').getLast? with
        | none => simp at hz
        | some z => simp
      rw [if_neg hne, h.head_eq, hL]; rfl
  · exact Chain.unlink hN (fun x hx => hB x (hL ▸ List.mem_append_right _ hx)) l1 0 hC hND
      (fun x hx => hB x (hL ▸ List.mem_append_left _ hx)) hP (fun _ _ => by omega)
      (fun h0 => absurd rfl h0)

/-- **A change of the occupied set that keeps it keeps the agreement.** -/
theorem EncodesBy.congr {P P' : Nat → Bool} {occ : Array Nat} {head : Nat} {L : List Nat}
    (h : EncodesBy P occ head L) (hc : ∀ j, P' j = P j) : EncodesBy P' occ head L :=
  ⟨h.nodup, fun j => (h.mem j).trans (by rw [hc j]), h.head_eq, h.chain⟩

/-- **The link on a cell array** (`EncodesBy.link`), its bounds read off the
array sizes. -/
theorem Encodes.link {α β : Type} {cells : Array (Option α)} {cells' : Array (Option β)}
    {occ : Array Nat} {head : Nat} {L : List Nat} (h : Encodes cells occ head L) {i : Nat}
    (hi : occupied cells i = false) (hsz : occ.size = 2 * cells'.size)
    (hc : ∀ j, occupied cells' j = (decide (j = i) || occupied cells j)) :
    Encodes cells' (linkWords occ head i) (i + 1) (i :: L) :=
  EncodesBy.link h hi (fun x hx => by have := occupied_lt hx; omega) hc

/-- **The unlink on a cell array** (`EncodesBy.unlink`). -/
theorem Encodes.unlink {α β : Type} {cells : Array (Option α)} {cells' : Array (Option β)}
    {occ : Array Nat} {head : Nat} {L : List Nat} (h : Encodes cells occ head L) {i : Nat}
    (hi : occupied cells i = true) (hsz : occ.size = 2 * cells.size)
    (hc : ∀ j, occupied cells' j = (!decide (j = i) && occupied cells j)) :
    Encodes cells' (unlinkWords occ i) (unlinkHead occ head i) (L.erase i) :=
  EncodesBy.unlink h hi (fun x hx => by have := occupied_lt hx; omega) hc

/-- **A rewrite of the cells that keeps which slots are occupied keeps the
agreement.** -/
theorem Encodes.congr {α β : Type} {cells : Array (Option α)} {cells' : Array (Option β)}
    {occ : Array Nat} {head : Nat} {L : List Nat} (h : Encodes cells occ head L)
    (hc : ∀ j, occupied cells' j = occupied cells j) : Encodes cells' occ head L :=
  EncodesBy.congr h hc

-- ============================================================================
-- Building the links of a whole array
-- ============================================================================

/-- **The links of a cell array's occupied slots below `k`, linked onto `occ`**
whose head word is `head`: each occupied slot from `k - 1` down to `0` linked in
at the head (`linkWords`), so the list runs in slot order.  The words alone, as
two accumulators: no pair is built. -/
def buildWords {α : Type} (cells : Array (Option α)) : Nat → Array Nat → Nat → Array Nat
  | 0, occ, _ => occ
  | k + 1, occ, head =>
    if occupied cells k then buildWords cells k (linkWords occ head k) (k + 1)
    else buildWords cells k occ head

/-- **The head word `buildWords` leaves.** -/
def buildHead {α : Type} (cells : Array (Option α)) : Nat → Nat → Nat
  | 0, head => head
  | k + 1, head => if occupied cells k then buildHead cells k (k + 1) else buildHead cells k head

theorem size_buildWords {α : Type} (cells : Array (Option α)) :
    ∀ (k : Nat) (occ : Array Nat) (head : Nat), (buildWords cells k occ head).size = occ.size
  | 0, _, _ => rfl
  | k + 1, occ, head => by
    unfold buildWords
    split
    · rw [size_buildWords cells k, size_linkWords]
    · exact size_buildWords cells k occ head

theorem buildWords_encodes {α : Type} (cells : Array (Option α)) :
    ∀ (k : Nat) (occ : Array Nat) (head : Nat) (L : List Nat),
      occ.size = 2 * cells.size →
      EncodesBy (fun i => decide (k ≤ i) && occupied cells i) occ head L →
      ∃ L', Encodes cells (buildWords cells k occ head) (buildHead cells k head) L'
  | 0, occ, head, L, _, h => ⟨L, EncodesBy.congr h (fun j => by simp)⟩
  | k + 1, occ, head, L, hsz, h => by
    unfold buildWords buildHead
    split
    · next hk =>
      refine buildWords_encodes cells k _ _ (k :: L) (by rw [size_linkWords, hsz])
        (EncodesBy.link h (by simp; intro hh; omega) (fun x hx => ?_) (fun j => ?_))
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
        have := occupied_lt hx.2; omega
      · by_cases e : j = k
        · subst e; simp [hk]
        · by_cases hj : k ≤ j
          · simp [e, hj, show k + 1 ≤ j by omega]
          · simp [e, hj, show ¬ k + 1 ≤ j by omega]
    · next hk =>
      refine buildWords_encodes cells k occ head L hsz (EncodesBy.congr h (fun j => ?_))
      by_cases e : j = k
      · subst e; simp [hk]
      · by_cases hj : k ≤ j
        · simp [hj, show k + 1 ≤ j by omega]
        · simp [hj, show ¬ k + 1 ≤ j by omega]

/-- **The links built over the whole of a cell array encode its occupied
slots**, from any array of the right size. -/
theorem build_encodes {α : Type} (cells : Array (Option α)) (occ : Array Nat)
    (hsz : occ.size = 2 * cells.size) :
    ∃ L, Encodes cells (buildWords cells cells.size occ 0) (buildHead cells cells.size 0) L :=
  buildWords_encodes cells cells.size occ 0 [] hsz
    ⟨List.nodup_nil, fun i => by
      simp only [List.not_mem_nil, false_iff, Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro hi ho; have := occupied_lt ho; omega, rfl, trivial⟩

/-- **A head word of `0` means no slot is occupied.** -/
theorem EncodesBy.none_of_head_zero {P : Nat → Bool} {occ : Array Nat} {L : List Nat}
    (h : EncodesBy P occ 0 L) (i : Nat) : P i = false := by
  have hL : L = [] := by
    have e := h.head_eq
    cases L with
    | nil => rfl
    | cons a l => simp at e
  cases hp : P i with
  | false => rfl
  | true => have := (h.mem i).2 hp; rw [hL] at this; cases this

/-- **A nonzero head word names an occupied slot**: the head of the list. -/
theorem EncodesBy.head_mem {P : Nat → Bool} {occ : Array Nat} {head : Nat} {L : List Nat}
    (h : EncodesBy P occ head L) (hH : head ≠ 0) : P (head - 1) = true := by
  have e := h.head_eq
  cases L with
  | nil => simp at e; exact absurd e hH
  | cons a l =>
    simp only [List.head?_cons, code_some] at e
    subst e
    exact (h.mem a).1 (List.mem_cons_self ..)

end SeLe4n.Model.SlotOccupancy
