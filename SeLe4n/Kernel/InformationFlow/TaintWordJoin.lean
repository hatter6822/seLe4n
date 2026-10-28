/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-ZA ZA5.12: **the join on the words an object holds.**

An object holds its taint as plain words (`TaintWords`, ZA5.11), and the taint
step joins a source's taint into a sink's.  Over the list form a join walks tag
lists and builds the joined list; here it reads and writes words alone.

* `TaintWords.isEmpty` reads two scalars, and is exactly "decodes to the empty
  taint" (`TaintWords.decode_eq_empty_iff`).  This is what lets an untainted
  step decide that nothing moves without decoding anything.
* `TaintWords.insertWords` inserts one tag word into the words of a taint.  It
  is equal to the list form's `DeclassificationTaint.insert`
  (`TaintWords.insertWords_toWords`), slot by slot, through `getD_insertTag`.
* `TaintWords.join` is the words of the join of what two words decode to.  Its
  compiled form `TaintWords.joinImpl` (`@[csimp]`) checks both operands'
  shape on scalars, then inserts the source's tag words one at a time.

The only module this one imports is `Taint.lean`, the value type.
-/
import SeLe4n.Kernel.InformationFlow.Taint

namespace SeLe4n.Kernel

/-! ### Insertion, read slot by slot -/

/-- A list above `b` holds only entries above `b`. -/
theorem lt_of_tagsAbove : ∀ {b : Nat} {l : List Nat}, tagsAbove b l → ∀ y ∈ l, b < y
  | _, [], _, _, h => by simp at h
  | b, a :: rest, ⟨hba, hrest⟩, y, hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hba
      · exact Nat.lt_trans hba (lt_of_tagsAbove hrest y hy)

/-- The tail of a canonical list is canonical. -/
theorem tagsCanonical_tail {x : Nat} {xs : List Nat} (h : tagsCanonical (x :: xs)) :
    tagsCanonical xs := by
  cases xs with
  | nil => trivial
  | cons y ys => exact h.2

/-- Every entry of a canonical list past its head is above the head. -/
theorem head_le_getD {x : Nat} {xs : List Nat} (h : tagsCanonical (x :: xs)) :
    ∀ j, j < (x :: xs).length → x ≤ (x :: xs).getD j 0 := by
  intro j hj
  cases j with
  | zero => simp
  | succ k =>
    have hk : k < xs.length := by simpa using hj
    have hmem : xs.getD k 0 ∈ xs := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    have := lt_of_tagsAbove h (xs.getD k 0) hmem
    simp only [List.getD_cons_succ]
    omega

/-- **Slot `i` of an insertion**: an entry below the new tag keeps its slot, the
first slot not below it takes the tag, and every slot after takes the entry one
before it.  Read on a canonical list the tag is not in, which is the case
insertion places a tag in. -/
theorem getD_insertTag : ∀ (L : List Nat) (t : Nat), tagsCanonical L → t ∉ L → ∀ i,
    (insertTag L t).getD i 0 =
      if i < L.length ∧ L.getD i 0 < t then L.getD i 0
      else if i = 0 ∨ (i - 1 < L.length ∧ L.getD (i - 1) 0 < t) then t
      else L.getD (i - 1) 0
  | [], t, _, _, i => by
      cases i with
      | zero => simp [insertTag]
      | succ k => simp [insertTag]
  | x :: xs, t, hC, hN, i => by
      have hxt : t ≠ x := fun h => hN (h ▸ List.mem_cons_self)
      have hNxs : t ∉ xs := fun h => hN (List.mem_cons_of_mem _ h)
      by_cases hlt : t < x
      · have hge := head_le_getD hC
        simp only [insertTag, if_pos hlt]
        cases i with
        | zero => simp; omega
        | succ k =>
          have h1 : ¬ (k + 1 < (x :: xs).length ∧ (x :: xs).getD (k + 1) 0 < t) := by
            rintro ⟨hk, hv⟩; have := hge (k + 1) hk; omega
          have h2 : ¬ (k + 1 = 0 ∨ (k < (x :: xs).length ∧ (x :: xs).getD k 0 < t)) := by
            rintro (h | ⟨hk, hv⟩)
            · omega
            · have := hge k hk; omega
          rw [if_neg h1, if_neg (by simpa using h2)]
          simp
      · have hgt : x < t := by omega
        simp only [insertTag, if_neg hlt, if_neg hxt]
        cases i with
        | zero => simp [hgt]
        | succ k =>
          have ih := getD_insertTag xs t (tagsCanonical_tail hC) hNxs k
          simp only [List.getD_cons_succ, List.length_cons, Nat.add_sub_cancel]
          rw [ih]
          cases k with
          | zero => simp [hgt]
          | succ m =>
            simp only [List.getD_cons_succ, Nat.add_sub_cancel, Nat.add_lt_add_iff_right]
            simp

/-- Inserting a tag a canonical list holds leaves it as it is. -/
theorem insertTag_of_mem : ∀ (L : List Nat) (t : Nat), tagsCanonical L → t ∈ L →
    insertTag L t = L
  | [], _, _, h => by simp at h
  | x :: xs, t, hC, hM => by
      simp only [insertTag]
      rcases List.mem_cons.mp hM with rfl | hM
      · simp
      · have hx : x < t := lt_of_tagsAbove (by cases xs <;> first | exact hC | simp at hM) t hM
        rw [if_neg (by omega), if_neg (by omega),
          insertTag_of_mem xs t (tagsCanonical_tail hC) hM]

/-- Inserting a tag a list does not hold adds one entry. -/
theorem length_insertTag_of_not_mem : ∀ (L : List Nat) (t : Nat), t ∉ L →
    (insertTag L t).length = L.length + 1
  | [], _, _ => by simp [insertTag]
  | x :: xs, t, hN => by
      have hxt : t ≠ x := fun h => hN (h ▸ List.mem_cons_self)
      simp only [insertTag]
      split
      · simp
      · rw [List.length_cons, List.length_cons,
          length_insertTag_of_not_mem xs t (fun h => hN (List.mem_cons_of_mem _ h))]

/-- A canonical list of at most eight entries holds `x` exactly when one of
its first eight slots does. -/
theorem mem_iff_slots (L : List Nat) (hL : L.length ≤ maxTaintTags) (x : Nat) :
    x ∈ L ↔
      (0 < L.length ∧ L.getD 0 0 = x) ∨ (1 < L.length ∧ L.getD 1 0 = x) ∨
      (2 < L.length ∧ L.getD 2 0 = x) ∨ (3 < L.length ∧ L.getD 3 0 = x) ∨
      (4 < L.length ∧ L.getD 4 0 = x) ∨ (5 < L.length ∧ L.getD 5 0 = x) ∨
      (6 < L.length ∧ L.getD 6 0 = x) ∨ (7 < L.length ∧ L.getD 7 0 = x) := by
  simp only [maxTaintTags] at hL
  match L, hL with
  | [], _ => simp
  | [a], _ => simp [eq_comm]
  | [a, b], _ => simp [eq_comm]
  | [a, b, c], _ => simp [eq_comm]
  | [a, b, c, d], _ => simp [eq_comm]
  | [a, b, c, d, e], _ => simp [eq_comm]
  | [a, b, c, d, e, f], _ => simp [eq_comm]
  | [a, b, c, d, e, f, g], _ => simp [eq_comm]
  | [a, b, c, d, e, f, g, h], _ => simp [eq_comm]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hL => simp at hL

namespace DeclassificationTaint

/-- Every slot of a taint's tag list fits a word. -/
theorem getD_fit (T : DeclassificationTaint) (j : Nat) : T.tags.getD j 0 < UInt64.size := by
  by_cases hj : j < T.tags.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact T.tags_fit _ (List.getElem_mem hj)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    decide

/-- Two taints with the same data fields have the same words. -/
theorem toWords_congr {A B : DeclassificationTaint} (hs : A.saturated = B.saturated)
    (ht : A.tags = B.tags) : A.toWords = B.toWords := by
  simp only [toWords, hs, ht]

end DeclassificationTaint

theorem toUInt64_toNat_of_lt {n : Nat} (h : n < UInt64.size) : n.toUInt64.toNat = n := by
  simp [Nat.toUInt64, Nat.mod_eq_of_lt h]

theorem toUInt64_lt_iff {n : Nat} (h : n < UInt64.size) (t : UInt64) :
    n.toUInt64 < t ↔ n < t.toNat := by
  rw [UInt64.lt_iff_toNat_lt, toUInt64_toNat_of_lt h]

theorem toUInt64_eq_iff {n : Nat} (h : n < UInt64.size) (t : UInt64) :
    n.toUInt64 = t ↔ n = t.toNat := by
  rw [← UInt64.toNat_inj, toUInt64_toNat_of_lt h]

namespace TaintWords

/-- The words of the saturated taint (`top_toWords`). -/
@[inline] def topWords : TaintWords := { saturated := true }

@[simp] theorem top_toWords : DeclassificationTaint.top.toWords = topWords := rfl

/-- **The words name no provenance**, read off two scalars
(`decode_eq_empty_iff`). -/
@[inline] def isEmpty (w : TaintWords) : Bool := w.count == 0 && !w.saturated

theorem decode_eq_empty_iff (w : TaintWords) :
    w.decode = DeclassificationTaint.empty ↔ w.isEmpty = true := by
  unfold decode isEmpty
  by_cases hc : w.count = 0
  · have hl : w.toList = [] := by simp [toList, hc]
    simp only [hl, List.map_nil]
    rw [dif_pos (by rfl)]
    simp [DeclassificationTaint.empty, hc]
  · have hne : w.toList ≠ [] := by
      simp only [toList, ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨hc, by simp⟩
    have hb : (w.count == 0) = false := by simpa using hc
    simp only [hb, Bool.false_and, Bool.false_eq_true, iff_false]
    split
    · intro h
      have := congrArg DeclassificationTaint.tags h
      simp [DeclassificationTaint.empty] at this
      exact hne this
    · intro h
      have := congrArg DeclassificationTaint.saturated h
      simp [DeclassificationTaint.empty, DeclassificationTaint.top] at this

/-- WS-ZA ZA5.12: **one tag word inserted into the words of a taint**, read and
written as words: the words of `DeclassificationTaint.insert`
(`insertWords_toWords`).  A tag already held leaves the words as they are; a
ninth tag saturates; otherwise each slot below the tag keeps its word, the
first slot not below it takes the tag, and each slot after takes the word one
before it (`getD_insertTag`). -/
@[inline] def insertWords (w : TaintWords) (t : UInt64) : TaintWords :=
  if w.saturated then topWords
  else
    let c := w.count
    let l0 := decide (0 < c) && decide (w.tag0 < t)
    let l1 := decide (1 < c) && decide (w.tag1 < t)
    let l2 := decide (2 < c) && decide (w.tag2 < t)
    let l3 := decide (3 < c) && decide (w.tag3 < t)
    let l4 := decide (4 < c) && decide (w.tag4 < t)
    let l5 := decide (5 < c) && decide (w.tag5 < t)
    let l6 := decide (6 < c) && decide (w.tag6 < t)
    let l7 := decide (7 < c) && decide (w.tag7 < t)
    if (decide (0 < c) && w.tag0 == t) || (decide (1 < c) && w.tag1 == t) ||
        (decide (2 < c) && w.tag2 == t) || (decide (3 < c) && w.tag3 == t) ||
        (decide (4 < c) && w.tag4 == t) || (decide (5 < c) && w.tag5 == t) ||
        (decide (6 < c) && w.tag6 == t) || (decide (7 < c) && w.tag7 == t) then w
    else if 8 ≤ c then topWords
    else
      { tag0 := if l0 then w.tag0 else t
        tag1 := if l1 then w.tag1 else if l0 then t else w.tag0
        tag2 := if l2 then w.tag2 else if l1 then t else w.tag1
        tag3 := if l3 then w.tag3 else if l2 then t else w.tag2
        tag4 := if l4 then w.tag4 else if l3 then t else w.tag3
        tag5 := if l5 then w.tag5 else if l4 then t else w.tag4
        tag6 := if l6 then w.tag6 else if l5 then t else w.tag5
        tag7 := if l7 then w.tag7 else if l6 then t else w.tag6
        count := c + 1
        saturated := false }

/-- Slot `i` of an insertion, as words. -/
theorem slot_insertTag (T : DeclassificationTaint) (t : UInt64) (hm : t.toNat ∉ T.tags)
    (i : Nat) :
    ((insertTag T.tags t.toNat).getD i 0).toUInt64 =
      if (decide (i < T.tags.length) && decide ((T.tags.getD i 0).toUInt64 < t)) then
        (T.tags.getD i 0).toUInt64
      else if (decide (i = 0) || (decide (i - 1 < T.tags.length) &&
          decide ((T.tags.getD (i - 1) 0).toUInt64 < t))) then t
      else (T.tags.getD (i - 1) 0).toUInt64 := by
  rw [getD_insertTag _ _ T.tags_canonical hm]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    toUInt64_lt_iff (T.getD_fit _)]
  by_cases hA : i < T.tags.length ∧ T.tags.getD i 0 < t.toNat
  · rw [if_pos hA, if_pos hA]
  · rw [if_neg hA, if_neg hA]
    by_cases hB : i = 0 ∨ i - 1 < T.tags.length ∧ T.tags.getD (i - 1) 0 < t.toNat
    · rw [if_pos hB, if_pos hB]; simp
    · rw [if_neg hB, if_neg hB]

/-- A slot's word is the tag word exactly when the slot is the tag. -/
theorem slot_beq (T : DeclassificationTaint) (j : Nat) (t : UInt64) :
    ((T.tags.getD j 0).toUInt64 == t) = decide (T.tags.getD j 0 = t.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  exact toUInt64_eq_iff (T.getD_fit j) t

/-- WS-ZA ZA5.12: **the word insertion is the list insertion**, on the words a
taint is written as. -/
theorem insertWords_toWords (T : DeclassificationTaint) (t : UInt64) :
    T.toWords.insertWords t = (T.insert t.toNat).toWords := by
  cases hs : T.saturated
  · have hsW : T.toWords.saturated = false := by simp [DeclassificationTaint.toWords, hs]
    have hIns : T.insert t.toNat =
        if h : (insertTag T.tags t.toNat).length ≤ maxTaintTags then
          ⟨false, insertTag T.tags t.toNat, h, insertTag_canonical T.tags t.toNat T.tags_canonical,
            fun a ha => by
              rcases (mem_insertTag T.tags t.toNat a).mp ha with rfl | ha
              · exact UInt64.toNat_lt_size t
              · exact T.tags_fit a ha⟩
        else DeclassificationTaint.top := by
      unfold DeclassificationTaint.insert
      rw [if_neg (by simp [hs]), dif_pos (UInt64.toNat_lt_size t)]
    rw [hIns]
    unfold insertWords
    simp only [hsW, Bool.false_eq_true, ↓reduceIte]
    simp only [DeclassificationTaint.toWords, slot_beq]
    have hb := T.tags_bounded
    by_cases hm : t.toNat ∈ T.tags
    · have hD := (mem_iff_slots T.tags hb t.toNat).mp hm
      have hI := insertTag_of_mem T.tags t.toNat T.tags_canonical hm
      rw [if_pos (by simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] using hD),
        dif_pos (by rw [hI]; exact hb)]
      simp only [hI, hs]
    · have hD := mt (mem_iff_slots T.tags hb t.toNat).mpr hm
      have hL := length_insertTag_of_not_mem T.tags t.toNat hm
      rw [if_neg (by simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] using hD)]
      by_cases h8 : 8 ≤ T.tags.length
      · rw [if_pos h8, dif_neg (by rw [hL]; simp only [maxTaintTags]; omega)]
        rfl
      · rw [if_neg h8, dif_pos (by rw [hL]; simp only [maxTaintTags]; omega)]
        simp only [hL, slot_insertTag T t hm]
        simp
  · have hsW : T.toWords.saturated = true := by simp [DeclassificationTaint.toWords, hs]
    unfold insertWords
    rw [if_pos hsW, DeclassificationTaint.insert_saturated hs]
    rfl

/-- WS-ZA ZA5.12: **do the words name a taint as written?**  The tag words in
use strictly increase, read on scalars (`canonical_eq`): the check `decode`
makes on the tag list, made on the words. -/
@[inline] def canonical (w : TaintWords) : Bool :=
  let c := w.count
  (decide (c ≤ 1) || decide (w.tag0 < w.tag1)) && (decide (c ≤ 2) || decide (w.tag1 < w.tag2)) &&
  (decide (c ≤ 3) || decide (w.tag2 < w.tag3)) && (decide (c ≤ 4) || decide (w.tag3 < w.tag4)) &&
  (decide (c ≤ 5) || decide (w.tag4 < w.tag5)) && (decide (c ≤ 6) || decide (w.tag5 < w.tag6)) &&
  (decide (c ≤ 7) || decide (w.tag6 < w.tag7))

theorem toList_of_count (w : TaintWords) :
    w.toList = [w.tag0, w.tag1, w.tag2, w.tag3, w.tag4, w.tag5, w.tag6, w.tag7].take w.count :=
  rfl

theorem canonical_eq (w : TaintWords) :
    w.canonical = tagsCanonicalB (w.toList.map UInt64.toNat) := by
  rw [toList_of_count]
  unfold canonical
  match w.count with
  | 0 => rfl
  | 1 => rfl
  | 2 => simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt]
  | 3 => simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt]
  | 4 => simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt, Bool.and_assoc]
  | 5 => simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt, Bool.and_assoc]
  | 6 => simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt, Bool.and_assoc]
  | 7 => simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt, Bool.and_assoc]
  | n + 8 =>
    simp [tagsCanonicalB, tagsAboveB, UInt64.lt_iff_toNat_lt, Bool.and_assoc,
      List.take_of_length_le (by simp : [w.tag0, w.tag1, w.tag2, w.tag3, w.tag4, w.tag5, w.tag6,
        w.tag7].length ≤ n + 8)]

/-- Words that fail the check decode to the saturated taint. -/
theorem decode_of_not_canonical {w : TaintWords} (h : w.canonical = false) :
    w.decode = DeclassificationTaint.top := by
  unfold decode
  rw [dif_neg (by rw [← canonical_eq, h]; simp)]

/-- The words as written of what canonical words decode to: the tag words in
use, zero past them, the count capped at the eight words there are. -/
@[inline] def written (w : TaintWords) : TaintWords :=
  let c := w.count
  { tag0 := if 0 < c then w.tag0 else 0, tag1 := if 1 < c then w.tag1 else 0,
    tag2 := if 2 < c then w.tag2 else 0, tag3 := if 3 < c then w.tag3 else 0,
    tag4 := if 4 < c then w.tag4 else 0, tag5 := if 5 < c then w.tag5 else 0,
    tag6 := if 6 < c then w.tag6 else 0, tag7 := if 7 < c then w.tag7 else 0,
    count := if c ≤ 8 then c else 8, saturated := w.saturated }

theorem decode_toWords_of_canonical {w : TaintWords} (h : w.canonical = true) :
    w.decode.toWords = w.written := by
  unfold decode
  rw [dif_pos (by rw [← canonical_eq, h])]
  simp only [DeclassificationTaint.toWords, written, toList_of_count]
  match w.count with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | 4 => simp
  | 5 => simp
  | 6 => simp
  | 7 => simp
  | n + 8 =>
    simp [List.take_of_length_le (by simp : [w.tag0, w.tag1, w.tag2, w.tag3, w.tag4, w.tag5,
      w.tag6, w.tag7].length ≤ n + 8)]

theorem decode_tags_of_canonical {w : TaintWords} (h : w.canonical = true) :
    w.decode.tags = w.toList.map UInt64.toNat := by
  unfold decode
  rw [dif_pos (by rw [← canonical_eq, h])]

theorem decode_saturated_of_canonical {w : TaintWords} (h : w.canonical = true) :
    w.decode.saturated = w.saturated := by
  unfold decode
  rw [dif_pos (by rw [← canonical_eq, h])]

/-- Inserting into the saturated taint stays saturated, along any list. -/
theorem foldl_insert_top (l : List Nat) :
    l.foldl (fun acc t => acc.insert t) DeclassificationTaint.top = DeclassificationTaint.top := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, DeclassificationTaint.insert_saturated (rfl : DeclassificationTaint.top.saturated = true)]
    exact ih

/-- WS-ZA ZA5.12: **the join, on words**: the words of the join of what two
words decode to.  Compiled as `joinImpl` (`join_eq_impl`). -/
def join (a b : TaintWords) : TaintWords :=
  (DeclassificationTaint.join a.decode b.decode).toWords

/-- WS-ZA ZA5.12: `join` as compiled, on scalars: words that name no taint as
written decode to the saturated taint, so either operand failing the check, or
a saturated source, gives the saturated words; otherwise the source's tag words
in use are inserted one at a time (`insertWords`), building no tag list. -/
def joinImpl (a b : TaintWords) : TaintWords :=
  if a.canonical && b.canonical then
    if b.saturated then topWords
    else
      let cb := b.count
      let r := a.written
      let r := if 0 < cb then r.insertWords b.tag0 else r
      let r := if 1 < cb then r.insertWords b.tag1 else r
      let r := if 2 < cb then r.insertWords b.tag2 else r
      let r := if 3 < cb then r.insertWords b.tag3 else r
      let r := if 4 < cb then r.insertWords b.tag4 else r
      let r := if 5 < cb then r.insertWords b.tag5 else r
      let r := if 6 < cb then r.insertWords b.tag6 else r
      if 7 < cb then r.insertWords b.tag7 else r
  else topWords

@[csimp] theorem join_eq_impl : @join = @joinImpl := by
  funext a b
  unfold join joinImpl
  cases ha : a.canonical
  · rw [decode_of_not_canonical ha]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    unfold DeclassificationTaint.join
    split
    · rfl
    · rw [foldl_insert_top]; rfl
  · cases hb : b.canonical
    · rw [decode_of_not_canonical hb]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      simp [DeclassificationTaint.join, DeclassificationTaint.top]; rfl
    · simp only [Bool.and_self, ↓reduceIte]
      unfold DeclassificationTaint.join
      rw [decode_saturated_of_canonical hb, decode_tags_of_canonical hb]
      cases hs : b.saturated
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← decode_toWords_of_canonical ha, toList_of_count]
        match b.count with
        | 0 => simp
        | 1 => simp [insertWords_toWords]
        | 2 => simp [insertWords_toWords]
        | 3 => simp [insertWords_toWords]
        | 4 => simp [insertWords_toWords]
        | 5 => simp [insertWords_toWords]
        | 6 => simp [insertWords_toWords]
        | 7 => simp [insertWords_toWords]
        | n + 8 =>
          simp [insertWords_toWords, List.take_of_length_le (by simp : [b.tag0, b.tag1, b.tag2,
            b.tag3, b.tag4, b.tag5, b.tag6, b.tag7].length ≤ n + 8)]
      · rfl
