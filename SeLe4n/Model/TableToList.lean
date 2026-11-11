-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Bridge

/-!
# A table's entry list and its lookups

`RHTable.toList` lists exactly the entries `get?` finds, each key once.  The
freeze proofs read these facts (Q6-A), and since WS-UC UC2 so do the walks the
kernel makes over the object table in place of the retired object index: a
walk's result is stated over the entries, and the entries are the stored
objects whatever order the table's slots hold them in.
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- Q6-A helpers: toList ↔ slot characterization
-- ============================================================================

/-- Q6-A helper: The fold that builds `toList` collects exactly the occupied
slot entries. Membership in the fold result iff in the initial accumulator or
from an occupied slot in the list. -/
theorem foldl_toList_mem_forward [BEq κ] [Hashable κ] [LawfulBEq κ]
    (slots : List (Option (RHEntry κ ν))) (acc : List (κ × ν)) (k : κ) (v : ν)
    (h : (k, v) ∈ slots.foldl (fun acc slot =>
      match slot with | none => acc | some e => (e.key, e.value) :: acc) acc) :
    (k, v) ∈ acc ∨ ∃ (entry : RHEntry κ ν), some entry ∈ slots ∧
      entry.key = k ∧ entry.value = v := by
  induction slots generalizing acc with
  | nil => exact Or.inl h
  | cons hd tl ih =>
    simp only [List.foldl_cons] at h
    have ih' := @ih
    cases hd with
    | none =>
      have h' : (k, v) ∈ tl.foldl (fun acc slot =>
          match slot with | none => acc | some e => (e.key, e.value) :: acc) acc := h
      rcases ih' acc h' with h1 | ⟨e, hE, hK, hV⟩
      · exact Or.inl h1
      · exact Or.inr ⟨e, .tail _ hE, hK, hV⟩
    | some entry =>
      have h' : (k, v) ∈ tl.foldl (fun acc slot =>
          match slot with | none => acc | some e => (e.key, e.value) :: acc)
          ((entry.key, entry.value) :: acc) := h
      rcases ih' ((entry.key, entry.value) :: acc) h' with h1 | ⟨e, hE, hK, hV⟩
      · cases h1 with
        | head => exact Or.inr ⟨entry, .head _, rfl, rfl⟩
        | tail _ h => exact Or.inl h
      · exact Or.inr ⟨e, .tail _ hE, hK, hV⟩

/-- Q6-A helper: If an occupied slot entry is in the list, its key-value pair
is in the fold result. -/
theorem foldl_toList_mem_backward [BEq κ] [Hashable κ] [LawfulBEq κ]
    (slots : List (Option (RHEntry κ ν))) (acc : List (κ × ν))
    (entry : RHEntry κ ν) (hE : some entry ∈ slots) :
    (entry.key, entry.value) ∈ slots.foldl (fun acc slot =>
      match slot with | none => acc | some e => (e.key, e.value) :: acc) acc := by
  induction slots generalizing acc with
  | nil => cases hE
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases hE with
    | head =>
      -- hd = some entry, so we prepend (entry.key, entry.value) to acc
      -- Then we fold over tl starting from (entry.key, entry.value) :: acc
      -- The result contains everything in (entry.key, entry.value) :: acc
      -- by an accumulator-monotonicity argument
      exact foldl_toList_acc_subset tl _ _ (List.Mem.head _)
    | tail _ h =>
      cases hd with
      | none => exact ih acc h
      | some e => exact ih ((e.key, e.value) :: acc) h
where
  /-- Accumulator monotonicity: if `x ∈ acc`, then `x` is in the fold result. -/
  foldl_toList_acc_subset [BEq κ] [Hashable κ] [LawfulBEq κ]
      (slots : List (Option (RHEntry κ ν))) (acc : List (κ × ν))
      (x : κ × ν) (hx : x ∈ acc) :
      x ∈ slots.foldl (fun acc slot =>
        match slot with | none => acc | some e => (e.key, e.value) :: acc) acc := by
    induction slots generalizing acc with
    | nil => exact hx
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      cases hd with
      | none => exact ih acc hx
      | some e => exact ih ((e.key, e.value) :: acc) (List.Mem.tail _ hx)

-- ============================================================================
-- Q6-A: toList ↔ get? connection
-- ============================================================================

/-- Q6-A: If `rt.get? k = some v` and `invExt` holds, then `(k, v) ∈ rt.toList`.
Connects slot-level occupancy (via `get_some_slot_entry`) to list membership
(via the fold characterization). -/
theorem toList_contains_of_get [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (v : ν) (_hExt : rt.invExt)
    (hGet : rt.get? k = some v) :
    (k, v) ∈ rt.toList := by
  -- Extract the slot entry from get?
  have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := RHTable.get_some_slot_entry rt k v hGet
  have hKeyEq : e.key = k := eq_of_beq hKeyE
  -- e is in the slots array at position p
  have hIdx : p < rt.slots.size := rt.hSlotsLen ▸ hp
  -- Show (some e) ∈ rt.slots.toList
  have hListIdx : p < rt.slots.toList.length := by
    simp [Array.length_toList]; exact hIdx
  have hSlotVal : rt.slots.toList[p] = some e := by
    rw [Array.getElem_toList]; exact hSlotP
  have hSlotInList : some e ∈ rt.slots.toList :=
    List.mem_of_getElem hSlotVal
  -- Use foldl_toList_mem_backward to conclude (e.key, e.value) is in toList
  unfold RHTable.toList RHTable.fold
  rw [← Array.foldl_toList]
  have := foldl_toList_mem_backward rt.slots.toList [] e hSlotInList
  rw [hKeyEq, hValE] at this
  exact this

/-- Q6-A: If `rt.get? k = none` and `invExt` holds, then no entry with key `k`
appears in `rt.toList`. Connects slot-level absence to list absence. -/
theorem toList_absent_of_get_none [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (hExt : rt.invExt)
    (hNone : rt.get? k = none) (v : ν) :
    (k, v) ∉ rt.toList := by
  intro hMem
  -- If (k, v) ∈ toList, there's a slot entry with key = k
  unfold RHTable.toList RHTable.fold at hMem
  rw [← Array.foldl_toList] at hMem
  rcases foldl_toList_mem_forward rt.slots.toList [] k v hMem with h | ⟨e, hE, hK, hV⟩
  · cases h
  · -- e is in slots.toList with e.key = k
    -- This contradicts get_none_no_matching_entry
    have hAbsent := RHTable.get_none_no_matching_entry rt k hExt hNone
    -- Find the slot index for e
    have ⟨p, hP⟩ := List.mem_iff_getElem.mp hE
    have hLen : p < rt.slots.toList.length := hP.1
    have hSlotEq : rt.slots.toList[p] = some e := hP.2
    have hIdx : p < rt.slots.size := by
      simp [Array.length_toList] at hLen; exact hLen
    have hp' : p < rt.capacity := by rw [← rt.hSlotsLen]; exact hIdx
    have hSlotArr : rt.slots[p]'(rt.hSlotsLen ▸ hp') = some e := by
      rw [← Array.getElem_toList]; exact hSlotEq
    have hFalse := hAbsent p hp' e hSlotArr
    rw [hK] at hFalse
    simp at hFalse

-- ============================================================================
-- Q6-A: toList has no duplicate keys (from noDupKeys on slots)
-- ============================================================================

/-- Q6-A helper: Fold invariant — the fold that builds `toList` produces a
`Nodup` list whose entries have pairwise distinct keys, when the source slots
satisfy `noDupKeys`. The combined invariant (Nodup ∧ key-unique) avoids needing
separate inductions. -/
theorem foldl_noDupKeys_inv [BEq κ] [Hashable κ] [LawfulBEq κ]
    (slots : List (Option (RHEntry κ ν)))
    (acc : List (κ × ν))
    (hAccNodup : acc.Nodup)
    (hAccKeyUniq : ∀ (a b : κ × ν), a ∈ acc → b ∈ acc →
      (a.1 == b.1) = true → a = b)
    (hSlotsND : ∀ (i j : Nat) (hi : i < slots.length) (hj : j < slots.length)
      (ei ej : RHEntry κ ν),
      slots[i] = some ei → slots[j] = some ej → (ei.key == ej.key) = true → i = j)
    (hDisjoint : ∀ (a : κ × ν), a ∈ acc →
      ∀ (j : Nat) (hj : j < slots.length) (ej : RHEntry κ ν),
      slots[j] = some ej → ¬(a.1 == ej.key) = true) :
    let result := slots.foldl (fun acc slot =>
      match slot with | none => acc | some e => (e.key, e.value) :: acc) acc
    result.Nodup ∧ ∀ (a b : κ × ν), a ∈ result → b ∈ result →
      (a.1 == b.1) = true → a = b := by
  induction slots generalizing acc with
  | nil => exact ⟨hAccNodup, hAccKeyUniq⟩
  | cons hd tl ih =>
    simp only [List.foldl]
    have hConsLen : (hd :: tl).length = tl.length + 1 := List.length_cons
    cases hd with
    | none =>
      exact ih acc hAccNodup hAccKeyUniq
        (fun i j hi hj ei ej hSi hSj hBeq =>
          have h := hSlotsND (i + 1) (j + 1)
            (by rw [hConsLen]; omega) (by rw [hConsLen]; omega) ei ej
            (by simp [hSi]) (by simp [hSj]) hBeq
          by omega)
        (fun a hA j hj ej hSj =>
          hDisjoint a hA (j + 1) (by rw [hConsLen]; omega) ej (by simp [hSj]))
    | some e =>
      apply ih ((e.key, e.value) :: acc)
      · -- Nodup for (e.key, e.value) :: acc
        rw [List.nodup_cons]
        constructor
        · -- (e.key, e.value) ∉ acc
          intro hMem
          -- If (e.key, e.value) ∈ acc, then e.key matches an acc entry's key
          have hSelf : (((e.key, e.value) : κ × ν).1 == e.key) = true := beq_self_eq_true _
          exact hDisjoint (e.key, e.value) hMem 0 (by rw [hConsLen]; omega) e rfl hSelf
        · exact hAccNodup
      · -- Key uniqueness for (e.key, e.value) :: acc
        intro a b hA hB hBeq
        cases hA with
        | head =>
          cases hB with
          | head => rfl
          | tail _ hB' =>
            exfalso
            have : (b.1 == e.key) = true := by rw [BEq.comm]; exact hBeq
            exact hDisjoint b hB' 0 (by rw [hConsLen]; omega) e rfl this
        | tail _ hA' =>
          cases hB with
          | head =>
            exfalso
            exact hDisjoint a hA' 0 (by rw [hConsLen]; omega) e rfl hBeq
          | tail _ hB' =>
            exact hAccKeyUniq a b hA' hB' hBeq
      · -- Slots tl have unique keys
        intro i j hi hj ei ej hSi hSj hBeq
        have h := hSlotsND (i + 1) (j + 1)
          (by rw [hConsLen]; omega) (by rw [hConsLen]; omega) ei ej
          (by simp [hSi]) (by simp [hSj]) hBeq
        omega
      · -- Disjointness for new acc and tl
        intro a hA j hj ej hSj
        cases hA with
        | head =>
          intro hBeq
          have h := hSlotsND 0 (j + 1)
            (by rw [hConsLen]; omega) (by rw [hConsLen]; omega) e ej rfl
            (by simp [hSj]) hBeq
          omega
        | tail _ hA' =>
          exact hDisjoint a hA' (j + 1) (by rw [hConsLen]; omega) ej (by simp [hSj])

/-- Q6-A: `toList` produces a list with no duplicate keys when `noDupKeys` holds.
This bridges the slot-level `noDupKeys` invariant to a list-level property. -/
theorem toList_noDupKeys [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (hExt : rt.invExt) :
    ∀ (i j : Nat) (hi : i < rt.toList.length) (hj : j < rt.toList.length),
      (rt.toList[i].1 == rt.toList[j].1) = true → i = j := by
  -- Establish combined Nodup + key-uniqueness on toList
  have hComb : rt.toList.Nodup ∧ ∀ (a b : κ × ν), a ∈ rt.toList → b ∈ rt.toList →
      (a.1 == b.1) = true → a = b := by
    unfold RHTable.toList RHTable.fold
    rw [← Array.foldl_toList]
    apply foldl_noDupKeys_inv rt.slots.toList []
    · exact List.nodup_nil
    · intro a b hA; cases hA
    · intro i j hi hj ei ej hSi hSj hBeq
      have hLen : rt.slots.toList.length = rt.slots.size := Array.length_toList
      have hi' : i < rt.slots.size := by omega
      have hj' : j < rt.slots.size := by omega
      have hi'' : i < rt.capacity := rt.hSlotsLen ▸ hi'
      have hj'' : j < rt.capacity := rt.hSlotsLen ▸ hj'
      have hSi' : rt.slots[i]'hi' = some ei := by
        have := (Array.getElem_toList (h := hi')).symm; rw [this]; exact hSi
      have hSj' : rt.slots[j]'hj' = some ej := by
        have := (Array.getElem_toList (h := hj')).symm; rw [this]; exact hSj
      exact hExt.2.2.1 i j hi'' hj'' ei ej hSi' hSj' hBeq
    · intro a hA; cases hA
  obtain ⟨hNodup, hKeyUniq⟩ := hComb
  -- Convert: toList[i].1 == toList[j].1 → toList[i] = toList[j] (by key uniq) → i = j (by Nodup)
  intro i j hi hj hBeq
  have hEqPair := hKeyUniq _ _ (List.getElem_mem ..) (List.getElem_mem ..) hBeq
  -- Nodup + equal elements → equal indices
  have hPw := List.pairwise_iff_getElem.mp hNodup
  rcases Nat.lt_or_ge i j with h | h
  · exact absurd hEqPair (hPw i j hi hj h)
  · rcases Nat.lt_or_ge j i with h' | h'
    · exact absurd hEqPair.symm (hPw j i hj hi h')
    · omega

-- ============================================================================
-- WS-SM SM3.A audit-pass-6 — reverse toList/get? bridge
-- ============================================================================

/-- WS-SM SM3.A audit-pass-6: reverse direction of `toList_contains_of_get` —
if `(k, v) ∈ rt.toList` and `invExt` holds, then `rt.get? k = some v`.

The forward direction (`toList_contains_of_get`) is at line 131 above.
This reverse direction closes the bidirectional bridge between
`RHTable.toList` membership and `RHTable.get?` lookups for keyed
queries.

**Proof outline**:
1. From `(k, v) ∈ rt.toList`, suppose `rt.get? k = none`.  By
   `toList_absent_of_get_none`, `(k, v) ∉ rt.toList` — contradiction.
2. So `rt.get? k = some v'` for some `v'`.  Need to show `v = v'`.
3. By `toList_contains_of_get` with `(k, v')`, `(k, v') ∈ rt.toList`.
4. By `toList_noDupKeys`, the indices of `(k, v)` and `(k, v')` in
   `toList` are equal (same key — uniqueness).  So `v = v'`. -/
theorem get_some_of_toList_contains [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (v : ν) (hExt : rt.invExt)
    (hMem : (k, v) ∈ rt.toList) :
    rt.get? k = some v := by
  -- Step 1: rt.get? k cannot be none (would contradict hMem via toList_absent_of_get_none).
  match hGet : rt.get? k with
  | none =>
      exact absurd hMem (toList_absent_of_get_none rt k hExt hGet v)
  | some v' =>
      -- Step 2: (k, v') ∈ toList by toList_contains_of_get.
      have hMem' : (k, v') ∈ rt.toList :=
        toList_contains_of_get rt k v' hExt hGet
      -- Step 3: Both (k, v) and (k, v') are in toList; they share a key.
      -- By toList_noDupKeys, their indices match, so the pairs are equal.
      obtain ⟨i, hi, hAti⟩ := List.mem_iff_getElem.mp hMem
      obtain ⟨j, hj, hAtj⟩ := List.mem_iff_getElem.mp hMem'
      have hKeyEq : (rt.toList[i].1 == rt.toList[j].1) = true := by
        rw [hAti, hAtj]; simp
      have hij := toList_noDupKeys rt hExt i j hi hj hKeyEq
      subst hij
      -- Now hAti : rt.toList[i] = (k, v) and hAtj : rt.toList[i] = (k, v') —
      -- so (k, v) = (k, v'), giving v = v'.
      have hEq : (k, v) = (k, v') := hAti.symm.trans hAtj
      have hVal : v = v' := (Prod.mk.inj hEq).2
      rw [hVal]

/-- WS-SM SM3.A audit-pass-6: bidirectional bridge between `RHTable.toList`
and `RHTable.get?` for keyed predicates, under `invExt`.

Captures the "list-quantification ↔ universal quantification on
lookups" pattern: for any predicate `P` on (key, value) pairs,

  toList.all (fun p => P p)  ↔  ∀ k v, get? k = some v → P (k, v)

The forward direction (`toList.all → ∀ get?`) uses
`toList_contains_of_get` to lift each `get?` hit into a `toList`
membership, then projects out `P`.

The reverse direction (`∀ get? → toList.all`) uses
`get_some_of_toList_contains` to lift each `toList` membership into
a `get?` hit, then applies the hypothesis. -/
theorem toList_all_iff_forall_get_some [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (P : κ × ν → Bool) (hExt : rt.invExt) :
    rt.toList.all P = true ↔
    ∀ k v, rt.get? k = some v → P (k, v) = true := by
  constructor
  · -- Forward: toList.all → ∀ get?
    intro hAll k v hGet
    rw [List.all_eq_true] at hAll
    exact hAll _ (toList_contains_of_get rt k v hExt hGet)
  · -- Backward: ∀ get? → toList.all
    intro hForall
    rw [List.all_eq_true]
    intro p hMem
    -- For any pair `p = (p.1, p.2)`, apply `get_some_of_toList_contains`
    -- to get `rt.get? p.1 = some p.2`, then apply the hypothesis.
    -- Destructure `p` to make the pair structure explicit (avoids
    -- needing `Prod.mk.eta` which does not exist in this Lean version).
    obtain ⟨k, v⟩ := p
    have hGet := get_some_of_toList_contains rt k v hExt hMem
    exact hForall k v hGet


-- ============================================================================
-- WS-UC UC2: a fold over a table is a fold over any list of its keys
-- ============================================================================

/-- WS-UC UC2: two duplicate-free lists with the same members are permutations
of each other. -/
theorem perm_of_nodup_of_mem_iff {α : Type} [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  have c1 := List.nodup_iff_count.mp h₁ a
  have c2 := List.nodup_iff_count.mp h₂ a
  by_cases ha : a ∈ l₁
  · have p1 := List.count_pos_iff.mpr ha
    have p2 := List.count_pos_iff.mpr ((h a).mp ha)
    omega
  · rw [List.count_eq_zero_of_not_mem ha,
      List.count_eq_zero_of_not_mem (fun h' => ha ((h a).mpr h'))]

/-- WS-UC UC2: the keys a table holds, listed once each. -/
theorem toList_keys_nodup [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (hExt : rt.invExt) : (rt.toList.map Prod.fst).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at heq
  have := toList_noDupKeys rt hExt i j hi hj (by rw [heq]; exact beq_self_eq_true _)
  omega

/-- WS-UC UC2: a key is listed exactly when the table holds it. -/
theorem mem_toList_keys_iff [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (hExt : rt.invExt) (k : κ) :
    k ∈ rt.toList.map Prod.fst ↔ rt.get? k ≠ none := by
  constructor
  · intro hm
    obtain ⟨⟨k', v⟩, hp, hk⟩ := List.mem_map.mp hm
    simp only at hk; subst hk
    rw [get_some_of_toList_contains rt k' v hExt hp]; simp
  · intro hne
    cases hg : rt.get? k with
    | none => exact absurd hg hne
    | some v => exact List.mem_map.mpr ⟨(k, v), toList_contains_of_get rt k v hExt hg, rfl⟩

private theorem foldl_option_step [BEq κ] [Hashable κ] [LawfulBEq κ] {γ : Type}
    (xs : List (Option (RHEntry κ ν))) (step : γ → Option (RHEntry κ ν) → γ)
    (F : γ → κ × ν → γ) (hN : ∀ a, step a none = a)
    (hS : ∀ a e, step a (some e) = F a (e.key, e.value)) (acc : γ) :
    xs.foldl step acc = (xs.filterMap (fun o => o.map fun e => (e.key, e.value))).foldl F acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons o xs ih =>
    cases o with
    | none => simp only [List.foldl_cons, hN, List.filterMap_cons, Option.map_none]; exact ih acc
    | some e =>
      simp only [List.foldl_cons, hS, List.filterMap_cons, Option.map_some]; exact ih _

private theorem foldl_cons_acc {α : Type} (P L : List α) :
    P.foldl (fun a p => p :: a) L = P.reverse ++ L := by
  induction P generalizing L with
  | nil => rfl
  | cons x P ih => simp [ih]

/-- WS-UC UC2: **a fold over a table is a fold over its entry list**, in the
order the slots hold them (`toList` lists them backwards). -/
theorem fold_eq_toList_reverse_foldl [BEq κ] [Hashable κ] [LawfulBEq κ] {γ : Type}
    (rt : RHTable κ ν) (init : γ) (f : γ → κ → ν → γ) :
    rt.fold init f = rt.toList.reverse.foldl (fun acc p => f acc p.1 p.2) init := by
  have hF : rt.fold init f = (rt.slots.toList.filterMap
      (fun o => o.map fun e => (e.key, e.value))).foldl (fun acc p => f acc p.1 p.2) init := by
    unfold RHTable.fold; rw [← Array.foldl_toList]
    exact foldl_option_step _ _ _ (fun _ => rfl) (fun _ _ => rfl) _
  have hT : rt.toList = (rt.slots.toList.filterMap
      (fun o => o.map fun e => (e.key, e.value))).foldl (fun a p => p :: a) [] := by
    unfold RHTable.toList RHTable.fold; rw [← Array.foldl_toList]
    exact foldl_option_step _ _ _ (fun _ => rfl) (fun _ _ => rfl) _
  rw [hF, hT, foldl_cons_acc]
  simp

private theorem foldl_congr_mem {α γ : Type} (l : List α) (f g : γ → α → γ)
    (h : ∀ acc a, a ∈ l → f acc a = g acc a) (init : γ) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h init a List.mem_cons_self]
    exact ih (fun acc b hb => h acc b (List.mem_cons_of_mem _ hb)) _

/-- WS-UC UC2: **a walk over a table does not depend on the order it visits the
keys in**: when each step reads only the key it is handed (`hfg`) and two steps
commute (`comm`), folding over the table is folding over any duplicate-free list
of exactly its keys.  What lets a kernel walk over the object table stand for
the specification's walk over the ghost object index. -/
theorem fold_eq_foldl_of_keys [BEq κ] [Hashable κ] [LawfulBEq κ] {γ : Type}
    (rt : RHTable κ ν) (hExt : rt.invExt) (l : List κ) (hl : l.Nodup)
    (hMem : ∀ k, k ∈ l ↔ rt.get? k ≠ none)
    (f : γ → κ → ν → γ) (g : γ → κ → γ)
    (hfg : ∀ acc k v, rt.get? k = some v → f acc k v = g acc k)
    (comm : ∀ z x y, g (g z x) y = g (g z y) x) (init : γ) :
    rt.fold init f = l.foldl g init := by
  rw [fold_eq_toList_reverse_foldl]
  rw [foldl_congr_mem _ _ (fun acc p => g acc p.1) (fun acc p hp =>
    hfg acc p.1 p.2 (get_some_of_toList_contains rt p.1 p.2 hExt (List.mem_reverse.mp hp)))]
  rw [← List.foldl_map (f := Prod.fst) (g := g)]
  apply List.Perm.foldl_eq' _ (fun x _ y _ z => comm z x y)
  apply perm_of_nodup_of_mem_iff
  · rw [List.map_reverse]; exact List.pairwise_reverse.mpr ((toList_keys_nodup rt hExt).imp fun h e => h e.symm)
  · exact hl
  · intro a
    rw [List.map_reverse, List.mem_reverse, mem_toList_keys_iff rt hExt, hMem]


private theorem mem_foldl_elim_cons {α β : Type} (g : α → Option β) (x : β) :
    ∀ (L : List α) (acc : List β),
      x ∈ L.foldl (fun acc p => (g p).elim acc (· :: acc)) acc ↔ x ∈ acc ∨ ∃ p ∈ L, g p = some x
  | [], acc => by simp
  | p :: L, acc => by
    rw [List.foldl_cons, mem_foldl_elim_cons g x L]
    cases hg : g p with
    | none =>
      simp only [Option.elim_none, List.mem_cons, exists_eq_or_imp, hg, reduceCtorEq, false_or]
    | some y =>
      simp only [Option.elim_some, List.mem_cons, exists_eq_or_imp, hg, Option.some.injEq]
      constructor
      · rintro ((rfl | h) | h) <;> simp_all
      · rintro (h | rfl | h) <;> simp_all

/-- WS-UC UC2: **what a collecting walk over a table collects does not depend on
the order it visits the keys in**: `x` is collected exactly when some entry the
table holds yields it. -/
theorem mem_fold_elim_cons_iff [BEq κ] [Hashable κ] [LawfulBEq κ] {β : Type}
    (rt : RHTable κ ν) (hExt : rt.invExt) (g : κ → ν → Option β) (x : β) :
    x ∈ rt.fold [] (fun acc k v => (g k v).elim acc (· :: acc)) ↔
      ∃ k v, rt.get? k = some v ∧ g k v = some x := by
  rw [fold_eq_toList_reverse_foldl]
  rw [mem_foldl_elim_cons (fun p : κ × ν => g p.1 p.2) x]
  constructor
  · rintro (h | ⟨⟨k, v⟩, hp, hg⟩)
    · cases h
    · exact ⟨k, v, get_some_of_toList_contains rt k v hExt (List.mem_reverse.mp hp), hg⟩
  · rintro ⟨k, v, hkv, hg⟩
    exact Or.inr ⟨(k, v), List.mem_reverse.mpr (toList_contains_of_get rt k v hExt hkv), hg⟩

/-- WS-UC UC2: a table lists as many entries as it counts. -/
theorem toList_length [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (hExt : rt.invExt) : rt.toList.length = rt.size := by
  have hT : rt.toList = (rt.slots.toList.filterMap
      (fun o => o.map fun e => (e.key, e.value))).foldl (fun a p => p :: a) [] := by
    unfold RHTable.toList RHTable.fold; rw [← Array.foldl_toList]
    exact foldl_option_step _ _ _ (fun _ => rfl) (fun _ _ => rfl) _
  rw [hT, foldl_cons_acc, List.append_nil, List.length_reverse, hExt.1.sizeCount]
  unfold countOccupied
  generalize rt.slots.toList = xs
  induction xs with
  | nil => rfl
  | cons o xs ih => cases o <;> simp [ih]

/-- WS-UC UC2: **a table whose keys another table also holds is no larger**. -/
theorem size_le_size_of_present [BEq κ] [Hashable κ] [LawfulBEq κ]
    (t t' : RHTable κ ν) (hExt : t.invExt) (hExt' : t'.invExt)
    (h : ∀ k, t.get? k ≠ none → t'.get? k ≠ none) : t.size ≤ t'.size := by
  rw [← toList_length t hExt, ← List.length_map (f := Prod.fst)]
  exact RHTable.length_le_size_of_nodup_present t' hExt' _ (toList_keys_nodup t hExt)
    (fun k hk => h k ((mem_toList_keys_iff t hExt k).mp hk))

/-- WS-UC UC2: **two tables holding the same keys have the same size** — what
keeps a fuel or a capacity reading of `size` fixed across an in-place rewrite. -/
theorem size_eq_of_present_iff [BEq κ] [Hashable κ] [LawfulBEq κ]
    (t t' : RHTable κ ν) (hExt : t.invExt) (hExt' : t'.invExt)
    (h : ∀ k, t.get? k ≠ none ↔ t'.get? k ≠ none) : t.size = t'.size :=
  Nat.le_antisymm (size_le_size_of_present t t' hExt hExt' fun k => (h k).mp)
    (size_le_size_of_present t' t hExt' hExt fun k => (h k).mpr)

/-- WS-UC UC2: whatever a collecting walk collects, some entry yielded — read
off the slots alone, with no invariant. -/
theorem exists_of_mem_fold_elim_cons [BEq κ] [Hashable κ] [LawfulBEq κ] {β : Type}
    (rt : RHTable κ ν) (g : κ → ν → Option β) (x : β)
    (h : x ∈ rt.fold [] (fun acc k v => (g k v).elim acc (· :: acc))) :
    ∃ k v, g k v = some x := by
  rw [fold_eq_toList_reverse_foldl, mem_foldl_elim_cons (fun p : κ × ν => g p.1 p.2) x] at h
  rcases h with h | ⟨⟨k, v⟩, -, hg⟩
  · cases h
  · exact ⟨k, v, hg⟩

/-- WS-UC UC2: a collecting walk that no entry yields to collects nothing. -/
theorem fold_elim_cons_eq_nil [BEq κ] [Hashable κ] [LawfulBEq κ] {β : Type}
    (rt : RHTable κ ν) (g : κ → ν → Option β) (h : ∀ k v, g k v = none) :
    rt.fold [] (fun acc k v => (g k v).elim acc (· :: acc)) = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    obtain ⟨k, v, hg⟩ := exists_of_mem_fold_elim_cons rt g x hx
    rw [h k v] at hg; cases hg

end SeLe4n.Model
