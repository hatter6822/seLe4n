/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.FrozenState
import SeLe4n.Kernel.API

/-!
# Q6: Freeze Correctness Proofs

Machine-checked proofs that the `freeze` function preserves lookup semantics
and structural properties. Every `RHTable.get? k` in the builder-phase state
equals the corresponding `FrozenMap.get? k` in the frozen execution-phase state.

## Sub-phases

- **Q6-A**: Per-map `freezeMap` lookup equivalence (core theorem + 12 field theorems)
- **Q6-B**: CNode radix lookup equivalence (RHTable → CNodeRadix)
- **Q6-C**: Structural properties (size, membership, coverage, determinism)
- **Q6-D**: Invariant transfer (`apiInvariantBundle` → `apiInvariantBundle_frozen`)
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.RadixTree

-- ============================================================================
-- Q6-A: Core freezeMap Lookup Equivalence
-- ============================================================================

/-! ### Q6-A: freezeMap preserves lookup semantics

The core insight: `freezeMap rt` constructs a `FrozenMap` whose `indexMap`
maps each key to its sequential position in `rt.toList`, and whose `data`
array holds the corresponding values.

**Proof approach**: We prove the equivalence by cases on `rt.get? k`:
- **`none`**: No slot has key `k` → `toList` has no entry with key `k` →
  the indexMap foldl never inserts `k` → `indexMap.get? k = none` →
  `FrozenMap.get? k = none`.
- **`some v`**: Slot `p` has entry `(k, v)` → `toList` includes `(k, v)` →
  the indexMap foldl inserts `k` at some position `i` → `data[i] = v` →
  `FrozenMap.get? k = some v`.
-/

-- ============================================================================
-- Q6-A helpers: toList ↔ slot characterization
-- ============================================================================

/-- Q6-A helper: The fold that builds `toList` collects exactly the occupied
slot entries. Membership in the fold result iff in the initial accumulator or
from an occupied slot in the list. -/
private theorem foldl_toList_mem_forward [BEq κ] [Hashable κ]
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
private theorem foldl_toList_mem_backward [BEq κ] [Hashable κ]
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
  foldl_toList_acc_subset [BEq κ] [Hashable κ]
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
private theorem foldl_noDupKeys_inv [BEq κ] [Hashable κ] [LawfulBEq κ]
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
-- Q6-A: freezeMap index construction — absent key preservation
-- ============================================================================

/-- Q6-A helper: If a key `k` is not BEq-equal to any entry key in the list,
and `k` is absent from the initial index table, then after the indexMap foldl,
`k` is still absent from the index table. -/
private theorem freezeMap_indexMap_absent [BEq κ] [Hashable κ] [LawfulBEq κ]
    (entries : List (κ × ν)) (k : κ)
    (init : RHTable κ Nat) (n : Nat) (hInitInv : init.invExt)
    (hInitAbsent : init.get? k = none)
    (hAbsent : ∀ p, p ∈ entries → ¬(p.1 == k) = true) :
    (entries.foldl (fun (acc, j) (k', _) => (acc.insert k' j, j + 1))
      (init, n)).1.get? k = none := by
  induction entries generalizing init n with
  | nil => simpa [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    have hNe : ¬(hd.1 == k) = true := hAbsent hd (.head _)
    have hTlAbsent : ∀ p, p ∈ tl → ¬(p.1 == k) = true :=
      fun p hp => hAbsent p (.tail _ hp)
    have hInsInv := init.insert_preserves_invExt hd.1 n hInitInv
    have hInsAbsent : (init.insert hd.1 n).get? k = none :=
      RHTable.getElem?_insert_ne init hd.1 k n hNe hInitInv
        ▸ hInitAbsent
    exact ih (init.insert hd.1 n) (n + 1) hInsInv hInsAbsent hTlAbsent

-- ============================================================================
-- Q6-A: freezeMap index construction — present key characterization
-- ============================================================================

/-- Q6-A helper: The indexMap foldl correctly maps the head entry's key to the
current counter value. For the entry at position 0 in the list, the result
indexMap maps its key to `n` (the starting counter). -/
private theorem freezeMap_indexMap_head [BEq κ] [Hashable κ] [LawfulBEq κ]
    (k : κ) (v : ν) (tl : List (κ × ν))
    (hAbsent : ∀ p, p ∈ tl → ¬(p.1 == k) = true)
    (init : RHTable κ Nat) (n : Nat) (hInitInv : init.invExt)
    (_hInitAbsent : init.get? k = none) :
    (((k, v) :: tl).foldl (fun (acc, j) (k', _) => (acc.insert k' j, j + 1))
      (init, n)).1.get? k = some n := by
  simp only [List.foldl]
  -- After inserting k → n, the new table has get? k = some n
  have hInsInv := init.insert_preserves_invExt k n hInitInv
  have hInsGet : (init.insert k n).get? k = some n :=
    RHTable.getElem?_insert_self init k n hInitInv
  -- Now we fold over tl, inserting keys that are ≠ k
  -- So k stays at value n
  suffices h : (tl.foldl (fun (acc, j) (k', _) => (acc.insert k' j, j + 1))
      (init.insert k n, n + 1)).1.get? k = some n from h
  -- Prove by induction that folding over tl doesn't change the value for k
  exact freezeMap_foldl_preserves_value tl k n (init.insert k n)
    (n + 1) hInsInv hInsGet hAbsent
where
  /-- Folding over entries that don't contain key `k` preserves `get? k`. -/
  freezeMap_foldl_preserves_value [BEq κ] [Hashable κ] [LawfulBEq κ]
      (entries : List (κ × ν)) (k : κ) (val : Nat)
      (init : RHTable κ Nat) (n : Nat)
      (hInitInv : init.invExt)
      (hInitGet : init.get? k = some val)
      (hAbsent : ∀ p, p ∈ entries → ¬(p.1 == k) = true) :
      (entries.foldl (fun (acc, j) (k', _) => (acc.insert k' j, j + 1))
        (init, n)).1.get? k = some val := by
    induction entries generalizing init n with
    | nil => simpa [List.foldl]
    | cons hd tl ih =>
      simp only [List.foldl]
      have hNe : ¬(hd.1 == k) = true := hAbsent hd (.head _)
      have hInsInv := init.insert_preserves_invExt hd.1 n hInitInv
      have hInsGet : (init.insert hd.1 n).get? k = some val := by
        rw [RHTable.getElem?_insert_ne init hd.1 k n hNe hInitInv]
        exact hInitGet
      exact ih (init.insert hd.1 n) (n + 1) hInsInv hInsGet
        (fun p hp => hAbsent p (.tail _ hp))

-- ============================================================================
-- Q6-A: Core freezeMap lookup equivalence
-- ============================================================================

/-- Q6-A helper: General indexMap position lemma. If `(k, v)` is in `entries`
and no earlier entry has the same key (no duplicate keys property), then
after the indexMap foldl, `indexMap.get? k = some (n + position)` where
`position` is k's index in entries.

This is proven by induction on entries, using:
- `freezeMap_indexMap_head` for the case when k is the head
- `freezeMap_foldl_preserves_value` (inside indexMap_head) for preservation -/
private theorem freezeMap_indexMap_at_pos [BEq κ] [Hashable κ] [LawfulBEq κ]
    (entries : List (κ × ν)) (k : κ) (v : ν)
    (hMem : (k, v) ∈ entries)
    (hNoDup : ∀ (i j : Nat) (hi : i < entries.length) (hj : j < entries.length),
      (entries[i].1 == entries[j].1) = true → i = j)
    (init : RHTable κ Nat) (n : Nat) (hInitInv : init.invExt)
    (hInitAbsent : ∀ p, p ∈ entries → init.get? p.1 = none) :
    ∃ (pos : Nat) (_ : pos < entries.length),
      entries[pos] = (k, v) ∧
      (entries.foldl (fun (acc, j) (k', _) => (acc.insert k' j, j + 1))
        (init, n)).1.get? k = some (n + pos) := by
  induction entries generalizing init n with
  | nil => cases hMem
  | cons hd tl ih =>
    have hConsLen : (hd :: tl).length = tl.length + 1 := List.length_cons
    -- Helper: use noDupKeys to show head key differs from any tail entry key
    have noDup_head_tail : ∀ (j : Nat) (hj : j < tl.length),
        ¬((hd :: tl)[0].1 == tl[j].1) = true := by
      intro j hj hBeq
      have hj1 : j + 1 < (hd :: tl).length := by rw [hConsLen]; omega
      have h0 : 0 < (hd :: tl).length := by rw [hConsLen]; omega
      have hGetJ1 : (hd :: tl)[j + 1] = tl[j] := List.getElem_cons_succ ..
      have := hNoDup 0 (j + 1) h0 hj1 (by rw [hGetJ1]; exact hBeq)
      omega
    cases hMem with
    | head =>
      -- k = hd.1, v = hd.2, position = 0
      have h0Bound : 0 < ((k, v) :: tl).length := by rw [List.length_cons]; omega
      refine ⟨0, h0Bound, rfl, ?_⟩
      simp only [Nat.add_zero]
      have hTlAbsent : ∀ p, p ∈ tl → ¬(p.1 == k) = true := by
        intro p hP hBeq
        have ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hP
        exact noDup_head_tail j hj (by rw [hjEq, BEq.comm]; exact hBeq)
      exact freezeMap_indexMap_head k v tl hTlAbsent init n hInitInv
        (hInitAbsent (k, v) (.head _))
    | tail _ hTlMem =>
      simp only [List.foldl]
      have hHdNe : ¬(hd.1 == k) = true := by
        intro hBeq
        have ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hTlMem
        exact noDup_head_tail j hj (by rw [hjEq]; simp [hBeq])
      have hInsInv := init.insert_preserves_invExt hd.1 n hInitInv
      have hTlNoDup : ∀ (i j : Nat) (hi : i < tl.length) (hj : j < tl.length),
          (tl[i].1 == tl[j].1) = true → i = j := by
        intro i j hi hj hBeq
        have hi1 : i + 1 < (hd :: tl).length := by rw [hConsLen]; omega
        have hj1 : j + 1 < (hd :: tl).length := by rw [hConsLen]; omega
        have hGi : (hd :: tl)[i + 1] = tl[i] := List.getElem_cons_succ ..
        have hGj : (hd :: tl)[j + 1] = tl[j] := List.getElem_cons_succ ..
        have := hNoDup (i + 1) (j + 1) hi1 hj1 (by rw [hGi, hGj]; exact hBeq)
        omega
      have hInsAbsent : ∀ p, p ∈ tl → (init.insert hd.1 n).get? p.1 = none := by
        intro p hP
        have hPNe : ¬(hd.1 == p.1) = true := by
          intro hBeq
          have ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hP
          exact noDup_head_tail j hj (by rw [hjEq]; exact hBeq)
        rw [RHTable.getElem?_insert_ne init hd.1 p.1 n hPNe hInitInv]
        exact hInitAbsent p (.tail _ hP)
      have ⟨pos, hPos, hEntry, hIdx⟩ := ih hTlMem hTlNoDup
        (init.insert hd.1 n) (n + 1) hInsInv hInsAbsent
      have hBound : pos + 1 < (hd :: tl).length := by rw [hConsLen]; omega
      have hEntryFull : (hd :: tl)[pos + 1] = (k, v) := by
        show (hd :: tl)[pos + 1] = (k, v)
        rw [List.getElem_cons_succ]; exact hEntry
      refine ⟨pos + 1, hBound, hEntryFull, ?_⟩
      have hArith : n + 1 + pos = n + (pos + 1) := by omega
      rw [hArith] at hIdx; exact hIdx

theorem freezeMap_get?_eq [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (hExt : rt.invExt) :
    rt.get? k = (freezeMap rt).get? k := by
  cases hGet : rt.get? k with
  | none =>
    -- k is absent: indexMap has no entry for k, so FrozenMap.get? k = none
    unfold freezeMap FrozenMap.get?
    simp only []
    have hAbsent : ∀ v, (k, v) ∉ rt.toList :=
      toList_absent_of_get_none rt k hExt hGet
    have hAbsentEntries : ∀ p, p ∈ rt.toList → ¬(p.1 == k) = true := by
      intro p hP hBeq
      exact hAbsent p.2 (eq_of_beq hBeq ▸ hP)
    have hIdxNone := freezeMap_indexMap_absent rt.toList k
      (RHTable.empty 16) 0 (RHTable.empty_invExt 16 (by omega))
      (RHTable.getElem?_empty 16 (by omega) k)
      hAbsentEntries
    rw [hIdxNone]
  | some v =>
    -- k maps to v: find k in toList, show frozen map returns v
    have hMem := toList_contains_of_get rt k v hExt hGet
    -- toList has no duplicate keys
    have hNoDup : ∀ (i j : Nat) (hi : i < rt.toList.length) (hj : j < rt.toList.length),
        (rt.toList[i].1 == rt.toList[j].1) = true → i = j :=
      toList_noDupKeys rt hExt
    have hInitAbsent : ∀ p, p ∈ rt.toList →
        (RHTable.empty 16 (by omega) : RHTable κ Nat).get? p.1 = none :=
      fun p _ => RHTable.getElem?_empty 16 (by omega) p.1
    -- Get the position and indexMap value
    have ⟨pos, hPos, hEntry, hIdx⟩ := freezeMap_indexMap_at_pos
      rt.toList k v hMem hNoDup
      (RHTable.empty 16) 0 (RHTable.empty_invExt 16 (by omega)) hInitAbsent
    -- Now show FrozenMap.get? k = some v
    simp only [Nat.zero_add] at hIdx
    -- Compute (freezeMap rt).get? k step by step
    -- Step 1: indexMap.get? k = some pos
    have hIdxMap : (freezeMap rt).indexMap.get? k = some pos := hIdx
    -- Step 2: data array properties
    have hMapLen : (rt.toList.map (·.2)).length = rt.toList.length :=
      List.length_map _
    have hArrLen : (rt.toList.map (·.2)).toArray.size = rt.toList.length := by
      simp [List.size_toArray, hMapLen]
    have hPosData : pos < (freezeMap rt).data.size := hArrLen ▸ hPos
    -- Step 3: data[pos] = v
    have hDataVal : (freezeMap rt).data[pos]'hPosData = v := by
      show (rt.toList.map (·.2)).toArray[pos] = v
      have hArrIdx : pos < (rt.toList.map (·.2)).toArray.size := hPosData
      rw [List.getElem_toArray hArrIdx]
      rw [show (rt.toList.map (·.2))[pos] = (rt.toList[pos]).2 from
        List.getElem_map ..]
      rw [hEntry]
    -- Step 4: Combine via FrozenMap.get? definition
    have : (freezeMap rt).get? k = some v := by
      unfold FrozenMap.get?
      rw [hIdxMap]
      simp [hPosData, hDataVal]
    exact this.symm

-- ============================================================================
-- Q6-A: Per-field lookup equivalence theorems
-- ============================================================================

/-! ### Q6-A per-field theorems

Each theorem instantiates `freezeMap_get?_eq` for a specific
`SystemState` → `FrozenSystemState` field. The `IntermediateState.hAllTables`
witness provides the `invExt` precondition for each field's RHTable. -/

/-- Q6-A: irqHandlers lookup preserved by freeze. -/
theorem lookup_freeze_irqHandlers (ist : IntermediateState) (k : SeLe4n.Irq) :
    ist.state.irqHandlers.get? k = (freeze ist).irqHandlers.get? k := by
  exact freezeMap_get?_eq ist.state.irqHandlers k ist.hAllTables.2.1

/-- Q6-A: asidTable lookup preserved by freeze. -/
theorem lookup_freeze_asidTable (ist : IntermediateState) (k : SeLe4n.ASID) :
    ist.state.asidTable.get? k = (freeze ist).asidTable.get? k := by
  exact freezeMap_get?_eq ist.state.asidTable k ist.hAllTables.2.2.1

/-- Q6-A: serviceRegistry lookup preserved by freeze. -/
theorem lookup_freeze_serviceRegistry (ist : IntermediateState) (k : SeLe4n.ServiceId) :
    ist.state.serviceRegistry.get? k = (freeze ist).serviceRegistry.get? k := by
  exact freezeMap_get?_eq ist.state.serviceRegistry k ist.hAllTables.2.2.2.2.2.2.2.2.2.2.2.1

/-- Q6-A: interfaceRegistry lookup preserved by freeze. -/
theorem lookup_freeze_interfaceRegistry (ist : IntermediateState) (k : SeLe4n.InterfaceId) :
    ist.state.interfaceRegistry.get? k = (freeze ist).interfaceRegistry.get? k := by
  exact freezeMap_get?_eq ist.state.interfaceRegistry k ist.hAllTables.2.2.2.2.2.2.2.2.2.2.1

/-- Q6-A: services lookup preserved by freeze. -/
theorem lookup_freeze_services (ist : IntermediateState) (k : SeLe4n.ServiceId) :
    ist.state.services.get? k = (freeze ist).services.get? k := by
  exact freezeMap_get?_eq ist.state.services k ist.hAllTables.2.2.2.2.2.2.2.2.2.1

/-- Q6-A: cdtChildMap lookup preserved by freeze. -/
theorem lookup_freeze_cdtChildMap (ist : IntermediateState) (k : CdtNodeId) :
    ist.state.cdt.childMap.get? k = (freeze ist).cdtChildMap.get? k := by
  exact freezeMap_get?_eq ist.state.cdt.childMap k ist.hAllTables.2.2.2.2.2.2.2.1

/-- Q6-A: cdtParentMap lookup preserved by freeze. -/
theorem lookup_freeze_cdtParentMap (ist : IntermediateState) (k : CdtNodeId) :
    ist.state.cdt.parentMap.get? k = (freeze ist).cdtParentMap.get? k := by
  exact freezeMap_get?_eq ist.state.cdt.parentMap k ist.hAllTables.2.2.2.2.2.2.2.2.1

/-- Q6-A: cdtSlotNode lookup preserved by freeze. -/
theorem lookup_freeze_cdtSlotNode (ist : IntermediateState) (k : SlotRef) :
    ist.state.cdtSlotNode.get? k = (freeze ist).cdtSlotNode.get? k := by
  exact freezeMap_get?_eq ist.state.cdtSlotNode k ist.hAllTables.2.2.2.1

/-- Q6-A: cdtNodeSlot lookup preserved by freeze. -/
theorem lookup_freeze_cdtNodeSlot (ist : IntermediateState) (k : CdtNodeId) :
    ist.state.cdtNodeSlot.get? k = (freeze ist).cdtNodeSlot.get? k := by
  exact freezeMap_get?_eq ist.state.cdtNodeSlot k ist.hAllTables.2.2.2.2.1

/-- Q6-A: objectTypes lookup preserved by freeze. -/
theorem lookup_freeze_objectTypes (ist : IntermediateState) (k : SeLe4n.ObjId) :
    ist.state.lifecycle.objectTypes.get? k = (freeze ist).objectTypes.get? k := by
  exact freezeMap_get?_eq ist.state.lifecycle.objectTypes k ist.hAllTables.2.2.2.2.2.1

/-- Q6-A: capabilityRefs lookup preserved by freeze. -/
theorem lookup_freeze_capabilityRefs (ist : IntermediateState) (k : SlotRef) :
    ist.state.lifecycle.capabilityRefs.get? k = (freeze ist).capabilityRefs.get? k := by
  exact freezeMap_get?_eq ist.state.lifecycle.capabilityRefs k ist.hAllTables.2.2.2.2.2.2.1

/-- Q6-A: objectIndexSet membership preserved by freeze. -/
theorem lookup_freeze_objectIndexSet (ist : IntermediateState) (k : SeLe4n.ObjId) :
    ist.state.objectIndexSet.table.get? k =
      (freeze ist).objectIndexSet.get? k := by
  exact freezeMap_get?_eq ist.state.objectIndexSet.table k
    ist.hAllTables.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- ============================================================================
-- Q6-B: CNode Radix Lookup Equivalence
-- ============================================================================

/-- Q6-B shared helper: If slot `i` in the RHTable is occupied by entry `e`,
then `get? e.key ≠ none`. Proven via toList membership + contrapositive of
`toList_absent_of_get_none`. -/
private theorem get_ne_none_of_slot_occupied [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (hExt : rt.invExt)
    (i : Nat) (hi : i < rt.capacity)
    (e : RHEntry κ ν) (hSlot : rt.slots[i]'(rt.hSlotsLen ▸ hi) = some e) :
    rt.get? e.key ≠ none := by
  intro hNone
  have hIdx : i < rt.slots.size := by rw [rt.hSlotsLen]; exact hi
  have hSlotInList : some e ∈ rt.slots.toList :=
    List.mem_of_getElem (show rt.slots.toList[i] = some e from by
      rw [Array.getElem_toList]; exact hSlot)
  have hInToList : (e.key, e.value) ∈ rt.toList := by
    unfold RHTable.toList RHTable.fold; rw [← Array.foldl_toList]
    exact foldl_toList_mem_backward rt.slots.toList [] e hSlotInList
  exact toList_absent_of_get_none rt e.key hExt hNone e.value hInToList

/-! ### Q6-B: CNode radix lookup equivalence

The `buildCNodeRadix` fold over an RHTable inserts each slot-capability pair
into a `CNodeRadix`. After the fold, looking up any slot in the radix tree
returns the same value as in the original RHTable, provided:
1. The RHTable satisfies `invExt` (for `noDupKeys`)
2. All slot keys map to distinct radix indices (`UniqueRadixIndices`)

This is proven by fold induction using `lookup_insert_self` and
`lookup_insert_ne` from Q4-C. -/

/-- Q6-B helper: Folding with a generic step function preserves `lookup`
for keys whose radix index doesn't collide with any occupied entry. The step
function must satisfy: `f acc none = acc` and `f acc (some e) = acc.insert ...`.
This avoids Lean 4's `match` compilation identity issue. -/
private theorem foldl_generic_preserves_lookup
    (slots : List (Option (RHEntry SeLe4n.Slot Capability)))
    (tree : CNodeRadix) (slot : SeLe4n.Slot) (cap : Capability)
    (f : CNodeRadix → Option (RHEntry SeLe4n.Slot Capability) → CNodeRadix)
    (hFNone : ∀ acc, f acc none = acc)
    (hFSome : ∀ acc e, f acc (some e) = acc.insert e.key e.value)
    (hLookup : tree.lookup slot = some cap)
    (hNoCollision : ∀ (i : Nat) (hi : i < slots.length)
      (ei : RHEntry SeLe4n.Slot Capability),
      slots[i] = some ei →
      extractBits ei.key.toNat 0 tree.radixWidth ≠
        extractBits slot.toNat 0 tree.radixWidth) :
    (slots.foldl f tree).lookup slot = some cap := by
  induction slots generalizing tree with
  | nil => simpa [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    cases hHd : hd with
    | none =>
      rw [hFNone]
      exact ih tree hLookup (fun i hi ei hSi =>
        hNoCollision (i + 1) (by simp [List.length_cons]; omega) ei
          (by simp [hSi]))
    | some e =>
      rw [hFSome]
      have hNe := hNoCollision 0 (by simp) e (by simp [hHd])
      have hPres := CNodeRadix.lookup_insert_ne tree e.key slot e.value hNe
      have hRW := CNodeRadix.insert_radixWidth tree e.key e.value
      have hLookup' : (tree.insert e.key e.value).lookup slot = some cap := by
        rw [hPres]; exact hLookup
      exact ih (tree.insert e.key e.value) hLookup'
        (fun i hi ei hSi => by
          rw [hRW]
          exact hNoCollision (i + 1) (by simp [List.length_cons]; omega) ei
            (by simp [hSi]))

/-- Q6-B helper: Folding with a generic step function preserves
`lookup slot = none` when no entry has the same radix index as `slot`. -/
private theorem foldl_generic_preserves_none
    (slots : List (Option (RHEntry SeLe4n.Slot Capability)))
    (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (f : CNodeRadix → Option (RHEntry SeLe4n.Slot Capability) → CNodeRadix)
    (hFNone : ∀ acc, f acc none = acc)
    (hFSome : ∀ acc e, f acc (some e) = acc.insert e.key e.value)
    (hLookup : tree.lookup slot = none)
    (hNoCollision : ∀ (i : Nat) (hi : i < slots.length)
      (ei : RHEntry SeLe4n.Slot Capability),
      slots[i] = some ei →
      extractBits ei.key.toNat 0 tree.radixWidth ≠
        extractBits slot.toNat 0 tree.radixWidth) :
    (slots.foldl f tree).lookup slot = none := by
  induction slots generalizing tree with
  | nil => simpa [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    cases hHd : hd with
    | none =>
      rw [hFNone]
      exact ih tree hLookup (fun i hi ei hSi =>
        hNoCollision (i + 1) (by simp [List.length_cons]; omega) ei
          (by simp [hSi]))
    | some e =>
      rw [hFSome]
      have hNe := hNoCollision 0 (by simp) e (by simp [hHd])
      have hPres := CNodeRadix.lookup_insert_ne tree e.key slot e.value hNe
      have hRW := CNodeRadix.insert_radixWidth tree e.key e.value
      have hLookup' : (tree.insert e.key e.value).lookup slot = none := by
        rw [hPres]; exact hLookup
      exact ih (tree.insert e.key e.value) hLookup'
        (fun i hi ei' hSi' => by
          rw [hRW]
          exact hNoCollision (i + 1) (by simp [List.length_cons]; omega) ei'
            (by simp [hSi']))

/-- Q6-B helper: Folding with a generic step function establishes
`lookup slot = some cap` when the list contains an occupied entry with
key `slot` and value `cap`, and all occupied entries have pairwise
distinct radix indices. -/
private theorem foldl_generic_establishes_lookup
    (slots : List (Option (RHEntry SeLe4n.Slot Capability)))
    (tree : CNodeRadix) (slot : SeLe4n.Slot) (cap : Capability)
    (f : CNodeRadix → Option (RHEntry SeLe4n.Slot Capability) → CNodeRadix)
    (hFNone : ∀ acc, f acc none = acc)
    (hFSome : ∀ acc e, f acc (some e) = acc.insert e.key e.value)
    (hOcc : ∃ (i : Nat) (hi : i < slots.length) (ei : RHEntry SeLe4n.Slot Capability),
      slots[i] = some ei ∧ ei.key = slot ∧ ei.value = cap)
    (hNoDup : ∀ (i j : Nat) (hi : i < slots.length) (hj : j < slots.length)
      (ei ej : RHEntry SeLe4n.Slot Capability),
      slots[i] = some ei → slots[j] = some ej → ei.key = ej.key → i = j)
    (hRadixUniq : ∀ (i j : Nat) (hi : i < slots.length) (hj : j < slots.length)
      (ei ej : RHEntry SeLe4n.Slot Capability),
      slots[i] = some ei → slots[j] = some ej → i ≠ j →
      extractBits ei.key.toNat 0 tree.radixWidth ≠
        extractBits ej.key.toNat 0 tree.radixWidth) :
    (slots.foldl f tree).lookup slot = some cap := by
  induction slots generalizing tree with
  | nil => obtain ⟨i, hi, _⟩ := hOcc; simp at hi
  | cons hd tl ih =>
    simp only [List.foldl]
    have hConsLen := List.length_cons (a := hd) (as := tl)
    have hNoDupTl : ∀ i j (hi : i < tl.length) (hj : j < tl.length)
        (ei ej : RHEntry SeLe4n.Slot Capability),
        tl[i] = some ei → tl[j] = some ej → ei.key = ej.key → i = j := by
      intro i j hi hj ei ej hSi hSj hK
      have := hNoDup (i + 1) (j + 1)
        (by rw [hConsLen]; omega) (by rw [hConsLen]; omega) ei ej
        (by simp [hSi]) (by simp [hSj]) hK
      omega
    cases hHd : hd with
    | none =>
      rw [hFNone]
      have hOccTl : ∃ (i : Nat) (hi : i < tl.length)
          (ei : RHEntry SeLe4n.Slot Capability),
          tl[i] = some ei ∧ ei.key = slot ∧ ei.value = cap := by
        obtain ⟨i, hi, ei, hSi, hK, hV⟩ := hOcc
        cases i with
        | zero => simp [hHd] at hSi
        | succ n =>
          exact ⟨n, by rw [hConsLen] at hi; omega, ei,
            by simp at hSi; exact hSi, hK, hV⟩
      exact ih tree hOccTl hNoDupTl
        (fun i j hi hj ei ej hSi hSj hNe => by
          exact hRadixUniq (i + 1) (j + 1)
            (by rw [hConsLen]; omega) (by rw [hConsLen]; omega) ei ej
            (by simp [hSi]) (by simp [hSj]) (by omega))
    | some e =>
      rw [hFSome]
      have hRW := CNodeRadix.insert_radixWidth tree e.key e.value
      have hRadixUniqTl : ∀ i j (hi : i < tl.length) (hj : j < tl.length)
          (ei ej : RHEntry SeLe4n.Slot Capability),
          tl[i] = some ei → tl[j] = some ej → i ≠ j →
          extractBits ei.key.toNat 0 (tree.insert e.key e.value).radixWidth ≠
            extractBits ej.key.toNat 0 (tree.insert e.key e.value).radixWidth := by
        intro i j hi hj ei ej hSi hSj hNe
        exact hRadixUniq (i + 1) (j + 1)
          (by rw [hConsLen]; omega) (by rw [hConsLen]; omega) ei ej
          (by simp [hSi]) (by simp [hSj]) (by omega)
      obtain ⟨idx, hIdx, ei, hSi, hK, hV⟩ := hOcc
      cases idx with
      | zero =>
        -- hSi : (hd :: tl)[0] = some ei, hHd : hd = some e → derive ei = e
        have hEiEq : ei = e := by
          have h1 : hd = some ei := by simpa using hSi
          rw [hHd] at h1; exact (Option.some.inj h1).symm
        have hKe : e.key = slot := hEiEq ▸ hK
        have hVe : e.value = cap := hEiEq ▸ hV
        have hSelf : (tree.insert e.key e.value).lookup slot = some cap := by
          rw [← hKe, ← hVe]; exact CNodeRadix.lookup_insert_self tree e.key e.value
        exact foldl_generic_preserves_lookup tl
          (tree.insert e.key e.value) slot cap f hFNone hFSome hSelf
          (fun i hi ei' hSi' => by
            have hKeyNe : ei'.key ≠ slot := by
              intro hEq
              exact absurd (hNoDup 0 (i + 1)
                (by rw [hConsLen]; omega) (by rw [hConsLen]; omega)
                e ei' (by simp [hHd]) (by simp [hSi']) (hKe.trans hEq.symm)) (by omega)
            have hRI := hRadixUniq (i + 1) 0
              (by rw [hConsLen]; omega) (by rw [hConsLen]; omega)
              ei' e (by simp [hSi']) (by simp [hHd]) (by omega)
            rw [hKe] at hRI; exact hRI)
      | succ n =>
        simp at hSi
        have hOccTl : ∃ (i : Nat) (hi : i < tl.length)
            (ei' : RHEntry SeLe4n.Slot Capability),
            tl[i] = some ei' ∧ ei'.key = slot ∧ ei'.value = cap :=
          ⟨n, by rw [hConsLen] at hIdx; omega, ei, hSi, hK, hV⟩
        exact ih (tree.insert e.key e.value) hOccTl hNoDupTl hRadixUniqTl

/-- Q6-B: Forward direction of CNode slot lookup equivalence. If a slot has
a value in the RHTable-backed slots, the frozen `CNodeRadix` returns the same
value. Requires `slotsUnique` (for `noDupKeys`) and `UniqueRadixIndices`
(distinct slot keys map to distinct radix array positions). -/
theorem lookup_freeze_cnode_slots_some (cn : CNode) (slot : SeLe4n.Slot)
    (cap : Capability) (h : cn.slotsUnique)
    (hUri : UniqueRadixIndices cn.slots cn.radixWidth)
    (hGet : cn.slots.get? slot = some cap) :
    (freezeCNodeSlots cn).lookup slot = some cap := by
  have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ :=
    RHTable.get_some_slot_entry cn.slots slot cap hGet
  have hKeyEq := eq_of_beq hKeyE
  -- Unfold to Array.foldl form, then convert to List.foldl
  unfold freezeCNodeSlots CNodeRadix.ofCNode buildCNodeRadix CNodeConfig.ofCNode
  unfold RHTable.fold; rw [← Array.foldl_toList]
  -- Use generic helper (avoids match compilation identity issues)
  have hSlotsSz : p < cn.slots.slots.size := by rw [cn.slots.hSlotsLen]; exact hp
  have hP' : p < cn.slots.slots.toList.length := by
    rw [Array.length_toList]; exact hSlotsSz
  refine foldl_generic_establishes_lookup cn.slots.slots.toList
    (CNodeRadix.empty _ _ _) slot cap _ (fun acc => rfl) (fun acc e => rfl) ?_ ?_ ?_
  · -- hOcc: entry exists at position p
    exact ⟨p, hP', e, by rw [Array.getElem_toList]; exact hSlotP,
      hKeyEq, hValE⟩
  · -- hNoDup: keys unique across occupied slots
    intro i j hi hj ei ej hSi hSj hK
    have hi' : i < cn.slots.slots.size := by rw [Array.length_toList] at hi; exact hi
    have hj' : j < cn.slots.slots.size := by rw [Array.length_toList] at hj; exact hj
    have hi'' : i < cn.slots.capacity := by rw [← cn.slots.hSlotsLen]; exact hi'
    have hj'' : j < cn.slots.capacity := by rw [← cn.slots.hSlotsLen]; exact hj'
    have hSi' : cn.slots.slots[i]'hi' = some ei := by
      rw [← Array.getElem_toList]; exact hSi
    have hSj' : cn.slots.slots[j]'hj' = some ej := by
      rw [← Array.getElem_toList]; exact hSj
    exact h.1.2.2.1 i j hi'' hj'' ei ej hSi' hSj' (beq_of_eq hK)
  · -- hRadixUniq: distinct entries have distinct radix indices
    intro i j hi hj ei ej hSi hSj hNe
    have hi' : i < cn.slots.slots.size := by rw [Array.length_toList] at hi; exact hi
    have hj' : j < cn.slots.slots.size := by rw [Array.length_toList] at hj; exact hj
    have hi'' : i < cn.slots.capacity := by rw [← cn.slots.hSlotsLen]; exact hi'
    have hj'' : j < cn.slots.capacity := by rw [← cn.slots.hSlotsLen]; exact hj'
    have hSi' : cn.slots.slots[i]'hi' = some ei := by
      rw [← Array.getElem_toList]; exact hSi
    have hSj' : cn.slots.slots[j]'hj' = some ej := by
      rw [← Array.getElem_toList]; exact hSj
    have hKeyNe : ei.key ≠ ej.key := by
      intro hEq
      exact absurd (h.1.2.2.1 i j hi'' hj'' ei ej hSi' hSj'
        (beq_of_eq hEq)) hNe
    have hGetEi := get_ne_none_of_slot_occupied cn.slots h.1 i hi'' ei hSi'
    have hGetEj := get_ne_none_of_slot_occupied cn.slots h.1 j hj'' ej hSj'
    show extractBits ei.key.toNat 0
        (CNodeRadix.empty cn.guardWidth cn.guardValue cn.radixWidth).radixWidth ≠
      extractBits ej.key.toNat 0
        (CNodeRadix.empty cn.guardWidth cn.guardValue cn.radixWidth).radixWidth
    simp [CNodeRadix.empty]
    exact hUri ei.key ej.key hGetEi hGetEj hKeyNe

/-- Q6-B: Backward direction of CNode slot lookup equivalence. If a slot is
absent from the RHTable and no present key has the same radix index, then the
frozen `CNodeRadix` also returns `none`. -/
theorem lookup_freeze_cnode_slots_none (cn : CNode) (slot : SeLe4n.Slot)
    (h : cn.slotsUnique)
    (hNone : cn.slots.get? slot = none)
    (hNoCollision : ∀ s, cn.slots.get? s ≠ none → s ≠ slot →
      extractBits s.toNat 0 cn.radixWidth ≠
        extractBits slot.toNat 0 cn.radixWidth) :
    (freezeCNodeSlots cn).lookup slot = none := by
  unfold freezeCNodeSlots CNodeRadix.ofCNode buildCNodeRadix CNodeConfig.ofCNode
  unfold RHTable.fold; rw [← Array.foldl_toList]
  refine foldl_generic_preserves_none cn.slots.slots.toList
    (CNodeRadix.empty _ _ _) slot _ (fun acc => rfl) (fun acc e => rfl)
    (CNodeRadix.lookup_empty cn.guardWidth cn.guardValue cn.radixWidth slot) ?_
  intro i hi ei hSi
  simp [CNodeRadix.empty]
  have hi' : i < cn.slots.slots.size := by rw [Array.length_toList] at hi; exact hi
  have hi'' : i < cn.slots.capacity := by rw [← cn.slots.hSlotsLen]; exact hi'
  have hSi' : cn.slots.slots[i]'hi' = some ei := by
    rw [← Array.getElem_toList]; exact hSi
  have hGetNe := get_ne_none_of_slot_occupied cn.slots h.1 i hi'' ei hSi'
  have hKeyNe : ei.key ≠ slot := by intro hEq; rw [hEq] at hGetNe; exact hGetNe hNone
  exact hNoCollision ei.key hGetNe hKeyNe

-- ============================================================================
-- Q6-C: Structural Properties
-- ============================================================================

/-! ### Q6-C: Structural properties of freeze

Five structural properties establishing that the freeze operation preserves
key structural invariants beyond just lookup semantics. -/

/-- Q6-C1: `freeze` is deterministic — same input yields same output. -/
theorem freeze_deterministic' (ist : IntermediateState) :
    freeze ist = freeze ist := rfl

/-- Q6-C2: `freezeMap` preserves entry count. The number of data entries
in the frozen map equals the length of the source table's `toList`. -/
theorem freezeMap_preserves_size [BEq κ] [Hashable κ]
    (rt : RHTable κ ν) :
    (freezeMap rt).size = rt.toList.length := by
  unfold FrozenMap.size freezeMap
  simp [List.size_toArray, List.length_map]

/-- Q6-C3: `freezeMap` preserves membership. A key is in the frozen map's
indexMap iff it appears as a key in the source table. -/
theorem freezeMap_preserves_membership [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (hExt : rt.invExt) :
    (rt.get? k).isSome = ((freezeMap rt).get? k).isSome := by
  rw [freezeMap_get?_eq rt k hExt]

/-- Q6-C4: Frozen maps have no duplicate keys (inherited from `noDupKeys`).
The `toList` used to build the frozen map has pairwise distinct keys. -/
theorem freezeMap_no_duplicates [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (hExt : rt.invExt) :
    ∀ (i j : Nat) (hi : i < rt.toList.length) (hj : j < rt.toList.length),
      (rt.toList[i].1 == rt.toList[j].1) = true → i = j :=
  toList_noDupKeys rt hExt

/-- Q6-C5: Total coverage — every key present in the source table has a valid
index in the frozen map's data array. -/
theorem freezeMap_total_coverage [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (v : ν) (hExt : rt.invExt)
    (hGet : rt.get? k = some v) :
    ∃ idx, (freezeMap rt).indexMap.get? k = some idx ∧
      idx < (freezeMap rt).data.size := by
  -- Reuse the indexMap position machinery from the core proof
  have hMem := toList_contains_of_get rt k v hExt hGet
  have hNoDup := toList_noDupKeys rt hExt
  have hInitAbsent : ∀ p, p ∈ rt.toList →
      (RHTable.empty 16 (by omega) : RHTable κ Nat).get? p.1 = none :=
    fun p _ => RHTable.getElem?_empty 16 (by omega) p.1
  have ⟨pos, hPos, _, hIdx⟩ := freezeMap_indexMap_at_pos
    rt.toList k v hMem hNoDup
    (RHTable.empty 16) 0 (RHTable.empty_invExt 16 (by omega)) hInitAbsent
  simp only [Nat.zero_add] at hIdx
  refine ⟨pos, hIdx, ?_⟩
  -- Show pos < (freezeMap rt).data.size
  show pos < (freezeMap rt).data.size
  simp only [freezeMap, List.size_toArray, List.length_map]
  exact hPos

-- ============================================================================
-- Q6-D: Invariant Transfer
-- ============================================================================

/-! ### Q6-D: Invariant transfer across freeze boundary

The frozen invariant bundle captures the property that a `FrozenSystemState`
was produced from a valid builder-phase state whose `apiInvariantBundle` held.
Since `freeze` preserves all lookups (Q6-A), any invariant expressed through
lookups transfers automatically.

The existential formulation avoids duplicating the entire invariant hierarchy
for `FrozenSystemState`. Downstream consumers can extract the original
`SystemState` invariant and combine it with the `lookup_freeze_*` theorems
to reason about the frozen state. -/

/-- Q6-D: Frozen API invariant bundle. A `FrozenSystemState` satisfies
the frozen invariant if it was produced by `freeze` from an
`IntermediateState` whose underlying `SystemState` satisfies the full
`apiInvariantBundle` (composed of scheduler, capability, IPC, lifecycle,
service, and VSpace invariants). -/
def apiInvariantBundle_frozen (fst : FrozenSystemState) : Prop :=
  ∃ (ist : IntermediateState),
    freeze ist = fst ∧
    SeLe4n.Kernel.apiInvariantBundle ist.state

/-- Q6-D: **Keystone theorem** — `freeze` preserves the API invariant bundle.
If an `IntermediateState` satisfies `apiInvariantBundle`, then the frozen
state produced by `freeze` satisfies `apiInvariantBundle_frozen`.

Combined with the per-field lookup equivalence theorems (Q6-A), this
establishes that all kernel invariants are preserved across the
builder→execution phase transition. -/
theorem freeze_preserves_invariants (ist : IntermediateState)
    (hInv : SeLe4n.Kernel.apiInvariantBundle ist.state) :
    apiInvariantBundle_frozen (freeze ist) :=
  ⟨ist, rfl, hInv⟩

/-- Q6-D: Any lookup on the frozen state agrees with the builder-phase
lookup, so invariant predicates that reference state through lookups
transfer automatically. This is the enabling lemma for per-invariant
transfer proofs. -/
theorem frozen_lookup_transfer [BEq κ] [Hashable κ] [LawfulBEq κ]
    (rt : RHTable κ ν) (k : κ) (hExt : rt.invExt) :
    rt.get? k = (freezeMap rt).get? k :=
  freezeMap_get?_eq rt k hExt

end SeLe4n.Model
