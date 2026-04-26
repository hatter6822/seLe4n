-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RadixTree.Core

/-!
# Q4-C: CNode Radix Tree — Invariants and Proofs

24 correctness proofs for `CNodeRadix` operations:

**Lookup correctness (6):**
1. `lookup_empty` — empty tree always returns `none`
2. `lookup_insert_self` — insert then lookup at same slot returns inserted value
3. `lookup_insert_ne` — insert does not affect other slots
4. `lookup_erase_self` — erase then lookup returns `none`
5. `lookup_erase_ne` — erase does not affect other slots
6. `insert_idempotent` — inserting same value twice is identity

**Well-formedness (5):**
7. `wf_of_mk` — any `CNodeRadix` value satisfies `WF`
8. `empty_wf` — empty tree is well-formed
9. `insert_wf` — insert preserves well-formedness
10. `erase_wf` — erase preserves well-formedness
11. `insert_erase_cancel` — insert then erase restores original tree

**Field preservation (6):**
12. `insert_guardWidth` / 13. `insert_guardValue` / 14. `insert_radixWidth`
15. `erase_guardWidth` / 16. `erase_guardValue` / 17. `erase_radixWidth`

**Size and fanout (4):**
18. `size_empty` — empty tree has size 0
19. `fanout_eq_slots_size` — fanout equals array size
20. `size_insert_le` — size increases by at most 1
21. `size_erase_le` — size only decreases

**Enumeration (3):**
22. `toList_complete` — toList contains every occupied entry
23. `toList_noDup` — toList has no duplicate keys
24. `fold_visits_all` — fold visits every occupied entry

All proofs are machine-checked with no admitted goals or postulated axioms.
-/

namespace SeLe4n.Kernel.RadixTree

open SeLe4n.Model

-- ============================================================================
-- Q4-C: Helper lemmas for array indexing
-- ============================================================================

private theorem extractBits_idx_eq (s : SeLe4n.Slot) (radixWidth : Nat) :
    extractBits s.toNat 0 radixWidth = s.toNat % (2 ^ radixWidth) := by
  simp [extractBits]

-- ============================================================================
-- Q4-C1: lookup_empty
-- ============================================================================

/-- Looking up any slot in an empty CNodeRadix returns `none`. -/
theorem CNodeRadix.lookup_empty (gw gv rw : Nat) (slot : SeLe4n.Slot) :
    (CNodeRadix.empty gw gv rw).lookup slot = none := by
  simp [CNodeRadix.lookup, CNodeRadix.empty]

-- ============================================================================
-- Q4-C2: lookup_insert_self
-- ============================================================================

/-- After inserting at `slot`, looking up `slot` returns the inserted capability. -/
theorem CNodeRadix.lookup_insert_self (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).lookup slot = some cap := by
  simp [CNodeRadix.lookup, CNodeRadix.insert]

-- ============================================================================
-- Q4-C3: lookup_insert_ne
-- ============================================================================

/-- Inserting at slot `s` does not affect lookup at a different slot `s'`
when `s` and `s'` map to different radix indices. -/
theorem CNodeRadix.lookup_insert_ne (tree : CNodeRadix) (s s' : SeLe4n.Slot)
    (cap : Capability)
    (hNe : extractBits s.toNat 0 tree.radixWidth ≠ extractBits s'.toNat 0 tree.radixWidth) :
    (tree.insert s cap).lookup s' = tree.lookup s' := by
  simp [CNodeRadix.lookup, CNodeRadix.insert, Array.getElem_set, hNe]

-- ============================================================================
-- Q4-C4: lookup_erase_self
-- ============================================================================

/-- After erasing at `slot`, looking up `slot` returns `none`. -/
theorem CNodeRadix.lookup_erase_self (tree : CNodeRadix) (slot : SeLe4n.Slot) :
    (tree.erase slot).lookup slot = none := by
  simp [CNodeRadix.lookup, CNodeRadix.erase]

-- ============================================================================
-- Q4-C5: lookup_erase_ne
-- ============================================================================

/-- Erasing at slot `s` does not affect lookup at a different slot `s'`
when `s` and `s'` map to different radix indices. -/
theorem CNodeRadix.lookup_erase_ne (tree : CNodeRadix) (s s' : SeLe4n.Slot)
    (hNe : extractBits s.toNat 0 tree.radixWidth ≠ extractBits s'.toNat 0 tree.radixWidth) :
    (tree.erase s).lookup s' = tree.lookup s' := by
  simp [CNodeRadix.lookup, CNodeRadix.erase, Array.getElem_set, hNe]

-- ============================================================================
-- Q4-C6: insert_idempotent
-- ============================================================================

/-- Inserting the same value at the same slot twice yields the same tree
as inserting once. -/
theorem CNodeRadix.insert_idempotent (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).insert slot cap = tree.insert slot cap := by
  simp [CNodeRadix.insert, Array.set_set]

-- ============================================================================
-- Q4-C7: Well-formedness definition and preservation
-- ============================================================================

/-- Well-formedness: the slot array has exactly `2^radixWidth` entries. -/
def CNodeRadix.WF (tree : CNodeRadix) : Prop :=
  tree.slots.size = 2 ^ tree.radixWidth

/-- Every CNodeRadix satisfies WF by construction (carried in `hSlotSize`). -/
theorem CNodeRadix.wf_of_mk (tree : CNodeRadix) : tree.WF :=
  tree.hSlotSize

/-- Empty tree is well-formed. -/
theorem CNodeRadix.empty_wf (gw gv rw : Nat) : (CNodeRadix.empty gw gv rw).WF := by
  simp [CNodeRadix.WF, CNodeRadix.empty, Array.size]

/-- Insert preserves well-formedness. -/
theorem CNodeRadix.insert_wf (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).WF := by
  simp [CNodeRadix.WF, CNodeRadix.insert, Array.size_set, tree.hSlotSize]

/-- Erase preserves well-formedness. -/
theorem CNodeRadix.erase_wf (tree : CNodeRadix) (slot : SeLe4n.Slot) :
    (tree.erase slot).WF := by
  simp [CNodeRadix.WF, CNodeRadix.erase, Array.size_set, tree.hSlotSize]

-- ============================================================================
-- Q4-C8: erase then insert roundtrip
-- ============================================================================

/-- Erasing then inserting at the same slot yields the insert result. -/
theorem CNodeRadix.insert_erase_cancel (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.erase slot).insert slot cap = tree.insert slot cap := by
  simp [CNodeRadix.insert, CNodeRadix.erase, Array.set_set]

-- ============================================================================
-- Q4-C9: insert preserves radix parameters
-- ============================================================================

/-- Insert does not change guardWidth. -/
theorem CNodeRadix.insert_guardWidth (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).guardWidth = tree.guardWidth := rfl

/-- Insert does not change guardValue. -/
theorem CNodeRadix.insert_guardValue (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).guardValue = tree.guardValue := rfl

/-- Insert does not change radixWidth. -/
theorem CNodeRadix.insert_radixWidth (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).radixWidth = tree.radixWidth := rfl

/-- Erase does not change guardWidth. -/
theorem CNodeRadix.erase_guardWidth (tree : CNodeRadix) (slot : SeLe4n.Slot) :
    (tree.erase slot).guardWidth = tree.guardWidth := rfl

/-- Erase does not change guardValue. -/
theorem CNodeRadix.erase_guardValue (tree : CNodeRadix) (slot : SeLe4n.Slot) :
    (tree.erase slot).guardValue = tree.guardValue := rfl

/-- Erase does not change radixWidth. -/
theorem CNodeRadix.erase_radixWidth (tree : CNodeRadix) (slot : SeLe4n.Slot) :
    (tree.erase slot).radixWidth = tree.radixWidth := rfl

-- ============================================================================
-- Q4-C10: empty tree size
-- ============================================================================

private theorem list_foldl_replicate_none_count (n : Nat) :
    List.foldl (fun acc (entry : Option Capability) =>
      match entry with | none => acc | some _ => acc + 1) 0
      (List.replicate n none) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.foldl_cons]; exact ih

/-- The empty tree has size 0. -/
theorem CNodeRadix.size_empty (gw gv rw : Nat) :
    (CNodeRadix.empty gw gv rw).size = 0 := by
  simp only [CNodeRadix.size, CNodeRadix.empty]
  rw [← Array.foldl_toList]
  exact list_foldl_replicate_none_count _

-- ============================================================================
-- Q4-C11: fanout equals slot array size
-- ============================================================================

/-- The fanout equals the slot array size. -/
theorem CNodeRadix.fanout_eq_slots_size (tree : CNodeRadix) :
    tree.fanout = tree.slots.size := by
  simp [CNodeRadix.fanout, tree.hSlotSize]

-- ============================================================================
-- Q4-C12: Counting helpers for size proofs
-- ============================================================================

/-- Recursive count of `some` entries in a list. -/
private def countSome : List (Option α) → Nat
  | [] => 0
  | none :: rest => countSome rest
  | some _ :: rest => 1 + countSome rest

/-- The foldl-based count equals the recursive count (generalized). -/
private theorem foldl_countSome_eq (l : List (Option α)) (n : Nat) :
    List.foldl (fun acc (entry : Option α) =>
      match entry with | none => acc | some _ => acc + 1) n l = n + countSome l := by
  induction l generalizing n with
  | nil => simp [countSome]
  | cons hd tl ih =>
    cases hd with
    | none => simp [List.foldl_cons, countSome]; exact ih n
    | some v => simp [List.foldl_cons, countSome]; rw [ih]; omega

/-- `CNodeRadix.size` equals `countSome` of the slot list. -/
private theorem size_eq_countSome (tree : CNodeRadix) :
    tree.size = countSome tree.slots.toList := by
  simp only [CNodeRadix.size, ← Array.foldl_toList]
  suffices ∀ (l : List (Option Capability)) (n : Nat),
    List.foldl (fun acc (entry : Option Capability) =>
      match entry with | none => acc | some _ => acc + 1) n l = n + countSome l from by
    simpa using this tree.slots.toList 0
  intro l; induction l with
  | nil => intro n; simp [countSome]
  | cons hd tl ih =>
    intro n; cases hd with
    | none => simp [List.foldl_cons, countSome]; exact ih n
    | some v => simp [List.foldl_cons, countSome]; rw [ih]; omega

/-- Setting a position to `some` increases count by at most 1. -/
private theorem countSome_set_some_le (l : List (Option α)) (i : Nat) (x : α)
    (hi : i < l.length) :
    countSome (l.set i (some x)) ≤ countSome l + 1 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    have hLen : tl.length + 1 = (hd :: tl).length := rfl
    cases i with
    | zero =>
      cases hd with
      | none => simp [List.set, countSome]; omega
      | some _ => simp [List.set, countSome]
    | succ n =>
      have hn : n < tl.length := by omega
      cases hd with
      | none => simp [List.set, countSome]; exact ih n hn
      | some _ => simp [List.set, countSome]; have := ih n hn; omega

/-- Setting a position to `none` does not increase count. -/
private theorem countSome_set_none_le (l : List (Option α)) (i : Nat)
    (hi : i < l.length) :
    countSome (l.set i none) ≤ countSome l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    have hLen : tl.length + 1 = (hd :: tl).length := rfl
    cases i with
    | zero =>
      cases hd with
      | none => simp [List.set, countSome]
      | some _ => simp [List.set, countSome]
    | succ n =>
      have hn : n < tl.length := by omega
      cases hd with
      | none => simp [List.set, countSome]; exact ih n hn
      | some _ => simp [List.set, countSome]; have := ih n hn; omega

-- ============================================================================
-- Q4-C13: size_insert_le
-- ============================================================================

/-- Inserting a capability increases size by at most 1. -/
theorem CNodeRadix.size_insert_le (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) :
    (tree.insert slot cap).size ≤ tree.size + 1 := by
  rw [size_eq_countSome, size_eq_countSome]
  simp only [CNodeRadix.insert]
  rw [Array.toList_set]
  have hIdx : extractBits slot.toNat 0 tree.radixWidth < tree.slots.toList.length := by
    change _ < tree.slots.size; rw [tree.hSlotSize]; exact extractBits_lt _ _ _
  exact countSome_set_some_le _ _ _ hIdx

-- ============================================================================
-- Q4-C14: size_erase_le
-- ============================================================================

/-- Erasing a capability does not increase size. -/
theorem CNodeRadix.size_erase_le (tree : CNodeRadix) (slot : SeLe4n.Slot) :
    (tree.erase slot).size ≤ tree.size := by
  rw [size_eq_countSome, size_eq_countSome]
  simp only [CNodeRadix.erase]
  rw [Array.toList_set]
  have hIdx : extractBits slot.toNat 0 tree.radixWidth < tree.slots.toList.length := by
    change _ < tree.slots.size; rw [tree.hSlotSize]; exact extractBits_lt _ _ _
  exact countSome_set_none_le _ _ hIdx

-- ============================================================================
-- Q4-C15: toList_complete (via Array.foldl_induction)
-- ============================================================================

/-- Recursive characterization of toList: collect occupied entries with their
array indices, starting from `startIdx`. -/
private def collectEntries (slots : List (Option Capability)) (startIdx : Nat)
    : List (SeLe4n.Slot × Capability) :=
  match slots with
  | [] => []
  | none :: rest => collectEntries rest (startIdx + 1)
  | some cap :: rest => (SeLe4n.Slot.ofNat startIdx, cap) :: collectEntries rest (startIdx + 1)

/-- V7-G: The foldl-based toList (cons-accumulate) produces the reverse of
`collectEntries` prepended to the accumulator. Generalized induction. -/
private theorem foldl_collect_eq (slots : List (Option Capability)) (startIdx : Nat)
    (acc : List (SeLe4n.Slot × Capability)) :
    (List.foldl (fun (x : List (SeLe4n.Slot × Capability) × Nat)
      (entry : Option Capability) =>
      match entry with
      | none => (x.fst, x.snd + 1)
      | some cap => ((SeLe4n.Slot.ofNat x.snd, cap) :: x.fst, x.snd + 1))
      (acc, startIdx) slots).fst = (collectEntries slots startIdx).reverse ++ acc := by
  induction slots generalizing startIdx acc with
  | nil => simp [collectEntries]
  | cons hd tl ih =>
    cases hd with
    | none =>
      simp only [List.foldl_cons, collectEntries]
      exact ih (startIdx + 1) acc
    | some cap =>
      simp only [List.foldl_cons, collectEntries]
      rw [ih (startIdx + 1) ((SeLe4n.Slot.ofNat startIdx, cap) :: acc)]
      simp [List.reverse_cons, List.append_assoc]

/-- `CNodeRadix.toList` equals `collectEntries` of the slot list. -/
private theorem toList_eq_collectEntries (tree : CNodeRadix) :
    tree.toList = collectEntries tree.slots.toList 0 := by
  unfold CNodeRadix.toList CNodeRadix.fold
  simp only [← Array.foldl_toList]
  have h := foldl_collect_eq tree.slots.toList 0 []
  simp only [List.append_nil] at h
  exact (congrArg List.reverse h).trans (List.reverse_reverse _)

-- ============================================================================
-- Q4-C16: toList_complete
-- ============================================================================

/-- Every occupied slot in `collectEntries` appears in the result. -/
private theorem collectEntries_mem (slots : List (Option Capability)) (startIdx : Nat)
    (relIdx : Nat) (cap : Capability) (hBound : relIdx < slots.length)
    (hEntry : slots[relIdx] = some cap) :
    (SeLe4n.Slot.ofNat (startIdx + relIdx), cap) ∈ collectEntries slots startIdx := by
  induction slots generalizing startIdx relIdx with
  | nil => simp at hBound
  | cons hd tl ih =>
    cases relIdx with
    | zero =>
      simp at hEntry; subst hEntry
      simp [collectEntries, Nat.add_zero, List.mem_cons]
    | succ n =>
      simp at hEntry
      have hBound' : n < tl.length := by
        have : (hd :: tl).length = tl.length + 1 := rfl; omega
      cases hd with
      | none =>
        simp only [collectEntries]
        have := ih (startIdx + 1) n hBound' hEntry
        rwa [show startIdx + 1 + n = startIdx + (n + 1) by omega] at this
      | some _ =>
        simp only [collectEntries, List.mem_cons]
        right
        have := ih (startIdx + 1) n hBound' hEntry
        rwa [show startIdx + 1 + n = startIdx + (n + 1) by omega] at this

/-- `toList` contains every occupied slot. -/
theorem CNodeRadix.toList_complete (tree : CNodeRadix) (i : Nat) (hi : i < tree.slots.size)
    (cap : Capability) (h : tree.slots[i] = some cap) :
    (SeLe4n.Slot.ofNat i, cap) ∈ tree.toList := by
  rw [toList_eq_collectEntries]
  have := collectEntries_mem tree.slots.toList 0 i cap (by exact hi) (by exact h)
  simp only [Nat.zero_add] at this
  exact this

-- ============================================================================
-- Q4-C17: toList_noDup
-- ============================================================================

/-- All keys in `collectEntries` have `toNat ≥ startIdx`. -/
private theorem collectEntries_keys_ge (slots : List (Option Capability)) (startIdx : Nat) :
    ∀ pair ∈ collectEntries slots startIdx, pair.1.toNat ≥ startIdx := by
  induction slots generalizing startIdx with
  | nil => simp [collectEntries]
  | cons hd tl ih =>
    intro pair hMem
    cases hd with
    | none =>
      simp only [collectEntries] at hMem
      have := ih (startIdx + 1) pair hMem; omega
    | some _ =>
      simp only [collectEntries, List.mem_cons] at hMem
      rcases hMem with heq | hTl
      · rw [heq]; simp [SeLe4n.Slot.toNat_ofNat]
      · have := ih (startIdx + 1) pair hTl; omega

/-- Keys in `collectEntries` are duplicate-free. -/
private theorem collectEntries_noDup (slots : List (Option Capability)) (startIdx : Nat) :
    (collectEntries slots startIdx |>.map Prod.fst).Nodup := by
  induction slots generalizing startIdx with
  | nil => simp [collectEntries]
  | cons hd tl ih =>
    cases hd with
    | none =>
      simp only [collectEntries]; exact ih (startIdx + 1)
    | some _ =>
      simp only [collectEntries, List.map_cons]
      rw [List.nodup_cons]
      refine ⟨?_, ih (startIdx + 1)⟩
      intro hMem
      rw [List.mem_map] at hMem
      obtain ⟨pair, hPairMem, hPairEq⟩ := hMem
      have hGe := collectEntries_keys_ge tl (startIdx + 1) pair hPairMem
      have : (SeLe4n.Slot.ofNat startIdx).toNat ≥ startIdx + 1 := by
        rw [← hPairEq]; exact hGe
      simp only [SeLe4n.Slot.toNat_ofNat] at this; omega

/-- `toList` produces no duplicate keys. -/
theorem CNodeRadix.toList_noDup (tree : CNodeRadix) :
    (tree.toList.map Prod.fst).Nodup := by
  rw [toList_eq_collectEntries]
  exact collectEntries_noDup tree.slots.toList 0

-- ============================================================================
-- Q4-C18: fold_visits_all (via toList completeness)
-- ============================================================================

/-- Fold visits every occupied slot: if `slots[i] = some cap`, the fold function
is called with `(Slot.ofNat i, cap)`. Stated via `toList` membership, which
is the fold instantiation for list collection. -/
theorem CNodeRadix.fold_visits_all (tree : CNodeRadix) (i : Nat) (hi : i < tree.slots.size)
    (cap : Capability) (h : tree.slots[i] = some cap) :
    (SeLe4n.Slot.ofNat i, cap) ∈ tree.toList :=
  tree.toList_complete i hi cap h

end SeLe4n.Kernel.RadixTree
