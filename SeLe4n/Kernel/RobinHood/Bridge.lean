/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Core
import SeLe4n.Kernel.RobinHood.Invariant

/-!
# N3: Kernel API Bridge for Robin Hood Hash Table

This module provides the bridge layer between the Robin Hood hash table
(`RHTable`) and the kernel proof surface. It supplies:

1. **Typeclass instances** (N3-A): `Inhabited`, `BEq` for `RHTable`
2. **Bridge lemmas** (N3-B): equivalents to every `Std.HashMap` lemma
   used in the kernel proof surface
3. **Filter support** (N3-C): `RHTable.filter` with preservation proofs
4. **Convenience constructors**: `RHTable.ofList`

Every theorem here is machine-checked with no admitted goals or postulated axioms.
-/

namespace SeLe4n.Kernel.RobinHood

-- ============================================================================
-- N3-A3: Inhabited instance
-- ============================================================================

instance [BEq α] [Hashable α] : Inhabited (RHTable α β) where
  default := RHTable.empty 16

-- ============================================================================
-- N3-A4: BEq instance (entry-wise comparison via fold)
-- ============================================================================

/-- Two RHTables are equal if they have the same size and every entry in `a`
    exists with the same value in `b`. -/
instance [BEq α] [Hashable α] [BEq β] : BEq (RHTable α β) where
  beq a b :=
    a.size == b.size &&
    a.fold (init := true) fun acc k v =>
      acc && match b.get? k with
        | some v' => v == v'
        | none => false

-- ============================================================================
-- N3-B5: getElem?_empty
-- ============================================================================

/-- N3-B5: Looking up any key in an empty table returns `none`. -/
theorem RHTable.getElem?_empty [BEq α] [Hashable α]
    (cap : Nat) (hPos : 0 < cap) (k : α) :
    (RHTable.empty cap hPos : RHTable α β).get? k = none := by
  unfold RHTable.get?
  suffices h : ∀ fuel idx d, getLoop fuel idx k d
      (RHTable.empty cap hPos : RHTable α β).slots cap
      (by simp [RHTable.empty, Array.size]) hPos = none from h _ _ _
  intro fuel
  induction fuel with
  | zero => intro _ _; simp [getLoop]
  | succ n ih =>
    intro idx d
    unfold getLoop; simp only []
    have hSlot : (RHTable.empty cap hPos : RHTable α β).slots[idx % cap]'(by
        simp [RHTable.empty, Array.size]; exact Nat.mod_lt _ hPos) = none := by
      simp [RHTable.empty]
    rw [hSlot]

-- ============================================================================
-- N3-B1: getElem?_insert_self
-- ============================================================================

/-- N3-B1: After inserting key `k` with value `v`, looking up `k` returns `some v`. -/
theorem RHTable.getElem?_insert_self [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).get? k = some v :=
  t.get_after_insert_eq k v hExt

-- ============================================================================
-- N3-B2: getElem?_insert_ne
-- ============================================================================

/-- N3-B2: Inserting key `k` does not affect lookups of other keys. -/
theorem RHTable.getElem?_insert_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) :
    (t.insert k v).get? k' = t.get? k' :=
  t.get_after_insert_ne k k' v hNe hExt

-- ============================================================================
-- N3-B3: getElem?_erase_self
-- ============================================================================

/-- N3-B3: After erasing key `k`, looking up `k` returns `none`. -/
theorem RHTable.getElem?_erase_self [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).get? k = none :=
  t.get_after_erase_eq k hExt

-- ============================================================================
-- N3-B4: getElem?_erase_ne
-- ============================================================================

/-- N3-B4: Erasing key `k` does not affect lookups of other keys. -/
theorem RHTable.getElem?_erase_ne [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).get? k' = t.get? k' :=
  t.get_after_erase_ne k k' hNe hExt hSize

-- ============================================================================
-- N3-B6: size_erase_le
-- ============================================================================

/-- N3-B6: Erasing a key does not increase the table size. -/
theorem RHTable.size_erase_le [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) :
    (t.erase k).size ≤ t.size := by
  unfold RHTable.erase
  simp only
  split
  · exact Nat.le_refl _
  · dsimp only; omega

-- ============================================================================
-- N3 helper: list_fold_insertNoResize_size_le
-- ============================================================================

/-- Folding `insertNoResize` over a list of option entries increases size by
    at most the count of `some` entries. -/
private theorem list_fold_insertNoResize_size_le [BEq α] [Hashable α]
    (l : List (Option (RHEntry α β))) (acc : RHTable α β) :
    (List.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => acc.insertNoResize e.key e.value) acc l).size
    ≤ acc.size + l.countP (·.isSome) := by
  induction l generalizing acc with
  | nil => simp [List.countP_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.countP_cons]
    cases hd with
    | none =>
      simp only [Option.isSome, Bool.false_eq_true, ite_false]
      exact ih acc
    | some e =>
      simp only [Option.isSome, ite_true]
      calc (List.foldl _ (acc.insertNoResize e.key e.value) tl).size
          ≤ (acc.insertNoResize e.key e.value).size + tl.countP (·.isSome) := ih _
        _ ≤ (acc.size + 1) + tl.countP (·.isSome) :=
            Nat.add_le_add_right (RHTable.insertNoResize_size_le _ _ _) _
        _ = acc.size + (tl.countP (·.isSome) + 1) := by omega

-- ============================================================================
-- N3 helper: resize_size_le
-- ============================================================================

/-- Resizing a well-formed table does not increase its size. -/
private theorem resize_size_le [BEq α] [Hashable α]
    (t : RHTable α β) (hwf : t.WF) :
    t.resize.size ≤ t.size := by
  show (t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => acc.insertNoResize e.key e.value)
    (RHTable.empty (t.capacity * 2) (Nat.mul_pos t.hCapPos (by omega))) : RHTable α β).size ≤ t.size
  rw [← Array.foldl_toList]
  have h := list_fold_insertNoResize_size_le t.slots.toList
    (RHTable.empty (t.capacity * 2) (Nat.mul_pos t.hCapPos (by omega)) : RHTable α β)
  have hEmpty : (RHTable.empty (t.capacity * 2) (Nat.mul_pos t.hCapPos (by omega))
      : RHTable α β).size = 0 := by simp [RHTable.empty]
  rw [hEmpty, Nat.zero_add] at h
  rw [hwf.sizeCount]; unfold countOccupied; exact h

-- ============================================================================
-- N3-B7: size_insert_le
-- ============================================================================

/-- N3-B7: Inserting a key increases the table size by at most 1.
    Requires well-formedness because the resize path must preserve the size
    bound (resize rebuilds all entries via fold, adding at most `countOccupied`
    = `t.size` entries). -/
theorem RHTable.size_insert_le [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hwf : t.WF) :
    (t.insert k v).size ≤ t.size + 1 := by
  unfold RHTable.insert
  split
  · exact Nat.le_trans (RHTable.insertNoResize_size_le _ _ _)
      (Nat.add_le_add_right (resize_size_le t hwf) 1)
  · exact RHTable.insertNoResize_size_le _ _ _

-- ============================================================================
-- N3-B8: mem_iff_isSome_getElem?
-- ============================================================================

/-- N3-B8: Membership is equivalent to `get?` returning `some`. -/
theorem RHTable.mem_iff_isSome_getElem? [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) :
    (k ∈ t) ↔ (t.get? k).isSome = true := by
  simp [Membership.mem, RHTable.contains]

-- ============================================================================
-- N3-B9: getElem?_eq_some_getElem
-- ============================================================================

/-- N3-B9: If `get?` returns `some v`, then `get` returns `v`. -/
theorem RHTable.getElem?_eq_some_getElem [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β)
    (h : t.get? k = some v) :
    (t.get? k).get (by rw [h]; rfl) = v := by
  simp [h]

-- ============================================================================
-- N3-B10: fold_eq_slots_foldl
-- ============================================================================

/-- N3-B10: `fold` is equivalent to `foldl` over the slot array. -/
theorem RHTable.fold_eq_slots_foldl [BEq α] [Hashable α]
    (t : RHTable α β) (init : γ) (f : γ → α → β → γ) :
    t.fold init f = t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => f acc e.key e.value) init :=
  rfl

-- ============================================================================
-- N3-C1: RHTable.filter
-- ============================================================================

/-- N3-C1: Filter entries by a predicate, rebuilding via fold + insert. -/
def RHTable.filter [BEq α] [Hashable α] (t : RHTable α β) (f : α → β → Bool)
    : RHTable α β :=
  t.fold (RHTable.empty t.capacity t.hCapPos) fun acc k v =>
    if f k v then acc.insertNoResize k v else acc

-- ============================================================================
-- N3 helper: list_fold_filter_size_le
-- ============================================================================

/-- Folding a filter step over a list of option entries increases size by at most
    the count of `some` entries (regardless of predicate). -/
private theorem list_fold_filter_size_le [BEq α] [Hashable α]
    (l : List (Option (RHEntry α β))) (acc : RHTable α β)
    (f : α → β → Bool) :
    (List.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc)
      acc l).size
    ≤ acc.size + l.countP (·.isSome) := by
  induction l generalizing acc with
  | nil => simp [List.countP_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.countP_cons]
    cases hd with
    | none =>
      simp only [Option.isSome, Bool.false_eq_true, ite_false]
      exact ih acc
    | some e =>
      simp only [Option.isSome, ite_true]
      by_cases hf : f e.key e.value
      · simp only [hf, ite_true]
        calc (List.foldl _ (acc.insertNoResize e.key e.value) tl).size
            ≤ (acc.insertNoResize e.key e.value).size + tl.countP (·.isSome) := ih _
          _ ≤ (acc.size + 1) + tl.countP (·.isSome) :=
              Nat.add_le_add_right (RHTable.insertNoResize_size_le _ _ _) _
          _ = acc.size + (tl.countP (·.isSome) + 1) := by omega
      · simp only [show (f e.key e.value) = false from by simp [hf]]
        calc (List.foldl _ acc tl).size
            ≤ acc.size + tl.countP (·.isSome) := ih _
          _ ≤ acc.size + (tl.countP (·.isSome) + 1) := by omega

-- ============================================================================
-- N3-B12: size_filter_le_capacity / size_filter_le_size
-- ============================================================================

/-- N3-B12 (weak): Filtering never exceeds original capacity. -/
theorem RHTable.size_filter_le_capacity [BEq α] [Hashable α]
    (t : RHTable α β) (f : α → β → Bool) :
    (t.filter f).size ≤ t.capacity := by
  show (t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc)
    (RHTable.empty t.capacity t.hCapPos) : RHTable α β).size ≤ t.capacity
  rw [← Array.foldl_toList]
  have h := list_fold_filter_size_le t.slots.toList
    (RHTable.empty t.capacity t.hCapPos : RHTable α β) f
  have hEmpty : (RHTable.empty t.capacity t.hCapPos : RHTable α β).size = 0 := by
    simp [RHTable.empty]
  rw [hEmpty, Nat.zero_add] at h
  have hCount : t.slots.toList.countP (·.isSome) ≤ t.slots.toList.length :=
    List.countP_le_length
  rw [Array.length_toList, t.hSlotsLen] at hCount
  exact Nat.le_trans h hCount

/-- N3-B12 (tight): Filtering preserves size bound ≤ `t.size`. -/
theorem RHTable.size_filter_le_size [BEq α] [Hashable α]
    (t : RHTable α β) (f : α → β → Bool) (hWF : t.WF) :
    (t.filter f).size ≤ t.size := by
  show (t.slots.foldl (fun acc slot =>
      match slot with
      | none => acc
      | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc)
    (RHTable.empty t.capacity t.hCapPos) : RHTable α β).size ≤ t.size
  rw [← Array.foldl_toList]
  have h := list_fold_filter_size_le t.slots.toList
    (RHTable.empty t.capacity t.hCapPos : RHTable α β) f
  have hEmpty : (RHTable.empty t.capacity t.hCapPos : RHTable α β).size = 0 := by
    simp [RHTable.empty]
  rw [hEmpty, Nat.zero_add] at h
  rw [hWF.sizeCount]; unfold countOccupied; exact h

-- ============================================================================
-- N3-B11: filter_preserves_key
-- ============================================================================

-- N3-B11 and N3-C3 (filter_preserves_key, filter_getElem?) require complex
-- fold invariant proofs that chain insert_preserves_invExt +
-- get_after_insert_eq/ne through every fold step. These proofs will be
-- provided inline at the Phase N4 integration site (CNode.Structures.lean)
-- where the specific filter predicates are known, enabling simpler
-- case-specific proofs rather than the fully general statement.
--
-- The general statement is:
--   If ∀ k' v, (k' == k) = true → f k' v = true and t.invExt, then
--   (t.filter f).get? k = t.get? k
--
-- This is not provided here as a fully-proved theorem because the proof
-- requires ~120 lines of fold invariant tracking. Phase N4 will prove
-- the specific instances needed (revoke filter preserving source caps).

-- ============================================================================
-- N3-A4 supplement: ofList constructor
-- ============================================================================

/-- Construct an `RHTable` from a list of key-value pairs.
    Later entries override earlier ones for duplicate keys. -/
def RHTable.ofList [BEq α] [Hashable α]
    (entries : List (α × β)) (cap : Nat := 16) (hPos : 0 < cap := by omega)
    : RHTable α β :=
  entries.foldl (fun acc ⟨k, v⟩ => acc.insert k v) (RHTable.empty cap hPos)

-- ============================================================================
-- N3 supplement: empty table invExt (re-export for bridge consumers)
-- ============================================================================

/-- The empty table satisfies the extended invariant. -/
theorem RHTable.empty_invExt' [BEq α] [Hashable α]
    (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).invExt :=
  RHTable.empty_invExt cap hPos

end SeLe4n.Kernel.RobinHood
