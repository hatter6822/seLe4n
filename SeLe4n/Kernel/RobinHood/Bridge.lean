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

Every theorem here is proved without `sorry` or `axiom`.
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
    rw [hSlot]; rfl

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
  split
  · exact Nat.le_refl _
  · simp only; omega

-- ============================================================================
-- N3-B7: size_insert_le
-- ============================================================================

/-- N3-B7: Inserting a key increases the table size by at most 1. -/
theorem RHTable.size_insert_le [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) :
    (t.insert k v).size ≤ t.size + 1 := by
  unfold RHTable.insert
  split
  · exact Nat.le_trans (RHTable.insertNoResize_size_le _ _ _)
      (Nat.add_le_add_right (by omega) 1)
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
-- N3-B12: size_filter_le_size (with invExt hypothesis)
-- ============================================================================

/-- N3-B12 (weak): Filtering never exceeds original capacity. -/
theorem RHTable.size_filter_le_capacity [BEq α] [Hashable α]
    (t : RHTable α β) (f : α → β → Bool) :
    (t.filter f).size ≤ t.capacity := by
  unfold filter fold
  have hStep : ∀ (i : Fin t.slots.size) (acc : RHTable α β),
      acc.size ≤ i.val →
      (match t.slots[i] with
       | none => acc
       | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc).size
      ≤ i.val + 1 := by
    intro i acc hAcc
    split
    · omega
    · split
      · exact Nat.le_trans (RHTable.insertNoResize_size_le _ _ _) (by omega)
      · omega
  have hInit : (RHTable.empty t.capacity t.hCapPos : RHTable α β).size ≤ 0 := by
    simp [RHTable.empty]
  have hFinal := Array.foldl_induction
    (motive := fun i (acc : RHTable α β) => acc.size ≤ i)
    hInit hStep
  rw [t.hSlotsLen] at hFinal; exact hFinal

/-- Count of occupied (isSome) entries in the first `n` slots. -/
private def countSomePrefix (slots : Array (Option γ)) (n : Nat) : Nat :=
  slots.foldl (fun acc s => acc + if s.isSome then 1 else 0) 0 (stop := n)

private theorem countSomePrefix_step (slots : Array (Option γ)) (i : Nat)
    (hi : i < slots.size) :
    countSomePrefix slots (i + 1) =
      countSomePrefix slots i + if (slots[i]'hi).isSome then 1 else 0 := by
  unfold countSomePrefix
  rw [Array.foldl_loop_step hi]

private theorem countSomePrefix_full_eq_countOccupied
    (slots : Array (Option (RHEntry α β))) :
    countSomePrefix slots slots.size = countOccupied slots := by
  unfold countSomePrefix countOccupied
  simp [Array.foldl_eq_foldl_toList, List.countP]
  induction slots.toList with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.foldl, List.countP_cons]
    cases hd <;> simp [ih]

/-- N3-B12 (tight): Filtering preserves size bound ≤ `t.size`. -/
theorem RHTable.size_filter_le_size [BEq α] [Hashable α]
    (t : RHTable α β) (f : α → β → Bool) (hWF : t.WF) :
    (t.filter f).size ≤ t.size := by
  unfold filter fold
  have hStep : ∀ (i : Fin t.slots.size) (acc : RHTable α β),
      acc.size ≤ countSomePrefix t.slots i.val →
      (match t.slots[i] with
       | none => acc
       | some e => if f e.key e.value then acc.insertNoResize e.key e.value else acc).size
      ≤ countSomePrefix t.slots (i.val + 1) := by
    intro ⟨i, hi⟩ acc hAcc
    rw [countSomePrefix_step t.slots i hi]
    split
    · -- none: acc unchanged, isSome = false, count unchanged
      simp; omega
    · -- some e: isSome = true, count +1
      simp; split
      · exact Nat.le_trans (RHTable.insertNoResize_size_le _ _ _) (by omega)
      · omega
  have hInit : (RHTable.empty t.capacity t.hCapPos : RHTable α β).size
      ≤ countSomePrefix t.slots 0 := by
    simp [RHTable.empty, countSomePrefix, Array.foldl]
  have hFinal := Array.foldl_induction
    (motive := fun i (acc : RHTable α β) => acc.size ≤ countSomePrefix t.slots i)
    hInit hStep
  -- hFinal : result.size ≤ countSomePrefix t.slots t.slots.size
  --        = countOccupied t.slots = t.size (by WF)
  rw [countSomePrefix_full_eq_countOccupied] at hFinal
  rw [hWF.sizeCount]; exact hFinal

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
-- This is not provided here as a zero-sorry theorem because the proof
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
