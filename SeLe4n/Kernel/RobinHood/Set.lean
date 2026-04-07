/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Bridge

/-!
# Q2-B: Verified Hash Set backed by Robin Hood Hash Table

`RHSet κ` is a newtype wrapper around `RHTable κ Unit`, providing a verified
hash set with the same invariant guarantees (well-formedness, probe chain
dominance, no duplicate keys) as the underlying Robin Hood table.

This replaces `Std.HashSet` for all state-persistent set fields in the kernel.
Algorithm-local `Std.HashSet` usage (BFS visited sets) is retained.
-/

namespace SeLe4n.Kernel.RobinHood

/-- A verified hash set backed by `RHTable κ Unit`. -/
structure RHSet (κ : Type) [BEq κ] [Hashable κ] [LawfulBEq κ] where
  table : RHTable κ Unit

/-- Create an empty `RHSet` with the given capacity. -/
def RHSet.empty [BEq κ] [Hashable κ] [LawfulBEq κ] (cap : Nat := 16) (hCapGe4 : 4 ≤ cap := by omega) : RHSet κ :=
  ⟨RHTable.empty cap hCapGe4⟩

/-- Check if the set contains the given key. -/
def RHSet.contains [BEq κ] [Hashable κ] [LawfulBEq κ] (s : RHSet κ) (k : κ) : Bool :=
  s.table.contains k

/-- Insert a key into the set. -/
def RHSet.insert [BEq κ] [Hashable κ] [LawfulBEq κ] (s : RHSet κ) (k : κ) : RHSet κ :=
  ⟨s.table.insert k ()⟩

/-- Remove a key from the set. -/
def RHSet.erase [BEq κ] [Hashable κ] [LawfulBEq κ] (s : RHSet κ) (k : κ) : RHSet κ :=
  ⟨s.table.erase k⟩

/-- Convert the set to a list of keys. -/
def RHSet.toList [BEq κ] [Hashable κ] [LawfulBEq κ] (s : RHSet κ) : List κ :=
  s.table.toList.map (·.1)

/-- Build a set from a list of keys. -/
def RHSet.ofList [BEq κ] [Hashable κ] [LawfulBEq κ] (keys : List κ)
    (cap : Nat := 16) (hCapGe4 : 4 ≤ cap := by omega) : RHSet κ :=
  ⟨RHTable.ofList (keys.map fun k => (k, ())) cap hCapGe4⟩

-- ============================================================================
-- Instances
-- ============================================================================

instance [BEq κ] [Hashable κ] [LawfulBEq κ] : Inhabited (RHSet κ) where
  default := RHSet.empty

instance [BEq κ] [Hashable κ] [LawfulBEq κ] : BEq (RHSet κ) where
  beq a b := a.table == b.table

instance [BEq κ] [Hashable κ] [LawfulBEq κ] : Membership κ (RHSet κ) where
  mem s k := s.contains k = true

instance [BEq κ] [Hashable κ] [LawfulBEq κ] : EmptyCollection (RHSet κ) where
  emptyCollection := RHSet.empty

-- ============================================================================
-- Bridge lemmas
-- ============================================================================

/-- Q2-B: Empty set contains nothing. -/
theorem RHSet.contains_empty [BEq κ] [Hashable κ] [LawfulBEq κ] (k : κ) :
    (RHSet.empty : RHSet κ).contains k = false := by
  simp [RHSet.contains, RHSet.empty, RHTable.contains,
        RHTable.getElem?_empty]

/-- Q2-B: After inserting `k`, the set contains `k`. -/
theorem RHSet.contains_insert_self [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (hExt : s.table.invExt) :
    (s.insert k).contains k = true := by
  simp [RHSet.contains, RHSet.insert, RHTable.contains,
        RHTable.getElem?_insert_self s.table k () hExt]

/-- Q2-B: Inserting `k` does not affect containment of other keys. -/
theorem RHSet.contains_insert_ne [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k k' : κ) (hNe : ¬(k == k') = true)
    (hExt : s.table.invExt) :
    (s.insert k).contains k' = s.contains k' := by
  simp [RHSet.contains, RHSet.insert, RHTable.contains,
        RHTable.getElem?_insert_ne s.table k k' () hNe hExt]

/-- Q2-B: After erasing `k`, the set does not contain `k`. -/
theorem RHSet.contains_erase_self [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (hExt : s.table.invExt) :
    (s.erase k).contains k = false := by
  simp [RHSet.contains, RHSet.erase, RHTable.contains,
        RHTable.getElem?_erase_self s.table k hExt]

/-- Q2-B: Erasing `k` does not affect containment of other keys. -/
theorem RHSet.contains_erase_ne [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k k' : κ) (hNe : ¬(k == k') = true)
    (hExt : s.table.invExt) (hSize : s.table.size < s.table.capacity) :
    (s.erase k).contains k' = s.contains k' := by
  simp [RHSet.contains, RHSet.erase, RHTable.contains,
        RHTable.getElem?_erase_ne s.table k k' hNe hExt hSize]

/-- Q2-B: Insert preserves invExt. -/
theorem RHSet.insert_preserves_invExt [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (hExt : s.table.invExt) :
    (s.insert k).table.invExt :=
  s.table.insert_preserves_invExt k () hExt

/-- Q2-B: Erase preserves invExt. -/
theorem RHSet.erase_preserves_invExt [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (hExt : s.table.invExt)
    (hSize : s.table.size < s.table.capacity) :
    (s.erase k).table.invExt :=
  s.table.erase_preserves_invExt k hExt hSize

/-- Q2-B: Empty set satisfies invExt. -/
theorem RHSet.empty_invExt [BEq κ] [Hashable κ] [LawfulBEq κ] :
    (RHSet.empty : RHSet κ).table.invExt :=
  RHTable.empty_invExt' 16 (by omega)

-- ============================================================================
-- V3-B Phase 2: invExtK wrappers for RHSet
-- ============================================================================

/-- Kernel-level extended invariant for RHSet (delegates to RHTable.invExtK). -/
def RHSet.invExtK [BEq κ] [Hashable κ] [LawfulBEq κ] (s : RHSet κ) : Prop := s.table.invExtK

/-- Empty set satisfies invExtK. -/
theorem RHSet.empty_invExtK [BEq κ] [Hashable κ] [LawfulBEq κ] :
    (RHSet.empty : RHSet κ).table.invExtK :=
  RHTable.empty_invExtK 16 (by omega)

/-- Insert preserves invExtK. -/
theorem RHSet.insert_preserves_invExtK [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (hK : s.table.invExtK) :
    (s.insert k).table.invExtK :=
  s.table.insert_preserves_invExtK k () hK

/-- Erase preserves invExtK. -/
theorem RHSet.erase_preserves_invExtK [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (hK : s.table.invExtK) :
    (s.erase k).table.invExtK :=
  s.table.erase_preserves_invExtK k hK

/-- Erasing `k` does not affect containment of other keys (kernel-level API). -/
theorem RHSet.contains_erase_ne_K [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k k' : κ) (hNe : ¬(k == k') = true) (hK : s.table.invExtK) :
    (s.erase k).contains k' = s.contains k' := by
  simp [RHSet.contains, RHSet.erase, RHTable.contains,
        RHTable.getElem?_erase_ne_K s.table k k' hNe hK]

-- ============================================================================
-- W6-F (L-13): Public invExtK API — preservation theorems using RHSet.invExtK
-- ============================================================================

/-- W6-F: Insert preserves `RHSet.invExtK` (public API form). -/
theorem RHSet.insert_invExtK [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (h : s.invExtK) : (s.insert k).invExtK :=
  RHSet.insert_preserves_invExtK s k h

/-- W6-F: Erase preserves `RHSet.invExtK` (public API form). -/
theorem RHSet.erase_invExtK [BEq κ] [Hashable κ] [LawfulBEq κ]
    (s : RHSet κ) (k : κ) (h : s.invExtK) : (s.erase k).invExtK :=
  RHSet.erase_preserves_invExtK s k h

/-- W6-F: Empty set satisfies `RHSet.invExtK` (public API form). -/
theorem RHSet.empty_invExtK' [BEq κ] [Hashable κ] [LawfulBEq κ] :
    (RHSet.empty : RHSet κ).invExtK :=
  RHSet.empty_invExtK

end SeLe4n.Kernel.RobinHood
