/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Bridge

/-!
# Q2: KMap — Invariant-Carrying Kernel Map

`KMap κ ν` bundles an `RHTable κ ν` with its `invExt` proof, providing an
API-compatible replacement for `Std.HashMap` that does not require manual
`invExt` proof threading at every callsite.

All operations automatically maintain and carry forward the `invExt` witness.
This is the kernel-state map type used during the builder phase.
-/

namespace SeLe4n.Kernel.RobinHood

/-- A kernel map: `RHTable` bundled with its `invExt` invariant proof
    and the `size < capacity` bound (maintained by all operations).
    Drop-in replacement for `Std.HashMap` in kernel state definitions. -/
structure KMap (κ : Type) (ν : Type) [BEq κ] [Hashable κ] where
  table : RHTable κ ν
  hInv : table.invExt
  hSizeLt : table.size < table.capacity
  hCapGe4 : 4 ≤ table.capacity

namespace KMap

variable {κ : Type} {ν : Type} [BEq κ] [Hashable κ]

/-- Create an empty KMap. Capacity must be ≥ 4 (default 16). -/
def empty (cap : Nat := 16) (h : 0 < cap := by omega) (hGe4 : 4 ≤ cap := by omega) : KMap κ ν :=
  ⟨RHTable.empty cap h, RHTable.empty_invExt cap h,
   by simp [RHTable.empty]; omega,
   by simp [RHTable.empty]; omega⟩

/-- Lookup a key. -/
@[inline] def get? (m : KMap κ ν) (k : κ) : Option ν :=
  m.table.get? k

/-- Check if a key is present. -/
@[inline] def contains (m : KMap κ ν) (k : κ) : Bool :=
  m.table.contains k

/-- Insert a key-value pair. Automatically preserves all invariants. -/
def insert [LawfulBEq κ] (m : KMap κ ν) (k : κ) (v : ν) : KMap κ ν :=
  have hCapGe4' : 4 ≤ (m.table.insert k v).capacity := by
    have hCap := m.hCapGe4
    simp only [RHTable.insert]
    split
    · have h1 := RHTable.insertNoResize_capacity m.table.resize k v
      have h2 := m.table.resize_fold_capacity
      omega
    · have h1 := RHTable.insertNoResize_capacity m.table k v
      omega
  ⟨m.table.insert k v,
   m.table.insert_preserves_invExt k v m.hInv,
   m.table.insert_size_lt_capacity k v m.hInv m.hSizeLt m.hCapGe4,
   hCapGe4'⟩

/-- Erase a key. Automatically preserves all invariants. -/
def erase [LawfulBEq κ] (m : KMap κ ν) (k : κ) : KMap κ ν :=
  have hCapGe4' : 4 ≤ (m.table.erase k).capacity := by
    unfold RHTable.erase; simp only []; split <;> exact m.hCapGe4
  ⟨m.table.erase k,
   m.table.erase_preserves_invExt k m.hInv m.hSizeLt,
   m.table.erase_size_lt_capacity k m.hSizeLt,
   hCapGe4'⟩

/-- Filter entries by a predicate. Preserves all invariants. -/
def filter [LawfulBEq κ] (m : KMap κ ν) (f : κ → ν → Bool) : KMap κ ν :=
  have hCapGe4' : 4 ≤ (m.table.filter f).capacity := by
    unfold RHTable.filter RHTable.fold
    exact Array.foldl_induction
      (motive := fun _ (acc : RHTable κ ν) => 4 ≤ acc.capacity)
      (by simp [RHTable.empty]; exact m.hCapGe4)
      (fun i acc hAcc => by
        simp only []; split
        · exact hAcc
        · rename_i entry _
          by_cases hf : f entry.key entry.value
          · simp only [hf, ite_true]; rw [RHTable.insertNoResize_capacity]; exact hAcc
          · simp only [show (f entry.key entry.value) = false from by simp [hf]]; exact hAcc)
  ⟨m.table.filter f,
   RHTable.filter_preserves_invExt m.table f m.hInv,
   RHTable.filter_size_lt_capacity m.table f m.hSizeLt m.hInv.1,
   hCapGe4'⟩

/-- Fold over all entries. -/
@[inline] def fold (m : KMap κ ν) (init : γ) (f : γ → κ → ν → γ) : γ :=
  m.table.fold init f

/-- Convert to list of key-value pairs. -/
def toList (m : KMap κ ν) : List (κ × ν) :=
  m.table.toList

/-- Size of the map. -/
@[inline] def size (m : KMap κ ν) : Nat := m.table.size

/-- Capacity of the map. -/
@[inline] def capacity (m : KMap κ ν) : Nat := m.table.capacity

end KMap

-- ============================================================================
-- Instances
-- ============================================================================

instance [BEq κ] [Hashable κ] : Inhabited (KMap κ ν) where
  default := KMap.empty

instance [BEq κ] [Hashable κ] : EmptyCollection (KMap κ ν) where
  emptyCollection := KMap.empty

instance [BEq κ] [Hashable κ] [BEq ν] : BEq (KMap κ ν) where
  beq a b := a.table == b.table

instance [BEq κ] [Hashable κ] : Membership κ (KMap κ ν) where
  mem m k := m.contains k = true

/-- GetElem? instance for bracket notation `m[k]?`. -/
instance [BEq κ] [Hashable κ] : GetElem? (KMap κ ν) κ ν (fun m k => (m.get? k).isSome) where
  getElem? m k := m.get? k
  getElem m k h := (m.get? k).get h
  getElem! m k := (m.get? k).getD default

-- ============================================================================
-- Bridge lemmas for simp-based proofs
-- ============================================================================

/-- After inserting key `k`, lookup returns `some v`. -/
@[simp] theorem KMap.get?_insert_self [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k : κ) (v : ν) :
    (m.insert k v).get? k = some v := by
  simp only [KMap.insert, KMap.get?]
  exact RHTable.getElem?_insert_self m.table k v m.hInv

/-- Inserting key `k` does not affect lookups of other keys. -/
theorem KMap.get?_insert_ne [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k k' : κ) (v : ν) (hNe : ¬(k == k') = true) :
    (m.insert k v).get? k' = m.get? k' := by
  simp only [KMap.insert, KMap.get?]
  exact RHTable.getElem?_insert_ne m.table k k' v hNe m.hInv

/-- Combined insert lookup characterization (matches HashMap_getElem?_insert). -/
theorem KMap.getElem?_insert [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k : κ) (v : ν) (a : κ) :
    (m.insert k v).get? a = if k == a then some v else m.get? a := by
  by_cases h : (k == a) = true
  · simp only [h, ite_true]
    have hka : a = k := (eq_of_beq h).symm
    subst hka
    exact KMap.get?_insert_self m a v
  · simp only [show (k == a) = false from Bool.eq_false_iff.mpr h]
    exact KMap.get?_insert_ne m k a v h

/-- After erasing key `k`, lookup returns `none`. -/
theorem KMap.get?_erase_self [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k : κ) :
    (m.erase k).get? k = none := by
  simp only [KMap.erase, KMap.get?]
  exact RHTable.getElem?_erase_self m.table k m.hInv

/-- Combined erase lookup characterization (matches HashMap_getElem?_erase). -/
theorem KMap.getElem?_erase [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k : κ) (a : κ) :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  by_cases h : (k == a) = true
  · simp only [h, ite_true]
    have hka : a = k := (eq_of_beq h).symm; subst hka
    exact KMap.get?_erase_self m a
  · simp only [show (k == a) = false from Bool.eq_false_iff.mpr h]
    simp only [KMap.erase, KMap.get?]
    exact RHTable.getElem?_erase_ne m.table k a h m.hInv m.hSizeLt

/-- Lookup in empty KMap returns none. -/
@[simp] theorem KMap.get?_empty [BEq κ] [Hashable κ] (k : κ) :
    (KMap.empty : KMap κ ν).get? k = none := by
  simp only [KMap.empty, KMap.get?]
  exact RHTable.getElem?_empty 16 (by omega) k

/-- Filter preserves key when predicate is true. -/
theorem KMap.filter_preserves_key [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (f : κ → ν → Bool) (k : κ)
    (hTrue : ∀ (k' : κ) (v : ν), (k' == k) = true → f k' v = true) :
    (m.filter f).get? k = m.get? k := by
  simp only [KMap.filter, KMap.get?]
  exact RHTable.filter_preserves_key m.table f k hTrue m.hInv

/-- Contains after insert self. -/
@[simp] theorem KMap.contains_insert_self [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k : κ) (v : ν) :
    (m.insert k v).contains k = true := by
  simp only [KMap.contains, KMap.insert, RHTable.contains]
  rw [RHTable.getElem?_insert_self m.table k v m.hInv]
  rfl

/-- Contains after erase self. -/
theorem KMap.contains_erase_self [BEq κ] [Hashable κ] [LawfulBEq κ]
    (m : KMap κ ν) (k : κ) :
    (m.erase k).contains k = false := by
  simp [KMap.contains, RHTable.contains]
  exact KMap.get?_erase_self m k

/-- Fold preserves a property. -/
theorem KMap.fold_preserves [BEq κ] [Hashable κ] (m : KMap κ ν) (init : γ) (f : γ → κ → ν → γ)
    (P : γ → Prop) (hInit : P init)
    (hStep : ∀ acc k v, P acc → P (f acc k v)) :
    P (m.fold init f) :=
  RHTable.fold_preserves m.table init f P hInit hStep

end SeLe4n.Kernel.RobinHood
