/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood.Core

namespace SeLe4n.Kernel.RobinHood

-- ============================================================================
-- N2: Invariant Definitions
-- ============================================================================

/-- N2-B: Probe distance correctness — every occupied slot's `dist` field
    reflects exact displacement from the entry's ideal (home) position. -/
def RHTable.distCorrect [Hashable α] (t : RHTable α β) : Prop :=
  ∀ (i : Nat) (hi : i < t.capacity) (e : RHEntry α β),
    t.slots[i]'(t.hSlotsLen ▸ hi) = some e →
    e.dist = (i + t.capacity - idealIndex e.key t.capacity t.hCapPos) % t.capacity

/-- N2-C: No duplicate keys — no two occupied slots share a BEq-equal key. -/
def RHTable.noDupKeys [BEq α] (t : RHTable α β) : Prop :=
  ∀ (i j : Nat) (hi : i < t.capacity) (hj : j < t.capacity)
    (ei ej : RHEntry α β),
    t.slots[i]'(t.hSlotsLen ▸ hi) = some ei →
    t.slots[j]'(t.hSlotsLen ▸ hj) = some ej →
    (ei.key == ej.key) = true → i = j

/-- N2-D: Robin Hood ordering — within each contiguous cluster of occupied
    slots, probe distances are non-decreasing. An entry at its ideal position
    (dist = 0) starts a new cluster. -/
def RHTable.robinHoodOrdered (t : RHTable α β) : Prop :=
  ∀ (i : Nat) (hi : i < t.capacity) (ei ej : RHEntry α β),
    t.slots[i]'(t.hSlotsLen ▸ hi) = some ei →
    t.slots[(i + 1) % t.capacity]'(by rw [t.hSlotsLen]; exact Nat.mod_lt _ t.hCapPos) = some ej →
    ej.dist = 0 ∨ ei.dist ≤ ej.dist

/-- Composite invariant bundle: well-formedness ∧ distance correctness ∧
    no duplicate keys ∧ Robin Hood ordering. -/
def RHTable.invariant [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.robinHoodOrdered

-- ============================================================================
-- N2-A1, B1, C1, D1: Empty Table Invariants
-- ============================================================================

/-- N2-B1: The empty table trivially satisfies distance correctness
    (no occupied slots). -/
theorem RHTable.empty_distCorrect [Hashable α] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).distCorrect := by
  intro i hi e hSlot
  simp [RHTable.empty] at hSlot

/-- N2-C1: The empty table trivially satisfies no-duplicate-keys
    (no occupied slots). -/
theorem RHTable.empty_noDupKeys [BEq α] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).noDupKeys := by
  intro i j hi hj ei ej hSlotI hSlotJ _
  simp [RHTable.empty] at hSlotI

/-- N2-D1: The empty table trivially satisfies Robin Hood ordering
    (no occupied slots). -/
theorem RHTable.empty_robinHoodOrdered (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).robinHoodOrdered := by
  intro i hi ei ej hSlotI _
  simp [RHTable.empty] at hSlotI

/-- N2-A1 + B1 + C1 + D1: The empty table satisfies the full invariant bundle. -/
theorem RHTable.empty_invariant [BEq α] [Hashable α] (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).invariant :=
  ⟨RHTable.empty_wf cap hPos,
   RHTable.empty_distCorrect cap hPos,
   RHTable.empty_noDupKeys cap hPos,
   RHTable.empty_robinHoodOrdered cap hPos⟩

end SeLe4n.Kernel.RobinHood
