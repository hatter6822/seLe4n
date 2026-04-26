-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.Types

/-!
# Q4-A/B: CNode Radix Tree — Core Types and Operations

Verified flat radix tree for CNode capability slots. Each CNode has a single
radix level with `2^radixWidth` entries, addressed by bit extraction from the
slot index. Lookup is O(1) with zero hashing — pure bitwise index computation.

This replaces `RHTable Slot Capability` in the frozen execution phase,
providing deterministic memory layout and zero-hash lookup.
-/

namespace SeLe4n.Kernel.RadixTree

open SeLe4n.Model

-- ============================================================================
-- Q4-A1: Bit Extraction Helper
-- ============================================================================

/-- Extract `width` bits starting at bit position `offset` from `n`.
Returns a value in `[0, 2^width)`. When `width = 0`, returns `0`.
AJ-L16: The `offset` parameter is more general than current callers require
(all pass `offset = 0`). This generality is harmless and costs nothing at
runtime; it avoids a future breaking change if multi-level radix trees are
introduced. No action required. -/
@[inline] def extractBits (n : Nat) (offset : Nat) (width : Nat) : Nat :=
  (n >>> offset) % (2 ^ width)

/-- `extractBits` always produces a value less than `2^width`. -/
theorem extractBits_lt (n offset width : Nat) :
    extractBits n offset width < 2 ^ width := by
  unfold extractBits
  exact Nat.mod_lt _ (Nat.two_pow_pos width)

/-- V3-H: `extractBits n 0 w = n` when `n < 2^w`. The zero-offset extraction
    is the identity on bounded values. This closes the hNoPhantom discharge
    chain: bounded slot keys have identity radix indices, so distinct keys
    map to distinct radix positions. -/
theorem extractBits_identity (n w : Nat) (h : n < 2 ^ w) :
    extractBits n 0 w = n := by
  unfold extractBits
  simp [Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt h

-- ============================================================================
-- Q4-A2: CNodeRadix — Flat Radix Array for CNode Slots
-- ============================================================================

/-- Flat radix array for CNode capability slots.

Each entry corresponds to a slot index in `[0, 2^radixWidth)`. Lookup is O(1)
via direct array indexing after bit extraction — no hashing required.

Fields:
- `guardWidth`: width of the guard field in bits
- `guardValue`: expected guard value for traversal authorization
- `radixWidth`: width of the radix field in bits (determines fanout)
- `slots`: fixed-size array of `2^radixWidth` optional capabilities
- `hSlotSize`: proof that the array size equals `2^radixWidth` -/
structure CNodeRadix where
  guardWidth : Nat
  guardValue : Nat
  radixWidth : Nat
  slots      : Array (Option Capability)
  hSlotSize  : slots.size = 2 ^ radixWidth

instance : Repr CNodeRadix where
  reprPrec r _ :=
    f!"CNodeRadix(guard={r.guardValue}/{r.guardWidth}, radix={r.radixWidth}, slots={r.slots.size})"

-- ============================================================================
-- Q4-B1: Construction
-- ============================================================================

/-- Create an empty CNodeRadix with the given guard and radix parameters.
All slots initialized to `none`. -/
def CNodeRadix.empty (guardWidth guardValue radixWidth : Nat) : CNodeRadix :=
  { guardWidth := guardWidth
    guardValue := guardValue
    radixWidth := radixWidth
    slots      := ⟨List.replicate (2 ^ radixWidth) none⟩
    hSlotSize  := by simp [Array.size] }

-- ============================================================================
-- Q4-B2: Lookup — O(1), Zero Hashing
-- ============================================================================

/-- O(1) lookup: extract radix bits from slot index, use as direct array index.
Returns `none` if the slot is unoccupied. -/
def CNodeRadix.lookup (tree : CNodeRadix) (slot : SeLe4n.Slot) : Option Capability :=
  let idx := extractBits slot.toNat 0 tree.radixWidth
  have hBound : idx < tree.slots.size := by
    rw [tree.hSlotSize]; exact extractBits_lt _ _ _
  tree.slots[idx]

-- ============================================================================
-- Q4-B3: Insert — O(1)
-- ============================================================================

/-- O(1) insert: set the slot at the radix-indexed position. -/
def CNodeRadix.insert (tree : CNodeRadix) (slot : SeLe4n.Slot)
    (cap : Capability) : CNodeRadix :=
  let idx := extractBits slot.toNat 0 tree.radixWidth
  have hBound : idx < tree.slots.size := by
    rw [tree.hSlotSize]; exact extractBits_lt _ _ _
  { tree with
    slots := tree.slots.set idx (some cap)
    hSlotSize := by rw [Array.size_set]; exact tree.hSlotSize }

-- ============================================================================
-- Q4-B4: Erase — O(1)
-- ============================================================================

/-- O(1) erase: set the slot at the radix-indexed position to `none`. -/
def CNodeRadix.erase (tree : CNodeRadix) (slot : SeLe4n.Slot) : CNodeRadix :=
  let idx := extractBits slot.toNat 0 tree.radixWidth
  have hBound : idx < tree.slots.size := by
    rw [tree.hSlotSize]; exact extractBits_lt _ _ _
  { tree with
    slots := tree.slots.set idx none
    hSlotSize := by rw [Array.size_set]; exact tree.hSlotSize }

-- ============================================================================
-- Q4-B5: Fold — O(2^radixWidth)
-- ============================================================================

/-- Fold over all occupied slots, applying `f` to accumulator, slot index, and
capability for each occupied entry. -/
def CNodeRadix.fold (tree : CNodeRadix) (init : β)
    (f : β → SeLe4n.Slot → Capability → β) : β :=
  tree.slots.foldl (init := (init, 0)) (fun (acc, i) entry =>
    match entry with
    | none => (acc, i + 1)
    | some cap => (f acc (SeLe4n.Slot.ofNat i) cap, i + 1)) |>.1

-- ============================================================================
-- Q4-B6: toList — O(2^radixWidth)
-- ============================================================================

/-- Collect all occupied slots as a list of `(Slot, Capability)` pairs.
V7-G: O(n) via cons-accumulate + reverse, replacing O(n²) append. -/
def CNodeRadix.toList (tree : CNodeRadix) : List (SeLe4n.Slot × Capability) :=
  (tree.fold [] (fun acc slot cap => (slot, cap) :: acc)).reverse

-- ============================================================================
-- Q4-B7: Size — O(2^radixWidth)
-- ============================================================================

/-- Count occupied slots. -/
def CNodeRadix.size (tree : CNodeRadix) : Nat :=
  tree.slots.foldl (init := 0) (fun acc entry =>
    match entry with
    | none => acc
    | some _ => acc + 1)

-- ============================================================================
-- Q4-B8: Fanout
-- ============================================================================

/-- Total number of addressable slots (2^radixWidth). -/
def CNodeRadix.fanout (tree : CNodeRadix) : Nat :=
  2 ^ tree.radixWidth

end SeLe4n.Kernel.RadixTree
