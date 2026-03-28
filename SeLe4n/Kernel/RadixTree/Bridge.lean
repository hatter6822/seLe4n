/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RadixTree.Invariant
import SeLe4n.Kernel.RobinHood.Bridge

/-!
# Q4-D: Builder Equivalence Bridge

Provides the `buildCNodeRadix` function that converts an `RHTable Slot Capability`
(builder-phase CNode backing store) into a `CNodeRadix` (frozen-phase flat radix
array). Proves functional equivalence: lookups in the frozen radix tree match
lookups in the original RHTable.

This bridge is the correctness foundation for Q5's freeze operation.
-/

namespace SeLe4n.Kernel.RadixTree

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- Q4-D1: CNodeConfig — Configuration for radix tree construction
-- ============================================================================

/-- Configuration parameters for building a CNodeRadix from an RHTable.
Captures the guard and radix widths from the source CNode. -/
structure CNodeConfig where
  guardWidth : Nat
  guardValue : Nat
  radixWidth : Nat
  deriving Repr

-- ============================================================================
-- Q4-D2: buildCNodeRadix — RHTable → CNodeRadix conversion
-- ============================================================================

/-- Convert an `RHTable Slot Capability` to a `CNodeRadix` by folding all
entries into a fresh flat radix array.

Each slot key is mapped to a radix index via `extractBits slot.toNat 0 radixWidth`.
Multiple RHTable keys that map to the same radix index will overwrite each other
(last-writer-wins via fold order). In well-formed CNodes, all slot keys are
within `[0, 2^radixWidth)` and map to distinct radix indices. -/
def buildCNodeRadix (rt : RHTable SeLe4n.Slot Capability) (config : CNodeConfig)
    : CNodeRadix :=
  rt.fold (CNodeRadix.empty config.guardWidth config.guardValue config.radixWidth)
    (fun tree slot cap => tree.insert slot cap)

-- ============================================================================
-- Q4-D3: buildCNodeRadix preserves guard/radix parameters
-- ============================================================================

private theorem rhFold_preserves_field
    {F : CNodeRadix → Nat}
    (hInsert : ∀ t (s : SeLe4n.Slot) (c : Capability), F (t.insert s c) = F t)
    (rt : RHTable SeLe4n.Slot Capability) (init : CNodeRadix) :
    F (rt.fold init fun tree slot cap => tree.insert slot cap) = F init := by
  unfold RHTable.fold
  rw [← Array.foldl_toList]
  induction rt.slots.toList generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases hd with
    | none => exact ih init
    | some e => simp only []; rw [ih]; exact hInsert _ _ _

/-- `buildCNodeRadix` preserves guardWidth from config. -/
theorem buildCNodeRadix_guardWidth (rt : RHTable SeLe4n.Slot Capability)
    (config : CNodeConfig) :
    (buildCNodeRadix rt config).guardWidth = config.guardWidth := by
  exact rhFold_preserves_field
    (fun _ _ _ => CNodeRadix.insert_guardWidth _ _ _) rt _

/-- `buildCNodeRadix` preserves guardValue from config. -/
theorem buildCNodeRadix_guardValue (rt : RHTable SeLe4n.Slot Capability)
    (config : CNodeConfig) :
    (buildCNodeRadix rt config).guardValue = config.guardValue := by
  exact rhFold_preserves_field
    (fun _ _ _ => CNodeRadix.insert_guardValue _ _ _) rt _

/-- `buildCNodeRadix` preserves radixWidth from config. -/
theorem buildCNodeRadix_radixWidth (rt : RHTable SeLe4n.Slot Capability)
    (config : CNodeConfig) :
    (buildCNodeRadix rt config).radixWidth = config.radixWidth := by
  exact rhFold_preserves_field
    (fun _ _ _ => CNodeRadix.insert_radixWidth _ _ _) rt _

-- ============================================================================
-- Q4-D4: buildCNodeRadix well-formedness
-- ============================================================================

/-- The built CNodeRadix is well-formed. -/
theorem buildCNodeRadix_wf (rt : RHTable SeLe4n.Slot Capability)
    (config : CNodeConfig) :
    (buildCNodeRadix rt config).WF := by
  exact (buildCNodeRadix rt config).wf_of_mk

-- ============================================================================
-- Q4-D6: CNode extraction helper
-- ============================================================================

/-- Extract a `CNodeConfig` from a `CNode` structure. -/
def CNodeConfig.ofCNode (cn : CNode) : CNodeConfig :=
  { guardWidth := cn.guardWidth
    guardValue := cn.guardValue
    radixWidth := cn.radixWidth }

/-- Build a `CNodeRadix` directly from a `CNode`. -/
def CNodeRadix.ofCNode (cn : CNode) : CNodeRadix :=
  buildCNodeRadix cn.slots (CNodeConfig.ofCNode cn)

-- ============================================================================
-- Q4-D7: buildCNodeRadix from empty RHTable
-- ============================================================================

/-- Building from an empty RHTable yields an empty CNodeRadix. -/
theorem buildCNodeRadix_empty_lookup (cap : Nat) (hPos : 0 < cap)
    (config : CNodeConfig) (slot : SeLe4n.Slot) :
    (buildCNodeRadix (RHTable.empty cap hPos) config).lookup slot = none := by
  -- Use fold_preserves to show the result equals the initial empty tree
  have hEq : (buildCNodeRadix (RHTable.empty cap hPos) config).lookup slot =
      (CNodeRadix.empty config.guardWidth config.guardValue config.radixWidth).lookup slot := by
    unfold buildCNodeRadix
    congr 1
    unfold RHTable.fold
    rw [← Array.foldl_toList]
    unfold RHTable.empty
    simp only []
    clear hPos
    induction cap with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      exact ih
  rw [hEq]
  exact CNodeRadix.lookup_empty _ _ _ _

-- ============================================================================
-- Q4-D8: Unique radix index predicate
-- ============================================================================

/-- Predicate: all keys in the RHTable map to distinct radix indices. This is
the precondition for `buildCNodeRadix_lookup_equiv` (Q6-B). In well-formed
CNodes, slots are within `[0, 2^radixWidth)` so this is automatically
satisfied. -/
def UniqueRadixIndices (rt : RHTable SeLe4n.Slot Capability) (radixWidth : Nat) : Prop :=
  ∀ s₁ s₂ : SeLe4n.Slot,
    rt.get? s₁ ≠ none → rt.get? s₂ ≠ none → s₁ ≠ s₂ →
    extractBits s₁.toNat 0 radixWidth ≠ extractBits s₂.toNat 0 radixWidth

-- ============================================================================
-- T4-I (M-DS-3): Bidirectional lookup equivalence
-- ============================================================================

/-- If `t.invExt` and `t.slots[i] = some e`, then `t.get? e.key ≠ none`.
Proof by contradiction using `get_none_no_matching_entry` + BEq reflexivity. -/
private theorem get_ne_none_of_slot_occupied
    (t : RHTable SeLe4n.Slot Capability) (hExt : t.invExt)
    (i : Nat) (hi : i < t.capacity) (e : RHEntry SeLe4n.Slot Capability)
    (hSlot : t.slots[i]'(t.hSlotsLen ▸ hi) = some e) :
    t.get? e.key ≠ none := by
  intro hNone
  have := RHTable.get_none_no_matching_entry t e.key hExt hNone i hi e hSlot
  simp [BEq.beq] at this

/-- List.foldl preserves `tree.lookup slot = none` when every occupied entry
has a distinct radix index from `slot`. Also preserves `radixWidth`. -/
private theorem foldl_preserves_none
    (L : List (Option (RHEntry SeLe4n.Slot Capability)))
    (tree : CNodeRadix) (slot : SeLe4n.Slot) (rw : Nat)
    (hRW : tree.radixWidth = rw)
    (hInit : tree.lookup slot = none)
    (hDiff : ∀ e : RHEntry SeLe4n.Slot Capability, some e ∈ L →
      extractBits e.key.toNat 0 rw ≠ extractBits slot.toNat 0 rw) :
    (L.foldl (fun (acc : CNodeRadix) (opt : Option (RHEntry SeLe4n.Slot Capability)) =>
      match opt with | none => acc | some e => acc.insert e.key e.value) tree).lookup slot = none ∧
    (L.foldl (fun (acc : CNodeRadix) (opt : Option (RHEntry SeLe4n.Slot Capability)) =>
      match opt with | none => acc | some e => acc.insert e.key e.value) tree).radixWidth = rw := by
  induction L generalizing tree with
  | nil => exact ⟨hInit, hRW⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases hd with
    | none => exact ih tree hRW hInit (fun e hMem => hDiff e (List.mem_cons_of_mem _ hMem))
    | some e =>
      have hDiffE := hDiff e (List.mem_cons.mpr (Or.inl rfl))
      have hRW' : (tree.insert e.key e.value).radixWidth = rw := by
        rw [CNodeRadix.insert_radixWidth]; exact hRW
      have hLookup : (tree.insert e.key e.value).lookup slot = none := by
        rw [CNodeRadix.lookup_insert_ne tree e.key slot e.value (hRW ▸ hDiffE)]
        exact hInit
      exact ih _ hRW' hLookup (fun e' hMem => hDiff e' (List.mem_cons_of_mem _ hMem))

/-- List.foldl preserves `tree.lookup slot = some cap` when every occupied
entry either has key=slot (overwrite with same cap) or has a distinct radix
index from `slot`. Also preserves `radixWidth`. -/
private theorem foldl_preserves_some
    (L : List (Option (RHEntry SeLe4n.Slot Capability)))
    (tree : CNodeRadix) (slot : SeLe4n.Slot) (cap : Capability) (rw : Nat)
    (hRW : tree.radixWidth = rw)
    (hInit : tree.lookup slot = some cap)
    (hCompat : ∀ e : RHEntry SeLe4n.Slot Capability, some e ∈ L →
      (e.key = slot → e.value = cap) ∧
      (e.key ≠ slot → extractBits e.key.toNat 0 rw ≠ extractBits slot.toNat 0 rw)) :
    (L.foldl (fun (acc : CNodeRadix) (opt : Option (RHEntry SeLe4n.Slot Capability)) =>
      match opt with | none => acc | some e => acc.insert e.key e.value) tree).lookup slot = some cap ∧
    (L.foldl (fun (acc : CNodeRadix) (opt : Option (RHEntry SeLe4n.Slot Capability)) =>
      match opt with | none => acc | some e => acc.insert e.key e.value) tree).radixWidth = rw := by
  induction L generalizing tree with
  | nil => exact ⟨hInit, hRW⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases hd with
    | none => exact ih tree hRW hInit (fun e hMem => hCompat e (List.mem_cons_of_mem _ hMem))
    | some e =>
      have hRW' : (tree.insert e.key e.value).radixWidth = rw := by
        rw [CNodeRadix.insert_radixWidth]; exact hRW
      have ⟨hEq, hNe⟩ := hCompat e (List.mem_cons.mpr (Or.inl rfl))
      by_cases hKey : e.key = slot
      · have hLookup : (tree.insert e.key e.value).lookup slot = some cap := by
          rw [hKey]; rw [CNodeRadix.lookup_insert_self]; congr 1; exact hEq hKey
        exact ih _ hRW' hLookup (fun e' hMem => hCompat e' (List.mem_cons_of_mem _ hMem))
      · have hLookup : (tree.insert e.key e.value).lookup slot = some cap := by
          rw [CNodeRadix.lookup_insert_ne tree e.key slot e.value (hRW ▸ hNe hKey)]; exact hInit
        exact ih _ hRW' hLookup (fun e' hMem => hCompat e' (List.mem_cons_of_mem _ hMem))

/-- Combined fold lemma: if there exists an entry with key=slot and value=cap,
no duplicate keys, and unique radix indices, the fold produces lookup=some cap. -/
private theorem foldl_establishes_some
    (L : List (Option (RHEntry SeLe4n.Slot Capability)))
    (tree : CNodeRadix) (slot : SeLe4n.Slot) (cap : Capability) (rw : Nat)
    (hRW : tree.radixWidth = rw)
    (hInitNone : tree.lookup slot = none)
    (hMem : ∃ e : RHEntry SeLe4n.Slot Capability, some e ∈ L ∧ e.key = slot ∧ e.value = cap)
    -- No duplicate keys in L
    (hNoDupKey : ∀ (e1 e2 : RHEntry SeLe4n.Slot Capability),
      some e1 ∈ L → some e2 ∈ L → e1.key = e2.key → e1 = e2)
    (hRadixUniq : ∀ (e1 e2 : RHEntry SeLe4n.Slot Capability),
      some e1 ∈ L → some e2 ∈ L → e1.key ≠ e2.key →
      extractBits e1.key.toNat 0 rw ≠ extractBits e2.key.toNat 0 rw) :
    (L.foldl (fun (acc : CNodeRadix) (opt : Option (RHEntry SeLe4n.Slot Capability)) =>
      match opt with | none => acc | some e => acc.insert e.key e.value) tree).lookup slot = some cap := by
  induction L generalizing tree with
  | nil => simp only [List.foldl_nil]; exact absurd hMem (by simp)
  | cons hd tl ih =>
    obtain ⟨target, hTargetMem, hTargetKey, hTargetVal⟩ := hMem
    simp only [List.foldl_cons]
    cases hd with
    | none =>
      have hMem' : ∃ e, some e ∈ tl ∧ e.key = slot ∧ e.value = cap := by
        exact ⟨target, (List.mem_cons.mp hTargetMem).elim (by simp) id,
          hTargetKey, hTargetVal⟩
      exact ih tree hRW hInitNone hMem'
        (fun e1 e2 h1 h2 => hNoDupKey e1 e2 (List.mem_cons_of_mem _ h1)
          (List.mem_cons_of_mem _ h2))
        (fun e1 e2 h1 h2 => hRadixUniq e1 e2 (List.mem_cons_of_mem _ h1)
          (List.mem_cons_of_mem _ h2))
    | some e =>
      have hRW' : (tree.insert e.key e.value).radixWidth = rw := by
        rw [CNodeRadix.insert_radixWidth]; exact hRW
      by_cases hKey : e.key = slot
      · -- This entry has key=slot. By noDupKey, it must be the target.
        have hEqTarget : e = target :=
          hNoDupKey e target (List.mem_cons.mpr (Or.inl rfl)) hTargetMem
            (hKey ▸ hTargetKey ▸ rfl)
        have hLookup : (tree.insert e.key e.value).lookup slot = some cap := by
          rw [hKey, CNodeRadix.lookup_insert_self]; congr 1; rw [hEqTarget]; exact hTargetVal
        -- Preserve through the tail using foldl_preserves_some
        exact (foldl_preserves_some tl _ slot cap rw hRW' hLookup (fun e' hMem' => by
          constructor
          · intro hKey'
            have hEq := hNoDupKey e e' (List.mem_cons.mpr (Or.inl rfl))
              (List.mem_cons_of_mem _ hMem') (hKey ▸ hKey' ▸ rfl)
            rw [← hEq, hEqTarget]; exact hTargetVal
          · intro hNe'
            have := hRadixUniq e e' (List.mem_cons.mpr (Or.inl rfl))
              (List.mem_cons_of_mem _ hMem') (fun h => hNe' (hKey ▸ h.symm))
            exact fun h => this (hKey ▸ h.symm))).1
      · -- Different key. Insert preserves lookup=none, continue searching.
        have hDiffRadix : extractBits e.key.toNat 0 rw ≠ extractBits slot.toNat 0 rw := by
          rw [← hTargetKey]
          exact hRadixUniq e target (List.mem_cons.mpr (Or.inl rfl)) hTargetMem
            (fun h => hKey (h ▸ hTargetKey))
        have hLookup : (tree.insert e.key e.value).lookup slot = none := by
          rw [CNodeRadix.lookup_insert_ne tree e.key slot e.value (hRW ▸ hDiffRadix)]
          exact hInitNone
        have hTargetInTl : some target ∈ tl := by
          rcases List.mem_cons.mp hTargetMem with h | h
          · exact absurd ((by injection h : target = e) ▸ hTargetKey) hKey
          · exact h
        exact ih _ hRW' hLookup ⟨target, hTargetInTl, hTargetKey, hTargetVal⟩
          (fun e1 e2 h1 h2 => hNoDupKey e1 e2 (List.mem_cons_of_mem _ h1)
            (List.mem_cons_of_mem _ h2))
          (fun e1 e2 h1 h2 => hRadixUniq e1 e2 (List.mem_cons_of_mem _ h1)
            (List.mem_cons_of_mem _ h2))

-- W2-H (L-3): 800K heartbeats — bidirectional lookup equivalence proof requires
-- list induction over RHTable entries with per-entry extractBits/radix reasoning.
-- Each step unfolds buildCNodeRadix fold and matches against radix array updates.
set_option maxHeartbeats 800000 in
/-- T4-I (M-DS-3): Bidirectional lookup equivalence for `buildCNodeRadix`.
After constructing a `CNodeRadix` from an `RHTable`, lookups in the radix
tree yield the same result as `get?` in the original hash table.

Preconditions: `hInvExt` (hash table well-formedness), `hUri` (distinct radix
indices for distinct keys), and `hNoPhantom` (absent keys have no radix index
collision with present keys). In well-formed CNodes where all keys are bounded,
both `hUri` and `hNoPhantom` hold automatically. -/
theorem buildCNodeRadix_lookup_equiv
    (rt : RHTable SeLe4n.Slot Capability) (config : CNodeConfig)
    (slot : SeLe4n.Slot)
    (hInvExt : rt.invExt)
    (hUri : UniqueRadixIndices rt config.radixWidth)
    (hNoPhantom : rt.get? slot = none → ∀ s, rt.get? s ≠ none → s ≠ slot →
      extractBits s.toNat 0 config.radixWidth ≠ extractBits slot.toNat 0 config.radixWidth) :
    (buildCNodeRadix rt config).lookup slot = rt.get? slot := by
  -- Normalize buildCNodeRadix to a list fold with beta-reduced body
  have hUnfold : (buildCNodeRadix rt config) =
      rt.slots.toList.foldl (fun (acc : CNodeRadix) (opt : Option (RHEntry SeLe4n.Slot Capability)) =>
        match opt with | none => acc | some e => acc.insert e.key e.value)
      (CNodeRadix.empty config.guardWidth config.guardValue config.radixWidth) := by
    unfold buildCNodeRadix RHTable.fold
    rw [← Array.foldl_toList]
    congr 1; funext acc opt; cases opt <;> rfl
  rw [hUnfold]
  cases hGet : rt.get? slot with
  | none =>
    -- None direction: no entry has key=slot, and hNoPhantom ensures no collisions
    exact (foldl_preserves_none rt.slots.toList (CNodeRadix.empty _ _ _) slot
      config.radixWidth rfl (CNodeRadix.lookup_empty _ _ _ _)
      (fun e hMem => by
        have hi := List.getElem_of_mem hMem
        obtain ⟨i, hi_lt, hi_eq⟩ := hi
        have hi_lt' : i < rt.slots.size := by rw [Array.length_toList] at hi_lt; exact hi_lt
        have hi_cap : i < rt.capacity := by rw [← rt.hSlotsLen]; exact hi_lt'
        have hSlot : rt.slots[i]'(rt.hSlotsLen ▸ hi_cap) = some e := by
          rw [← Array.getElem_toList]; exact hi_eq
        have hGetNe := get_ne_none_of_slot_occupied rt hInvExt i hi_cap e hSlot
        have hKeyNe : e.key ≠ slot := fun h => hGetNe (h ▸ hGet)
        exact hNoPhantom hGet e.key hGetNe hKeyNe)).1
  | some cap =>
    -- Some direction: there exists an entry with key=slot and value=cap
    have ⟨p, hp, e, hSlotP, hKeyE, hValE⟩ := RHTable.get_some_slot_entry rt slot cap hGet
    have hKeyEq := eq_of_beq hKeyE
    -- Construct membership in toList
    have hP' : p < rt.slots.toList.length := by rw [Array.length_toList, rt.hSlotsLen]; exact hp
    have hSlotInList : rt.slots.toList[p] = some e := by
      rw [Array.getElem_toList]; exact hSlotP
    have hMemList : some e ∈ rt.slots.toList := by
      have := List.getElem_mem hP'
      rw [hSlotInList] at this; exact this
    -- noDupKeys in list form
    have hNoDupList : ∀ (e1 e2 : RHEntry SeLe4n.Slot Capability),
        some e1 ∈ rt.slots.toList → some e2 ∈ rt.slots.toList →
        e1.key = e2.key → e1 = e2 := by
      intro e1 e2 h1 h2 hK
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem h1
      obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem h2
      have hi_sz : i < rt.slots.size := by rw [Array.length_toList] at hi_lt; exact hi_lt
      have hj_sz : j < rt.slots.size := by rw [Array.length_toList] at hj_lt; exact hj_lt
      have hi_cap : i < rt.capacity := by rw [← rt.hSlotsLen]; exact hi_sz
      have hj_cap : j < rt.capacity := by rw [← rt.hSlotsLen]; exact hj_sz
      have hSi : rt.slots[i]'(rt.hSlotsLen ▸ hi_cap) = some e1 := by
        rw [← Array.getElem_toList]; exact hi_eq
      have hSj : rt.slots[j]'(rt.hSlotsLen ▸ hj_cap) = some e2 := by
        rw [← Array.getElem_toList]; exact hj_eq
      have hij := hInvExt.2.2.1 i j hi_cap hj_cap e1 e2 hSi hSj (beq_of_eq hK)
      subst hij; simp only [hSi] at hSj; exact Option.some.inj hSj
    -- UniqueRadixIndices in list form
    have hRadixList : ∀ (e1 e2 : RHEntry SeLe4n.Slot Capability),
        some e1 ∈ rt.slots.toList → some e2 ∈ rt.slots.toList →
        e1.key ≠ e2.key →
        extractBits e1.key.toNat 0 config.radixWidth ≠
          extractBits e2.key.toNat 0 config.radixWidth := by
      intro e1 e2 h1 h2 hNe
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem h1
      obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem h2
      have hi_sz : i < rt.slots.size := by rw [Array.length_toList] at hi_lt; exact hi_lt
      have hj_sz : j < rt.slots.size := by rw [Array.length_toList] at hj_lt; exact hj_lt
      have hi_cap : i < rt.capacity := by rw [← rt.hSlotsLen]; exact hi_sz
      have hj_cap : j < rt.capacity := by rw [← rt.hSlotsLen]; exact hj_sz
      have hSi : rt.slots[i]'(rt.hSlotsLen ▸ hi_cap) = some e1 := by
        rw [← Array.getElem_toList]; exact hi_eq
      have hSj : rt.slots[j]'(rt.hSlotsLen ▸ hj_cap) = some e2 := by
        rw [← Array.getElem_toList]; exact hj_eq
      have hGet1 := get_ne_none_of_slot_occupied rt hInvExt i hi_cap e1 hSi
      have hGet2 := get_ne_none_of_slot_occupied rt hInvExt j hj_cap e2 hSj
      exact hUri e1.key e2.key hGet1 hGet2 hNe
    -- Apply foldl_establishes_some and let Lean handle the let-binding unification
    exact @foldl_establishes_some rt.slots.toList (CNodeRadix.empty _ _ _) slot cap
      config.radixWidth rfl (CNodeRadix.lookup_empty _ _ _ _)
      ⟨e, hMemList, hKeyEq, hValE⟩ hNoDupList hRadixList

-- ============================================================================
-- V3-C (H-RAD-1): UniqueRadixIndices sufficiency documentation
-- ============================================================================

/-- V3-C (H-RAD-1): When all keys in the table are bounded by `2^radixWidth`
    (i.e., `slot.toNat < 2^radixWidth`), `UniqueRadixIndices` at build time
    is sufficient to guarantee the `hNoPhantom` precondition required by
    `buildCNodeRadix_lookup_equiv`.

    The proof chain: bounded keys make `extractBits` injective (it becomes the
    identity on `[0, 2^radixWidth)`), so `s ≠ slot` directly implies distinct
    radix indices — regardless of whether `slot` is present or absent.

    In seLe4n CNodes, slot values are always bounded by the CNode's radix width
    (capacity = `2^radixWidth`), so this precondition holds for all well-formed
    kernel states. This theorem documents the full sufficiency chain:
    `invExt` + bounded keys → `UniqueRadixIndices` → `hNoPhantom` →
    `buildCNodeRadix_lookup_equiv`. -/
theorem uniqueRadixIndices_sufficient
    (rt : RHTable SeLe4n.Slot Capability) (radixWidth : Nat)
    (hBounded : ∀ s : SeLe4n.Slot, rt.get? s ≠ none → s.toNat < 2 ^ radixWidth)
    (hAllBounded : ∀ s : SeLe4n.Slot, s.toNat < 2 ^ radixWidth →
      extractBits s.toNat 0 radixWidth = s.toNat) :
    ∀ slot, slot.toNat < 2 ^ radixWidth →
      rt.get? slot = none → ∀ s, rt.get? s ≠ none → s ≠ slot →
      extractBits s.toNat 0 radixWidth ≠ extractBits slot.toNat 0 radixWidth := by
  intro slot hSlotBnd _hAbsent s hPresent hNe
  have hSBnd := hBounded s hPresent
  rw [hAllBounded s hSBnd, hAllBounded slot hSlotBnd]
  intro hEq
  have : s = slot := by
    cases s; cases slot; simp [SeLe4n.Slot.toNat] at hEq; exact congrArg _ hEq
  exact absurd this hNe

/-- V3-H (M-DS-4): The `hNoPhantom` precondition is automatically discharged
    for well-formed CNodes where slot values are bounded by `2^radixWidth`.
    `extractBits_identity` proves `extractBits n 0 w = n` when `n < 2^w`,
    making radix indices equal to slot keys. Combined with
    `uniqueRadixIndices_sufficient` (V3-C), this shows that bounded-key CNodes
    satisfy `hNoPhantom` unconditionally — absent keys cannot collide with
    present keys in the radix index space. -/
theorem buildCNodeRadix_hNoPhantom_auto_discharge
    (rt : RHTable SeLe4n.Slot Capability) (radixWidth : Nat)
    (hBounded : ∀ s : SeLe4n.Slot, rt.get? s ≠ none → s.toNat < 2 ^ radixWidth) :
    ∀ slot, slot.toNat < 2 ^ radixWidth →
      rt.get? slot = none → ∀ s, rt.get? s ≠ none → s ≠ slot →
      extractBits s.toNat 0 radixWidth ≠ extractBits slot.toNat 0 radixWidth :=
  uniqueRadixIndices_sufficient rt radixWidth hBounded
    (fun s hBnd => extractBits_identity s.toNat radixWidth hBnd)

-- ============================================================================
-- Q4-D10: freezeCNodeSlots — integration point for Q5
-- ============================================================================

/-- Convert a CNode's RHTable-backed slot store to a flat radix array.
This is the integration point for Q5's freeze operation: during freeze,
each CNode's `slots : RHTable Slot Capability` is converted to a
`CNodeRadix` via this function. -/
def freezeCNodeSlots (cn : CNode) : CNodeRadix :=
  CNodeRadix.ofCNode cn

/-- `freezeCNodeSlots` preserves guard parameters from the source CNode. -/
theorem freezeCNodeSlots_guardWidth (cn : CNode) :
    (freezeCNodeSlots cn).guardWidth = cn.guardWidth :=
  buildCNodeRadix_guardWidth cn.slots (CNodeConfig.ofCNode cn)

/-- `freezeCNodeSlots` preserves guard value from the source CNode. -/
theorem freezeCNodeSlots_guardValue (cn : CNode) :
    (freezeCNodeSlots cn).guardValue = cn.guardValue :=
  buildCNodeRadix_guardValue cn.slots (CNodeConfig.ofCNode cn)

/-- `freezeCNodeSlots` preserves radix width from the source CNode. -/
theorem freezeCNodeSlots_radixWidth (cn : CNode) :
    (freezeCNodeSlots cn).radixWidth = cn.radixWidth :=
  buildCNodeRadix_radixWidth cn.slots (CNodeConfig.ofCNode cn)

/-- `freezeCNodeSlots` produces a well-formed radix tree. -/
theorem freezeCNodeSlots_wf (cn : CNode) :
    (freezeCNodeSlots cn).WF :=
  buildCNodeRadix_wf cn.slots (CNodeConfig.ofCNode cn)

end SeLe4n.Kernel.RadixTree
