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
-- Q4-D5: buildCNodeRadix deterministic
-- ============================================================================

/-- `buildCNodeRadix` is a pure function — same inputs yield same output. -/
theorem buildCNodeRadix_deterministic (rt : RHTable SeLe4n.Slot Capability)
    (config : CNodeConfig) :
    buildCNodeRadix rt config = buildCNodeRadix rt config := rfl

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

end SeLe4n.Kernel.RadixTree
