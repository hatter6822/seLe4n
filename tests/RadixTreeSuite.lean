/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Kernel.RadixTree.Bridge

open SeLe4n.Kernel.RadixTree
open SeLe4n.Kernel.RobinHood
open SeLe4n.Model

namespace SeLe4n.Testing.RadixTreeSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"radix-tree check passed [{label}]"
  else
    throw <| IO.userError s!"radix-tree check failed [{label}]"

-- ============================================================================
-- Q4-T1: CNodeRadix Core Operation Tests (8 scenarios)
-- ============================================================================

/-- RT-001: Empty tree — lookup returns none, size = 0 -/
private def rt001_emptyTree : IO Unit := do
  let t := CNodeRadix.empty 4 0 3  -- guardWidth=4, guardValue=0, radixWidth=3 (8 slots)
  expect "empty lookup returns none" (t.lookup (SeLe4n.Slot.ofNat 0) == none)
  expect "empty lookup slot 5" (t.lookup (SeLe4n.Slot.ofNat 5) == none)
  expect "empty size is 0" (t.size == 0)
  expect "fanout equals 2^radixWidth" (t.fanout == 8)
  expect "slots size equals fanout" (t.slots.size == 8)

/-- RT-002: Single insert/lookup roundtrip -/
private def rt002_singleInsertLookup : IO Unit := do
  let cap : Capability := { target := .object ⟨100⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let t := (CNodeRadix.empty 0 0 4).insert (SeLe4n.Slot.ofNat 3) cap  -- radixWidth=4, 16 slots
  expect "insert then lookup" (t.lookup (SeLe4n.Slot.ofNat 3) == some cap)
  expect "size after insert" (t.size == 1)
  expect "other slot still none" (t.lookup (SeLe4n.Slot.ofNat 7) == none)

/-- RT-003: Insert then erase — lookup returns none -/
private def rt003_insertErase : IO Unit := do
  let cap : Capability := { target := .object ⟨200⟩, rights := AccessRightSet.ofList [.write], badge := none }
  let t := ((CNodeRadix.empty 0 0 3).insert (SeLe4n.Slot.ofNat 2) cap).erase (SeLe4n.Slot.ofNat 2)
  expect "erase then lookup returns none" (t.lookup (SeLe4n.Slot.ofNat 2) == none)
  expect "size after erase" (t.size == 0)

/-- RT-004: Overwrite — insert same slot twice, lookup returns latest -/
private def rt004_overwrite : IO Unit := do
  let cap1 : Capability := { target := .object ⟨10⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let cap2 : Capability := { target := .object ⟨20⟩, rights := AccessRightSet.ofList [.write], badge := none }
  let t := ((CNodeRadix.empty 0 0 3).insert (SeLe4n.Slot.ofNat 5) cap1).insert (SeLe4n.Slot.ofNat 5) cap2
  expect "overwrite returns latest" (t.lookup (SeLe4n.Slot.ofNat 5) == some cap2)
  expect "size still 1 after overwrite" (t.size == 1)

/-- RT-005: Multiple distinct slots — insert 4 slots, verify all -/
private def rt005_multipleSlots : IO Unit := do
  let mkCap (n : Nat) : Capability :=
    { target := .object ⟨n⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let t := (CNodeRadix.empty 0 0 4)
    |>.insert (SeLe4n.Slot.ofNat 0) (mkCap 0)
    |>.insert (SeLe4n.Slot.ofNat 3) (mkCap 3)
    |>.insert (SeLe4n.Slot.ofNat 7) (mkCap 7)
    |>.insert (SeLe4n.Slot.ofNat 15) (mkCap 15)
  expect "slot 0 present" (t.lookup (SeLe4n.Slot.ofNat 0) == some (mkCap 0))
  expect "slot 3 present" (t.lookup (SeLe4n.Slot.ofNat 3) == some (mkCap 3))
  expect "slot 7 present" (t.lookup (SeLe4n.Slot.ofNat 7) == some (mkCap 7))
  expect "slot 15 present" (t.lookup (SeLe4n.Slot.ofNat 15) == some (mkCap 15))
  expect "size is 4" (t.size == 4)
  expect "unoccupied slot" (t.lookup (SeLe4n.Slot.ofNat 1) == none)

/-- RT-006: Guard/radix parameter preservation across operations -/
private def rt006_parameterPreservation : IO Unit := do
  let cap : Capability := { target := .object ⟨1⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let t0 := CNodeRadix.empty 8 42 4  -- guardWidth=8, guardValue=42, radixWidth=4
  let t1 := t0.insert (SeLe4n.Slot.ofNat 5) cap
  let t2 := t1.erase (SeLe4n.Slot.ofNat 5)
  expect "insert preserves guardWidth" (t1.guardWidth == 8)
  expect "insert preserves guardValue" (t1.guardValue == 42)
  expect "insert preserves radixWidth" (t1.radixWidth == 4)
  expect "erase preserves guardWidth" (t2.guardWidth == 8)
  expect "erase preserves guardValue" (t2.guardValue == 42)
  expect "erase preserves radixWidth" (t2.radixWidth == 4)

/-- RT-007: toList completeness and noDup -/
private def rt007_toList : IO Unit := do
  let mkCap (n : Nat) : Capability :=
    { target := .object ⟨n⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let t := (CNodeRadix.empty 0 0 3)
    |>.insert (SeLe4n.Slot.ofNat 1) (mkCap 10)
    |>.insert (SeLe4n.Slot.ofNat 4) (mkCap 40)
    |>.insert (SeLe4n.Slot.ofNat 6) (mkCap 60)
  let lst := t.toList
  expect "toList length" (lst.length == 3)
  -- Verify all entries present
  let has1 := lst.any (fun ⟨s, c⟩ => s == (SeLe4n.Slot.ofNat 1) && c == mkCap 10)
  let has4 := lst.any (fun ⟨s, c⟩ => s == (SeLe4n.Slot.ofNat 4) && c == mkCap 40)
  let has6 := lst.any (fun ⟨s, c⟩ => s == (SeLe4n.Slot.ofNat 6) && c == mkCap 60)
  expect "toList contains slot 1" has1
  expect "toList contains slot 4" has4
  expect "toList contains slot 6" has6
  -- Verify no duplicate keys
  let keys := lst.map Prod.fst
  let noDup := keys.length == keys.eraseDups.length
  expect "toList no duplicate keys" noDup

/-- RT-008: Fold — sum all capability target ObjIds -/
private def rt008_fold : IO Unit := do
  let mkCap (n : Nat) : Capability :=
    { target := .object ⟨n⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let t := (CNodeRadix.empty 0 0 3)
    |>.insert (SeLe4n.Slot.ofNat 0) (mkCap 10)
    |>.insert (SeLe4n.Slot.ofNat 2) (mkCap 20)
    |>.insert (SeLe4n.Slot.ofNat 5) (mkCap 30)
  let sum := t.fold 0 fun acc _ cap =>
    match cap.target with
    | .object oid => acc + oid.toNat
    | _ => acc
  expect "fold sums correctly" (sum == 60)

-- ============================================================================
-- Q4-T2: Bridge Tests (4 scenarios)
-- ============================================================================

/-- RT-009: buildCNodeRadix from empty RHTable -/
private def rt009_buildEmpty : IO Unit := do
  let rt : RHTable SeLe4n.Slot Capability := RHTable.empty 16
  let config : CNodeConfig := { guardWidth := 0, guardValue := 0, radixWidth := 4 }
  let radix := buildCNodeRadix rt config
  expect "empty build lookup none" (radix.lookup (SeLe4n.Slot.ofNat 0) == none)
  expect "empty build size 0" (radix.size == 0)
  expect "preserves guardWidth" (radix.guardWidth == 0)
  expect "preserves radixWidth" (radix.radixWidth == 4)

/-- RT-010: buildCNodeRadix with entries -/
private def rt010_buildWithEntries : IO Unit := do
  let cap1 : Capability := { target := .object ⟨100⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let cap2 : Capability := { target := .object ⟨200⟩, rights := AccessRightSet.ofList [.write], badge := none }
  let rt := ((RHTable.empty 16 : RHTable SeLe4n.Slot Capability).insert (SeLe4n.Slot.ofNat 3) cap1).insert (SeLe4n.Slot.ofNat 7) cap2
  let config : CNodeConfig := { guardWidth := 0, guardValue := 0, radixWidth := 4 }
  let radix := buildCNodeRadix rt config
  expect "slot 3 present" (radix.lookup (SeLe4n.Slot.ofNat 3) == some cap1)
  expect "slot 7 present" (radix.lookup (SeLe4n.Slot.ofNat 7) == some cap2)
  expect "unoccupied slot" (radix.lookup (SeLe4n.Slot.ofNat 0) == none)

/-- RT-011: freezeCNodeSlots preserves parameters -/
private def rt011_freezePreservation : IO Unit := do
  let cn := CNode.empty
  let frozen := freezeCNodeSlots cn
  expect "preserves guardWidth" (frozen.guardWidth == cn.guardWidth)
  expect "preserves guardValue" (frozen.guardValue == cn.guardValue)
  expect "preserves radixWidth" (frozen.radixWidth == cn.radixWidth)

/-- RT-012: buildCNodeRadix determinism — same input, same output -/
private def rt012_determinism : IO Unit := do
  let cap : Capability := { target := .object ⟨50⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let rt := (RHTable.empty 16 : RHTable SeLe4n.Slot Capability).insert (SeLe4n.Slot.ofNat 4) cap
  let config : CNodeConfig := { guardWidth := 2, guardValue := 1, radixWidth := 3 }
  let r1 := buildCNodeRadix rt config
  let r2 := buildCNodeRadix rt config
  expect "deterministic guardWidth" (r1.guardWidth == r2.guardWidth)
  expect "deterministic radixWidth" (r1.radixWidth == r2.radixWidth)
  expect "deterministic lookup" (r1.lookup (SeLe4n.Slot.ofNat 4) == r2.lookup (SeLe4n.Slot.ofNat 4))

-- ============================================================================
-- Runner
-- ============================================================================

private def runRadixTreeSuite : IO Unit := do
  IO.println "=== CNode Radix Tree Test Suite (WS-Q4) ==="
  IO.println ""
  IO.println "--- Core Operation Tests (RT-001 to RT-008) ---"
  rt001_emptyTree
  rt002_singleInsertLookup
  rt003_insertErase
  rt004_overwrite
  rt005_multipleSlots
  rt006_parameterPreservation
  rt007_toList
  rt008_fold
  IO.println ""
  IO.println "--- Bridge Tests (RT-009 to RT-012) ---"
  rt009_buildEmpty
  rt010_buildWithEntries
  rt011_freezePreservation
  rt012_determinism
  IO.println ""
  IO.println "=== All Radix Tree tests passed ==="

end SeLe4n.Testing.RadixTreeSuite

def main : IO Unit :=
  SeLe4n.Testing.RadixTreeSuite.runRadixTreeSuite
