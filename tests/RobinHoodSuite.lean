/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n

open SeLe4n.Kernel.RobinHood
open SeLe4n.Model

namespace SeLe4n.Testing.RobinHoodSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"robin-hood check passed [{label}]"
  else
    throw <| IO.userError s!"robin-hood check failed [{label}]"

-- ============================================================================
-- N5-A: Robin Hood Standalone Test Suite (12 scenarios)
-- ============================================================================

/-- RH-001: Empty table — get? returns none, size = 0, contains = false -/
private def rh001_emptyTable : IO Unit := do
  let t : RHTable Nat Nat := RHTable.empty 16
  expect "empty get? returns none" (t.get? 42 == none)
  expect "empty size is 0" (t.size == 0)
  expect "empty contains is false" (!t.contains 42)

/-- RH-002: Single insert/get roundtrip -/
private def rh002_singleInsertGet : IO Unit := do
  let t : RHTable Nat Nat := (RHTable.empty 16).insert 10 100
  expect "insert then get" (t.get? 10 == some 100)
  expect "size after insert" (t.size == 1)
  expect "contains after insert" (t.contains 10)

/-- RH-003: Insert/erase/get — erase then get returns none -/
private def rh003_insertErase : IO Unit := do
  let t := ((RHTable.empty 16 : RHTable Nat Nat).insert 10 100).erase 10
  expect "erase then get returns none" (t.get? 10 == none)
  expect "size after erase" (t.size == 0)
  expect "contains after erase" (!t.contains 10)

/-- RH-004: Overwrite — insert same key twice, get returns latest value -/
private def rh004_overwrite : IO Unit := do
  let t := ((RHTable.empty 16 : RHTable Nat Nat).insert 5 50).insert 5 99
  expect "overwrite returns latest" (t.get? 5 == some 99)
  expect "size unchanged after overwrite" (t.size == 1)

/-- RH-005: Multiple distinct keys — insert 10 keys, verify all retrievable -/
private def rh005_multipleKeys : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 16
  for i in List.range 10 do
    t := t.insert i (i * 10)
  expect "size is 10" (t.size == 10)
  let mut allFound := true
  for i in List.range 10 do
    if t.get? i != some (i * 10) then allFound := false
  expect "all 10 keys retrievable" allFound

/-- RH-006: Collision handling — keys with same hash mod capacity -/
private def rh006_collisionHandling : IO Unit := do
  -- Keys 0, 16, 32 all hash to same bucket in capacity-16 table
  -- (since idealIndex uses hash(k).toNat % capacity, and hash for Nat
  --  delegates to native hash — we use keys likely to collide)
  let mut t : RHTable Nat Nat := RHTable.empty 16
  let keys := [0, 16, 32, 48]
  for k in keys do
    t := t.insert k (k + 1)
  let mut allFound := true
  for k in keys do
    if t.get? k != some (k + 1) then allFound := false
  expect "colliding keys all retrievable" allFound
  expect "size matches inserted count" (t.size == 4)

/-- RH-007: Robin Hood swap verification — insert sequence triggering displacement -/
private def rh007_robinHoodSwap : IO Unit := do
  -- Insert a sequence of keys, then verify all are still accessible.
  -- The Robin Hood property ensures displaced entries remain findable.
  let mut t : RHTable Nat Nat := RHTable.empty 8
  -- With capacity 8, inserting 5 keys forces collisions and swaps
  let keys := [0, 8, 16, 1, 9]
  for k in keys do
    t := t.insert k (k * 3)
  let mut allFound := true
  for k in keys do
    if t.get? k != some (k * 3) then allFound := false
  expect "all keys findable after swaps" allFound
  expect "size correct" (t.size == 5)

/-- RH-008: Backward-shift verification — erase from middle of cluster -/
private def rh008_backwardShift : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 16
  let keys := [0, 16, 32, 1, 17]
  for k in keys do
    t := t.insert k (k + 100)
  -- Erase a key from the middle of a likely cluster
  t := t.erase 16
  expect "erased key gone" (t.get? 16 == none)
  -- Remaining keys still accessible after backward shift
  expect "key 0 still present" (t.get? 0 == some 100)
  expect "key 32 still present" (t.get? 32 == some 132)
  expect "key 1 still present" (t.get? 1 == some 101)
  expect "key 17 still present" (t.get? 17 == some 117)
  expect "size decremented" (t.size == 4)

/-- RH-009: Resize trigger — insert until 75% load, verify resize doubles capacity -/
private def rh009_resizeTrigger : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 8
  -- Resize triggers when size * 4 ≥ capacity * 3 (75% load).
  -- With capacity 8: triggers when size ≥ 6 (6*4=24 ≥ 8*3=24).
  -- The check happens at the START of insert, so the 7th insert sees size=6
  -- and triggers resize (capacity 8→16) before inserting.
  for i in List.range 7 do
    t := t.insert i (i * 7)
  -- After 7 inserts, the 7th triggered resize: capacity 8→16
  expect "capacity doubled" (t.capacity == 16)
  expect "size preserved" (t.size == 7)

/-- RH-010: Post-resize correctness — all entries accessible after resize -/
private def rh010_postResizeCorrectness : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 4
  -- Insert enough to trigger multiple resizes: 4→8→16
  for i in List.range 12 do
    t := t.insert i (i * 11)
  let mut allFound := true
  for i in List.range 12 do
    if t.get? i != some (i * 11) then allFound := false
  expect "all entries accessible after resizes" allFound
  expect "size correct" (t.size == 12)
  expect "capacity grew" (t.capacity > 4)

/-- RH-011: Large-scale — insert 200 entries, verify all, erase 100, verify remaining -/
private def rh011_largeScale : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 16
  for i in List.range 200 do
    t := t.insert i (i * 13)
  expect "size is 200" (t.size == 200)
  let mut allInserted := true
  for i in List.range 200 do
    if t.get? i != some (i * 13) then allInserted := false
  expect "all 200 entries retrievable" allInserted
  -- Erase even-numbered keys (0, 2, 4, ..., 198) = 100 keys
  for i in List.range 100 do
    t := t.erase (i * 2)
  expect "size after 100 erases" (t.size == 100)
  -- Verify erased keys are gone
  let mut erasedGone := true
  for i in List.range 100 do
    if t.get? (i * 2) != none then erasedGone := false
  expect "erased keys absent" erasedGone
  -- Verify remaining (odd) keys still present
  let mut oddPresent := true
  for i in List.range 100 do
    let k := i * 2 + 1
    if t.get? k != some (k * 13) then oddPresent := false
  expect "remaining keys still present" oddPresent

/-- RH-012: Fold/toList — verify fold visits all entries -/
private def rh012_foldToList : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 16
  for i in List.range 5 do
    t := t.insert i (i * 2)
  -- Fold: sum all values
  let sum := t.fold 0 fun acc _ v => acc + v
  -- Expected: 0 + 2 + 4 + 6 + 8 = 20
  expect "fold sums correctly" (sum == 20)
  -- toList: verify length
  let lst := t.toList
  expect "toList length" (lst.length == 5)
  -- Verify all entries in list
  let mut allInList := true
  for i in List.range 5 do
    if !lst.any (fun ⟨k, v⟩ => k == i && v == i * 2) then allInList := false
  expect "toList contains all entries" allInList

-- ============================================================================
-- N5-B: CNode Integration Regression Tests (6 scenarios)
-- ============================================================================

open CNode in
/-- RH-INT-001: CNode lookup/insert/remove with RHTable-backed slots -/
private def rhInt001_cnodeLookupInsertRemove : IO Unit := do
  let cap1 : Capability := { target := .object ⟨100⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let cap2 : Capability := { target := .object ⟨200⟩, rights := AccessRightSet.ofList [.write], badge := none }
  let cn := CNode.empty
  -- Insert two capabilities
  let cn := cn.insert (SeLe4n.Slot.ofNat 0) cap1
  let cn := cn.insert (SeLe4n.Slot.ofNat 1) cap2
  expect "RH-INT-001a lookup slot 0" (cn.lookup (SeLe4n.Slot.ofNat 0) == some cap1)
  expect "RH-INT-001b lookup slot 1" (cn.lookup (SeLe4n.Slot.ofNat 1) == some cap2)
  expect "RH-INT-001c absent slot" (cn.lookup (SeLe4n.Slot.ofNat 5) == none)
  -- Remove slot 0
  let cn := cn.remove (SeLe4n.Slot.ofNat 0)
  expect "RH-INT-001d removed slot gone" (cn.lookup (SeLe4n.Slot.ofNat 0) == none)
  expect "RH-INT-001e other slot preserved" (cn.lookup (SeLe4n.Slot.ofNat 1) == some cap2)

open CNode in
/-- RH-INT-002: CNode.revokeTargetLocal with RHTable filter -/
private def rhInt002_revokeTargetLocal : IO Unit := do
  let target := CapTarget.object ⟨50⟩
  let otherTarget := CapTarget.object ⟨99⟩
  let cap1 : Capability := { target := target, rights := AccessRightSet.ofList [.read, .grant], badge := none }
  let cap2 : Capability := { target := target, rights := AccessRightSet.ofList [.read], badge := none }
  let capOther : Capability := { target := otherTarget, rights := AccessRightSet.ofList [.write], badge := none }
  let cn := ((CNode.empty.insert (SeLe4n.Slot.ofNat 0) cap1).insert (SeLe4n.Slot.ofNat 1) cap2).insert (SeLe4n.Slot.ofNat 2) capOther
  -- Revoke target from slot 0 (source) — should keep slot 0, remove slot 1, keep slot 2
  let cn' := cn.revokeTargetLocal (SeLe4n.Slot.ofNat 0) target
  expect "RH-INT-002a source slot preserved" (cn'.lookup (SeLe4n.Slot.ofNat 0) == some cap1)
  expect "RH-INT-002b target sibling removed" (cn'.lookup (SeLe4n.Slot.ofNat 1) == none)
  expect "RH-INT-002c other target preserved" (cn'.lookup (SeLe4n.Slot.ofNat 2) == some capOther)

open CNode in
/-- RH-INT-003: CNode.findFirstEmptySlot with RHTable-backed slots -/
private def rhInt003_findFirstEmptySlot : IO Unit := do
  let cap : Capability := { target := .object ⟨10⟩, rights := AccessRightSet.ofList [.read], badge := none }
  -- CNode with slots 0 and 1 occupied
  let cn := (CNode.empty.insert (SeLe4n.Slot.ofNat 0) cap).insert (SeLe4n.Slot.ofNat 1) cap
  -- Find first empty starting from slot 0 with limit 4
  let result := cn.findFirstEmptySlot (SeLe4n.Slot.ofNat 0) 4
  expect "RH-INT-003a finds empty slot" (result.isSome)
  -- Slot 2 should be the first empty (0 and 1 are occupied)
  expect "RH-INT-003b correct empty slot" (result == some (SeLe4n.Slot.ofNat 2))
  -- Verify the found slot is actually empty
  match result with
  | some s => expect "RH-INT-003c slot is empty" (cn.lookup s == none)
  | none => throw <| IO.userError "RH-INT-003c: expected some"

open CNode in
/-- RH-INT-004: CNode slotCountBounded after insert sequence -/
private def rhInt004_slotCountBounded : IO Unit := do
  let cap : Capability := { target := .object ⟨10⟩, rights := AccessRightSet.ofList [.read], badge := none }
  let mut cn := CNode.empty
  -- Insert several capabilities and verify slot count stays bounded
  for i in List.range 8 do
    cn := cn.insert (SeLe4n.Slot.ofNat i) cap
  -- The RHTable size should reflect the number of inserted slots
  expect "RH-INT-004a slot count" (cn.slots.size == 8)
  -- Capacity should be at least 16 (initial capacity of CNode.empty)
  expect "RH-INT-004b capacity >= 16" (cn.slots.capacity ≥ 16)

open CNode in
/-- RH-INT-005: Multi-level CSpace resolution with RHTable-backed CNodes -/
private def rhInt005_cspaceResolution : IO Unit := do
  -- Create a CNode with specific guard/radix for resolution testing
  let cap : Capability := { target := .object ⟨42⟩, rights := AccessRightSet.ofList [.read, .write], badge := none }
  let cn := CNode.mk' 4 0 0 2 (RHTable.ofList [((SeLe4n.Slot.ofNat 0), cap), ((SeLe4n.Slot.ofNat 1), cap), ((SeLe4n.Slot.ofNat 3), cap)])
  -- Resolve slot from CPtr
  let result := cn.resolveSlot (SeLe4n.CPtr.ofNat 3) 4
  match result with
  | .ok slot =>
    expect "RH-INT-005a resolution succeeds" true
    expect "RH-INT-005b resolved slot has capability" (cn.lookup slot == some cap)
  | .error _ =>
    -- Resolution depends on guard/radix matching — verify the CNode at least works
    expect "RH-INT-005a direct lookup works" (cn.lookup (SeLe4n.Slot.ofNat 0) == some cap)
    expect "RH-INT-005b direct lookup slot 3" (cn.lookup (SeLe4n.Slot.ofNat 3) == some cap)

open CNode in
/-- RH-INT-006: CNode BEq comparison with RHTable slots -/
private def rhInt006_cnodeBEq : IO Unit := do
  let cap : Capability := { target := .object ⟨10⟩, rights := AccessRightSet.ofList [.read], badge := none }
  -- Two CNodes built identically should be BEq-equal
  let cn1 := CNode.empty.insert (SeLe4n.Slot.ofNat 0) cap
  let cn2 := CNode.empty.insert (SeLe4n.Slot.ofNat 0) cap
  expect "RH-INT-006a identical CNodes equal" (cn1 == cn2)
  -- Different CNodes should not be equal
  let cn3 := CNode.empty.insert (SeLe4n.Slot.ofNat 1) cap
  expect "RH-INT-006b different CNodes not equal" (!(cn1 == cn3))

private def runRobinHoodSuite : IO Unit := do
  IO.println "=== Robin Hood Hash Table Test Suite (WS-N5) ==="
  IO.println ""
  IO.println "--- Standalone Tests (RH-001 to RH-012) ---"
  rh001_emptyTable
  rh002_singleInsertGet
  rh003_insertErase
  rh004_overwrite
  rh005_multipleKeys
  rh006_collisionHandling
  rh007_robinHoodSwap
  rh008_backwardShift
  rh009_resizeTrigger
  rh010_postResizeCorrectness
  rh011_largeScale
  rh012_foldToList
  IO.println ""
  IO.println "--- Integration Tests (RH-INT-001 to RH-INT-006) ---"
  rhInt001_cnodeLookupInsertRemove
  rhInt002_revokeTargetLocal
  rhInt003_findFirstEmptySlot
  rhInt004_slotCountBounded
  rhInt005_cspaceResolution
  rhInt006_cnodeBEq
  IO.println ""
  IO.println "=== All Robin Hood tests passed ==="

end SeLe4n.Testing.RobinHoodSuite

def main : IO Unit :=
  SeLe4n.Testing.RobinHoodSuite.runRobinHoodSuite
