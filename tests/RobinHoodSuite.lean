/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RobinHood

open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- Robin Hood Hash Table Test Suite (WS-N2)
-- ============================================================================

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"robin-hood check passed [{label}]"
  else
    throw <| IO.userError s!"robin-hood check FAILED [{label}]"

-- ============================================================================
-- Section 1: Basic Operations
-- ============================================================================

private def testEmptyTable : IO Unit := do
  let t : RHTable Nat String := RHTable.empty 8
  expect "empty-size-zero" (t.size == 0)
  expect "empty-capacity-8" (t.capacity == 8)
  expect "empty-get-none" (t.get? 42 == none)
  expect "empty-contains-false" (t.contains 42 == false)

private def testInsertAndGet : IO Unit := do
  let t : RHTable Nat String := RHTable.empty 8
  let t := t.insert 1 "one"
  expect "insert-get-eq" (t.get? 1 == some "one")
  expect "insert-size-1" (t.size == 1)
  expect "insert-contains" (t.contains 1 == true)
  expect "insert-other-none" (t.get? 2 == none)

private def testInsertOverwrite : IO Unit := do
  let t : RHTable Nat String := RHTable.empty 8
  let t := t.insert 1 "one"
  let t := t.insert 1 "ONE"
  expect "overwrite-get" (t.get? 1 == some "ONE")
  expect "overwrite-size-still-1" (t.size == 1)

private def testEraseBasic : IO Unit := do
  let t : RHTable Nat String := RHTable.empty 8
  let t := t.insert 1 "one"
  let t := t.insert 2 "two"
  let t := t.erase 1
  expect "erase-removed" (t.get? 1 == none)
  expect "erase-other-intact" (t.get? 2 == some "two")
  expect "erase-size-1" (t.size == 1)

private def testEraseNonexistent : IO Unit := do
  let t : RHTable Nat String := RHTable.empty 8
  let t := t.insert 1 "one"
  let t := t.erase 99
  expect "erase-nonexistent-intact" (t.get? 1 == some "one")
  expect "erase-nonexistent-size" (t.size == 1)

-- ============================================================================
-- Section 2: Multiple Inserts and Collision Handling
-- ============================================================================

private def testMultipleInserts : IO Unit := do
  let mut t : RHTable Nat String := RHTable.empty 16
  for i in List.range 10 do
    t := t.insert i s!"val-{i}"
  expect "multi-insert-size" (t.size == 10)
  for i in List.range 10 do
    expect s!"multi-insert-get-{i}" (t.get? i == some s!"val-{i}")

private def testInsertEraseSequence : IO Unit := do
  let mut t : RHTable Nat String := RHTable.empty 16
  -- Insert 8 entries
  for i in List.range 8 do
    t := t.insert i s!"v{i}"
  -- Erase even keys
  for i in [0, 2, 4, 6] do
    t := t.erase i
  expect "insert-erase-seq-size" (t.size == 4)
  -- Odd keys still present
  for i in [1, 3, 5, 7] do
    expect s!"insert-erase-seq-odd-{i}" (t.get? i == some s!"v{i}")
  -- Even keys gone
  for i in [0, 2, 4, 6] do
    expect s!"insert-erase-seq-even-{i}" (t.get? i == none)

-- ============================================================================
-- Section 3: Resize Behavior
-- ============================================================================

private def testResizeTrigger : IO Unit := do
  -- Capacity 4, 75% load = 3 entries triggers resize
  let mut t : RHTable Nat String := RHTable.empty 4
  let origCap := t.capacity
  for i in List.range 4 do
    t := t.insert i s!"v{i}"
  expect "resize-capacity-doubled" (t.capacity > origCap)
  -- All entries survive resize
  for i in List.range 4 do
    expect s!"resize-entry-{i}" (t.get? i == some s!"v{i}")

private def testResizePreservesEntries : IO Unit := do
  let mut t : RHTable Nat String := RHTable.empty 4
  for i in List.range 10 do
    t := t.insert i s!"val-{i}"
  expect "resize-pres-size" (t.size == 10)
  for i in List.range 10 do
    expect s!"resize-pres-get-{i}" (t.get? i == some s!"val-{i}")

-- ============================================================================
-- Section 4: Edge Cases
-- ============================================================================

private def testSingleCapacity : IO Unit := do
  let t : RHTable Nat String := RHTable.empty 1
  let t := t.insert 0 "zero"
  expect "single-cap-get" (t.get? 0 == some "zero")
  -- Second insert triggers resize
  let t := t.insert 1 "one"
  expect "single-cap-resize-get-0" (t.get? 0 == some "zero")
  expect "single-cap-resize-get-1" (t.get? 1 == some "one")

private def testEraseAll : IO Unit := do
  let mut t : RHTable Nat String := RHTable.empty 8
  for i in List.range 5 do
    t := t.insert i s!"v{i}"
  for i in List.range 5 do
    t := t.erase i
  expect "erase-all-size-zero" (t.size == 0)
  for i in List.range 5 do
    expect s!"erase-all-none-{i}" (t.get? i == none)

-- ============================================================================
-- Section 5: Well-Formedness Checks
-- ============================================================================

private def checkWF (t : RHTable Nat String) : Bool :=
  t.slots.size == t.capacity && t.size ≤ t.capacity

private def testWFAfterOperations : IO Unit := do
  let mut t : RHTable Nat String := RHTable.empty 8
  expect "wf-empty" (checkWF t)
  for i in List.range 6 do
    t := t.insert i s!"v{i}"
  expect "wf-after-inserts" (checkWF t)
  for i in [0, 2, 4] do
    t := t.erase i
  expect "wf-after-erases" (checkWF t)

-- ============================================================================
-- Section 6: Fold and ToList
-- ============================================================================

private def testFoldAndToList : IO Unit := do
  let mut t : RHTable Nat Nat := RHTable.empty 8
  for i in List.range 5 do
    t := t.insert i (i * 10)
  -- Fold to sum values
  let sum := t.fold 0 (fun acc _ v => acc + v)
  expect "fold-sum" (sum == 0 + 10 + 20 + 30 + 40)
  -- toList contains all entries
  let entries := t.toList
  expect "toList-length" (entries.length == 5)

-- ============================================================================
-- Section 7: Bracket Notation (GetElem? instance)
-- ============================================================================

private def testBracketNotation : IO Unit := do
  let t : RHTable Nat String := (RHTable.empty 8).insert 42 "answer"
  expect "bracket-some" (t[42]? == some "answer")
  expect "bracket-none" (t[99]? == none)

-- ============================================================================
-- Main entry point
-- ============================================================================

def main : IO Unit := do
  IO.println "=== Robin Hood Hash Table Test Suite ==="
  testEmptyTable
  testInsertAndGet
  testInsertOverwrite
  testEraseBasic
  testEraseNonexistent
  testMultipleInserts
  testInsertEraseSequence
  testResizeTrigger
  testResizePreservesEntries
  testSingleCapacity
  testEraseAll
  testWFAfterOperations
  testFoldAndToList
  testBracketNotation
  IO.println "=== All Robin Hood tests passed ==="
