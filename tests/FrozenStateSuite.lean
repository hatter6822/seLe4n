/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Model.FrozenState

open SeLe4n.Kernel.RadixTree
open SeLe4n.Kernel.RobinHood
open SeLe4n.Model

namespace SeLe4n.Testing.FrozenStateSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"frozen-state check passed [{label}]"
  else
    throw <| IO.userError s!"frozen-state check failed [{label}]"

-- ============================================================================
-- Q5-T1: FrozenMap Core Tests (7 scenarios)
-- ============================================================================

/-- FS-001: Empty FrozenMap — get? returns none for any key -/
private def fs001_emptyFrozenMap : IO Unit := do
  let fm : FrozenMap ObjId Nat := freezeMap (RHTable.empty 16)
  expect "empty frozen map get? returns none" (fm.get? ⟨0⟩ == none)
  expect "empty frozen map get? returns none for key 42" (fm.get? ⟨42⟩ == none)
  expect "empty frozen map size is 0" (fm.data.size == 0)
  expect "empty frozen map contains is false" (fm.contains ⟨0⟩ == false)

/-- FS-002: Single-entry FrozenMap — insert into RHTable, freeze, lookup -/
private def fs002_singleEntry : IO Unit := do
  let rt := (RHTable.empty 16 : RHTable ObjId Nat).insert ⟨5⟩ 100
  let fm := freezeMap rt
  -- The frozen map should have 1 entry
  expect "frozen map data size is 1" (fm.data.size == 1)
  -- Lookup should find the value
  expect "frozen map get? finds value" (fm.get? ⟨5⟩ == some 100)
  -- Missing key returns none
  expect "frozen map get? misses key" (fm.get? ⟨99⟩ == none)
  expect "frozen map contains works" (fm.contains ⟨5⟩ == true)

/-- FS-003: Multi-entry FrozenMap — 3 entries, verify all lookups -/
private def fs003_multiEntry : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
    |>.insert ⟨3⟩ 30
  let fm := freezeMap rt
  expect "data size is 3" (fm.data.size == 3)
  expect "get? key 1" (fm.get? ⟨1⟩ == some 10)
  expect "get? key 2" (fm.get? ⟨2⟩ == some 20)
  expect "get? key 3" (fm.get? ⟨3⟩ == some 30)
  expect "get? missing key" (fm.get? ⟨99⟩ == none)

/-- FS-004: FrozenMap.set — update existing value -/
private def fs004_frozenMapSet : IO Unit := do
  let rt := (RHTable.empty 16 : RHTable ObjId Nat).insert ⟨7⟩ 42
  let fm := freezeMap rt
  match fm.set ⟨7⟩ 99 with
  | none => throw <| IO.userError "set should succeed"
  | some fm' =>
    expect "set updates value" (fm'.get? ⟨7⟩ == some 99)
    expect "set preserves size" (fm'.data.size == fm.data.size)

/-- FS-005: FrozenMap.set — missing key returns none -/
private def fs005_frozenMapSetMissing : IO Unit := do
  let rt := (RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10
  let fm := freezeMap rt
  expect "set missing key returns none" (fm.set ⟨99⟩ 50 |>.isNone)

/-- FS-006: FrozenSet — membership checks -/
private def fs006_frozenSet : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ThreadId Unit).insert ⟨1⟩ ())
    |>.insert ⟨2⟩ ()
    |>.insert ⟨3⟩ ()
  let fs : FrozenSet ThreadId := freezeMap rt
  expect "frozen set member 1" (FrozenMap.contains fs ⟨1⟩ == true)
  expect "frozen set member 2" (FrozenMap.contains fs ⟨2⟩ == true)
  expect "frozen set non-member" (FrozenMap.contains fs ⟨99⟩ == false)

/-- FS-007: FrozenMap.get? — retrieves entries by key -/
private def fs007_frozenMapGet : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
  let fm := freezeMap rt
  expect "get key 1" (fm.get? ⟨1⟩ == some 10)
  expect "get key 2" (fm.get? ⟨2⟩ == some 20)
  expect "get missing key" (fm.get? ⟨99⟩ == none)

-- ============================================================================
-- Q5-T2: FrozenKernelObject Tests (3 scenarios)
-- ============================================================================

/-- FS-008: freezeObject preserves TCB (pass-through) -/
private def fs008_freezeTcb : IO Unit := do
  let tid : ThreadId := ⟨1⟩
  let tcb : TCB :=
    { tid := tid, priority := ⟨10⟩, domain := ⟨0⟩
      cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) }
  let frozen := freezeObject (.tcb tcb)
  expect "frozen TCB has correct type" (frozen.objectType == .tcb)

/-- FS-009: freezeObject converts CNode to FrozenCNode -/
private def fs009_freezeCNode : IO Unit := do
  let cap : Capability :=
    { target := .object ⟨100⟩
      rights := AccessRightSet.ofList [.read]
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 4, guardValue := 0
      radixWidth := 4
      slots := (RHTable.empty 16).insert (SeLe4n.Slot.ofNat 3) cap }
  let frozen := freezeObject (.cnode cn)
  expect "frozen CNode has correct type" (frozen.objectType == .cnode)
  -- Verify the frozen CNode slots use CNodeRadix (flat array)
  match frozen with
  | .cnode fc =>
    expect "guard width preserved" (fc.guardWidth == 4)
    expect "guard value preserved" (fc.guardValue == 0)
    expect "radix width preserved" (fc.radixWidth == 4)
    expect "radix lookup finds cap" (fc.slots.lookup (SeLe4n.Slot.ofNat 3) == some cap)
    expect "radix lookup misses" (fc.slots.lookup (SeLe4n.Slot.ofNat 7) == none)
  | _ => throw <| IO.userError "expected FrozenCNode"

/-- FS-010: freezeObject converts VSpaceRoot to FrozenVSpaceRoot -/
private def fs010_freezeVSpaceRoot : IO Unit := do
  let perms : PagePermissions :=
    { read := true, write := false, execute := false }
  let vs : VSpaceRoot :=
    { asid := ⟨1⟩
      mappings := (RHTable.empty 16).insert (SeLe4n.VAddr.ofNat 0x1000) ((SeLe4n.PAddr.ofNat 0x2000), perms) }
  let frozen := freezeObject (.vspaceRoot vs)
  expect "frozen VSpaceRoot type" (frozen.objectType == .vspaceRoot)
  match frozen with
  | .vspaceRoot fvs =>
    expect "ASID preserved" (fvs.asid == ⟨1⟩)
    expect "mappings lookup works" (fvs.mappings.get? (SeLe4n.VAddr.ofNat 0x1000) == some ((SeLe4n.PAddr.ofNat 0x2000), perms))
  | _ => throw <| IO.userError "expected FrozenVSpaceRoot"

-- ============================================================================
-- Q5-T3: Freeze Integration Tests (3 scenarios)
-- ============================================================================

/-- FS-011: freeze empty IntermediateState -/
private def fs011_freezeEmpty : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  expect "frozen objects data size 0" (fss.objects.data.size == 0)
  expect "frozen IRQ handlers empty" (fss.irqHandlers.data.size == 0)
  expect "frozen ASID table empty" (fss.asidTable.data.size == 0)
  expect "objectIndex empty" (fss.objectIndex.length == 0)
  expect "CDT edges empty" (fss.cdtEdges.length == 0)
  expect "objectIndexSet empty" (fss.objectIndexSet.data.size == 0)
  expect "scheduler current is none" (fss.scheduler.current == none)
  expect "scheduler byPriority empty" (fss.scheduler.byPriority.data.size == 0)
  expect "scheduler threadPriority empty" (fss.scheduler.threadPriority.data.size == 0)

/-- FS-012: freeze deterministic — same input yields same output -/
private def fs012_freezeDeterministic : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss1 := freeze ist
  let fss2 := freeze ist
  expect "same objects data size" (fss1.objects.data.size == fss2.objects.data.size)
  expect "same irq data size" (fss1.irqHandlers.data.size == fss2.irqHandlers.data.size)
  expect "same CDT edges" (fss1.cdtEdges == fss2.cdtEdges)
  expect "same objectIndex" (fss1.objectIndex == fss2.objectIndex)

/-- FS-014: FrozenMap.set preserves data size -/
private def fs014_frozenMapSetSize : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
  let fm := freezeMap rt
  let origSize := fm.data.size
  match fm.set ⟨1⟩ 99 with
  | none => throw <| IO.userError "set should succeed"
  | some fm' =>
    expect "set preserves data size" (fm'.data.size == origSize)
    expect "set updates value" (fm'.get? ⟨1⟩ == some 99)
    expect "set preserves other value" (fm'.get? ⟨2⟩ == some 20)

/-- FS-015: freezeMap data size matches source entry count -/
private def fs015_freezeMapDataSize : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
    |>.insert ⟨3⟩ 30
    |>.insert ⟨4⟩ 40
    |>.insert ⟨5⟩ 50
  let fm := freezeMap rt
  expect "data size is 5" (fm.data.size == 5)
  -- Verify round-trip: all keys accessible
  expect "all 5 keys accessible" (
    (fm.get? ⟨1⟩).isSome && (fm.get? ⟨2⟩).isSome && (fm.get? ⟨3⟩).isSome &&
    (fm.get? ⟨4⟩).isSome && (fm.get? ⟨5⟩).isSome)

-- ============================================================================
-- Main test runner
-- ============================================================================

end SeLe4n.Testing.FrozenStateSuite

open SeLe4n.Testing.FrozenStateSuite in
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Q5 Frozen State Suite"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Q5-T1: FrozenMap Core
  fs001_emptyFrozenMap
  fs002_singleEntry
  fs003_multiEntry
  fs004_frozenMapSet
  fs005_frozenMapSetMissing
  fs006_frozenSet
  fs007_frozenMapGet

  -- Q5-T2: FrozenKernelObject
  fs008_freezeTcb
  fs009_freezeCNode
  fs010_freezeVSpaceRoot

  -- Q5-T3: Freeze Integration
  fs011_freezeEmpty
  fs012_freezeDeterministic
  fs014_frozenMapSetSize
  fs015_freezeMapDataSize

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  All 14 frozen-state tests passed!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
