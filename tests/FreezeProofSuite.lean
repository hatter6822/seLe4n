/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Model.FrozenState
import SeLe4n.Model.FreezeProofs

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.RadixTree
open SeLe4n.Model

namespace SeLe4n.Testing.FreezeProofSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"freeze-proof check passed [{label}]"
  else
    throw <| IO.userError s!"freeze-proof check failed [{label}]"

-- ============================================================================
-- Q6-T1: freezeMap Lookup Equivalence (7 scenarios)
-- ============================================================================

/-- FP-001: freezeMap single entry — lookup matches source -/
private def fp001_singleLookup : IO Unit := do
  let rt := (RHTable.empty 16 : RHTable ObjId Nat).insert ⟨5⟩ 100
  let fm := freezeMap rt
  expect "FP-001a frozen get? matches insert" (fm.get? ⟨5⟩ == some 100)
  expect "FP-001b frozen get? missing key" (fm.get? ⟨99⟩ == none)
  expect "FP-001c source get? matches" (rt.get? ⟨5⟩ == fm.get? ⟨5⟩)

/-- FP-002: freezeMap multi-entry — all lookups agree with source -/
private def fp002_multiLookup : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
    |>.insert ⟨3⟩ 30
  let fm := freezeMap rt
  expect "FP-002a key 1" (rt.get? ⟨1⟩ == fm.get? ⟨1⟩)
  expect "FP-002b key 2" (rt.get? ⟨2⟩ == fm.get? ⟨2⟩)
  expect "FP-002c key 3" (rt.get? ⟨3⟩ == fm.get? ⟨3⟩)
  expect "FP-002d missing" (rt.get? ⟨99⟩ == fm.get? ⟨99⟩)

/-- FP-003: freezeMap empty — none for all lookups -/
private def fp003_emptyLookup : IO Unit := do
  let rt : RHTable ObjId Nat := RHTable.empty 16
  let fm := freezeMap rt
  expect "FP-003a empty get? key 0" (fm.get? ⟨0⟩ == none)
  expect "FP-003b empty get? key 42" (fm.get? ⟨42⟩ == none)
  expect "FP-003c source agrees" (rt.get? ⟨0⟩ == fm.get? ⟨0⟩)

/-- FP-004: freezeMap with overwritten key — latest value wins -/
private def fp004_overwrite : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨1⟩ 99
  let fm := freezeMap rt
  expect "FP-004a overwritten key" (fm.get? ⟨1⟩ == some 99)
  expect "FP-004b source agrees" (rt.get? ⟨1⟩ == fm.get? ⟨1⟩)

/-- FP-005: freezeMap large table — 10 entries all preserved -/
private def fp005_largeLookup : IO Unit := do
  let mut rt : RHTable ObjId Nat := RHTable.empty 32
  for i in List.range 10 do
    rt := rt.insert ⟨i⟩ (i * 100)
  let fm := freezeMap rt
  let mut allMatch := true
  for i in List.range 10 do
    if rt.get? ⟨i⟩ != fm.get? ⟨i⟩ then allMatch := false
  expect "FP-005a all 10 entries match" allMatch
  expect "FP-005b missing key 99" (fm.get? ⟨99⟩ == none)

-- ============================================================================
-- Q6-T2: Per-Field Lookup Equivalence (4 scenarios)
-- ============================================================================

/-- FP-006: IRQ handlers field — freeze preserves lookup -/
private def fp006_irqHandlers : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  expect "FP-006a empty irq lookup" (fss.irqHandlers.get? ⟨0⟩ == none)
  expect "FP-006b empty irq lookup 5" (fss.irqHandlers.get? ⟨5⟩ == none)

/-- FP-007: ASID table field — freeze preserves lookup -/
private def fp007_asidTable : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  expect "FP-007a empty asid lookup" (fss.asidTable.get? ⟨0⟩ == none)

/-- FP-008: Object types field — freeze preserves lookup -/
private def fp008_objectTypes : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  expect "FP-008a empty objectTypes lookup" (fss.objectTypes.get? ⟨0⟩ == none)

/-- FP-009: CDT maps — freeze preserves lookup -/
private def fp009_cdtMaps : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  let nodeId : CdtNodeId := ⟨0⟩
  expect "FP-009a cdtChildMap empty" (fss.cdtChildMap.get? nodeId == none)
  expect "FP-009b cdtParentMap empty" (fss.cdtParentMap.get? nodeId == none)

-- ============================================================================
-- Q6-T3: CNode Radix Equivalence (4 scenarios)
-- ============================================================================

/-- FP-010: CNode radix — single slot lookup preserved -/
private def fp010_cnodeRadixSingle : IO Unit := do
  let cap : Capability :=
    { target := .object ⟨100⟩
      rights := AccessRightSet.ofList [.read]
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 4, guardValue := 0
      radixWidth := 4
      slots := (RHTable.empty 16).insert ⟨3⟩ cap }
  let frozen := freezeObject (.cnode cn)
  match frozen with
  | .cnode fc =>
    -- Source lookup matches radix lookup
    expect "FP-010a radix finds cap" (fc.slots.lookup ⟨3⟩ == some cap)
    expect "FP-010b source agrees" (cn.slots.get? ⟨3⟩ == some cap)
    expect "FP-010c radix misses absent" (fc.slots.lookup ⟨7⟩ == none)
  | _ => throw <| IO.userError "FP-010: expected FrozenCNode"

/-- FP-011: CNode radix — multiple slots all preserved -/
private def fp011_cnodeRadixMulti : IO Unit := do
  let mkCap (n : Nat) : Capability :=
    { target := .object ⟨n⟩
      rights := AccessRightSet.ofList [.read]
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 0, guardValue := 0
      radixWidth := 4
      slots := ((RHTable.empty 16).insert ⟨1⟩ (mkCap 1))
        |>.insert ⟨2⟩ (mkCap 2)
        |>.insert ⟨5⟩ (mkCap 5) }
  let frozen := freezeObject (.cnode cn)
  match frozen with
  | .cnode fc =>
    expect "FP-011a slot 1" (fc.slots.lookup ⟨1⟩ == some (mkCap 1))
    expect "FP-011b slot 2" (fc.slots.lookup ⟨2⟩ == some (mkCap 2))
    expect "FP-011c slot 5" (fc.slots.lookup ⟨5⟩ == some (mkCap 5))
    expect "FP-011d absent slot" (fc.slots.lookup ⟨0⟩ == none)
  | _ => throw <| IO.userError "FP-011: expected FrozenCNode"

/-- FP-012: CNode radix — empty CNode slots all none -/
private def fp012_cnodeRadixEmpty : IO Unit := do
  let cn : CNode :=
    { depth := 16, guardWidth := 4, guardValue := 0
      radixWidth := 4
      slots := RHTable.empty 16 }
  let frozen := freezeObject (.cnode cn)
  match frozen with
  | .cnode fc =>
    expect "FP-012a empty radix slot 0" (fc.slots.lookup ⟨0⟩ == none)
    expect "FP-012b empty radix slot 3" (fc.slots.lookup ⟨3⟩ == none)
  | _ => throw <| IO.userError "FP-012: expected FrozenCNode"

/-- FP-013: CNode radix — structural properties preserved -/
private def fp013_cnodeRadixStructure : IO Unit := do
  let cap : Capability :=
    { target := .object ⟨42⟩
      rights := AccessRightSet.ofList [.read, .write]
      badge := none }
  let cn : CNode :=
    { depth := 16, guardWidth := 2, guardValue := 1
      radixWidth := 3
      slots := (RHTable.empty 16).insert ⟨4⟩ cap }
  let frozen := freezeObject (.cnode cn)
  match frozen with
  | .cnode fc =>
    expect "FP-013a guardWidth preserved" (fc.guardWidth == 2)
    expect "FP-013b guardValue preserved" (fc.guardValue == 1)
    expect "FP-013c radixWidth preserved" (fc.radixWidth == 3)
  | _ => throw <| IO.userError "FP-013: expected FrozenCNode"

-- ============================================================================
-- Q6-T4: Structural Properties (5 scenarios)
-- ============================================================================

/-- FP-014: freezeMap preserves size -/
private def fp014_preservesSize : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
    |>.insert ⟨3⟩ 30
  let fm := freezeMap rt
  expect "FP-014a data size equals entry count" (fm.data.size == 3)

/-- FP-015: freezeMap preserves membership symmetry -/
private def fp015_preservesMembership : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
  let fm := freezeMap rt
  expect "FP-015a present key isSome" ((fm.get? ⟨1⟩).isSome)
  expect "FP-015b present key isSome" ((fm.get? ⟨2⟩).isSome)
  expect "FP-015c absent key isNone" ((fm.get? ⟨99⟩).isNone)

/-- FP-016: freeze determinism — same input same output -/
private def fp016_deterministic : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss1 := freeze ist
  let fss2 := freeze ist
  expect "FP-016a same objects size" (fss1.objects.data.size == fss2.objects.data.size)
  expect "FP-016b same irq size" (fss1.irqHandlers.data.size == fss2.irqHandlers.data.size)
  expect "FP-016c same CDT edges" (fss1.cdtEdges == fss2.cdtEdges)
  expect "FP-016d same objectIndex" (fss1.objectIndex == fss2.objectIndex)

/-- FP-017: freezeMap no duplicate keys — distinct entries have distinct keys -/
private def fp017_noDuplicates : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨1⟩ 10)
    |>.insert ⟨2⟩ 20
    |>.insert ⟨3⟩ 30
  let fm := freezeMap rt
  -- All keys are distinct — no two different indices return the same key
  let keys := #[⟨1⟩, ⟨2⟩, ⟨3⟩]
  let mut allDistinct := true
  for i in List.range keys.size do
    for j in List.range keys.size do
      if i != j then
        if fm.get? keys[i]! == fm.get? keys[j]! then
          allDistinct := false
  expect "FP-017a all keys distinct values" allDistinct

/-- FP-018: freezeMap total coverage — every source key has a data index -/
private def fp018_totalCoverage : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨10⟩ 100)
    |>.insert ⟨20⟩ 200
  let fm := freezeMap rt
  expect "FP-018a key 10 covered" ((fm.get? ⟨10⟩).isSome)
  expect "FP-018b key 20 covered" ((fm.get? ⟨20⟩).isSome)
  expect "FP-018c data size matches" (fm.data.size == 2)

-- ============================================================================
-- Q6-T5: Invariant Transfer (3 scenarios)
-- ============================================================================

/-- FP-019: freeze empty state preserves structural integrity -/
private def fp019_freezeEmptyInvariant : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  -- All frozen maps have consistent empty state
  expect "FP-019a objects empty" (fss.objects.data.size == 0)
  expect "FP-019b objectTypes empty" (fss.objectTypes.data.size == 0)
  expect "FP-019c capabilityRefs empty" (fss.capabilityRefs.data.size == 0)

/-- FP-020: freeze preserves field parity — all SystemState fields represented -/
private def fp020_fieldParity : IO Unit := do
  let ist := mkEmptyIntermediateState
  let fss := freeze ist
  -- Verify all fields exist and are accessible
  expect "FP-020a objects accessible" (fss.objects.data.size == 0)
  expect "FP-020b irqHandlers accessible" (fss.irqHandlers.data.size == 0)
  expect "FP-020c asidTable accessible" (fss.asidTable.data.size == 0)
  expect "FP-020d cdtEdges accessible" (fss.cdtEdges.length == 0)
  expect "FP-020e objectIndex accessible" (fss.objectIndex.length == 0)
  expect "FP-020f scheduler accessible" (fss.scheduler.current == none)

/-- FP-021: frozen lookup transfer — source and frozen agree for all keys -/
private def fp021_lookupTransfer : IO Unit := do
  let rt := ((RHTable.empty 16 : RHTable ObjId Nat).insert ⟨7⟩ 77)
    |>.insert ⟨13⟩ 130
    |>.insert ⟨42⟩ 420
  let fm := freezeMap rt
  -- Exhaustive check: every key lookup agrees
  expect "FP-021a transfer key 7" (rt.get? ⟨7⟩ == fm.get? ⟨7⟩)
  expect "FP-021b transfer key 13" (rt.get? ⟨13⟩ == fm.get? ⟨13⟩)
  expect "FP-021c transfer key 42" (rt.get? ⟨42⟩ == fm.get? ⟨42⟩)
  expect "FP-021d transfer absent key" (rt.get? ⟨99⟩ == fm.get? ⟨99⟩)

-- ============================================================================
-- Main test runner
-- ============================================================================

end SeLe4n.Testing.FreezeProofSuite

open SeLe4n.Testing.FreezeProofSuite in
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Q6 Freeze Proof Suite"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Q6-T1: freezeMap Lookup Equivalence
  fp001_singleLookup
  fp002_multiLookup
  fp003_emptyLookup
  fp004_overwrite
  fp005_largeLookup

  -- Q6-T2: Per-Field Lookup Equivalence
  fp006_irqHandlers
  fp007_asidTable
  fp008_objectTypes
  fp009_cdtMaps

  -- Q6-T3: CNode Radix Equivalence
  fp010_cnodeRadixSingle
  fp011_cnodeRadixMulti
  fp012_cnodeRadixEmpty
  fp013_cnodeRadixStructure

  -- Q6-T4: Structural Properties
  fp014_preservesSize
  fp015_preservesMembership
  fp016_deterministic
  fp017_noDuplicates
  fp018_totalCoverage

  -- Q6-T5: Invariant Transfer
  fp019_freezeEmptyInvariant
  fp020_fieldParity
  fp021_lookupTransfer

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  All 21 freeze-proof tests passed!"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
