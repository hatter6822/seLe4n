/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.RadixTree
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Model

namespace SeLe4n.Testing.FrozenOpsSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"frozen-ops check passed [{label}]"
  else
    throw <| IO.userError s!"frozen-ops check failed [{label}]"

-- ============================================================================
-- Q7-T1: FrozenKernel Monad Tests
-- ============================================================================

/-- FO-001: frozenLookupObject — find existing object -/
private def fo001_lookupExisting : IO Unit := do
  let tcb : TCB := { tid := ⟨1⟩, priority := ⟨0⟩, domain := ⟨0⟩, cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := ⟨0⟩ }
  let rt := (RHTable.empty 16 : RHTable ObjId FrozenKernelObject).insert ⟨1⟩ (.tcb tcb)
  let fm := freezeMap rt
  let fst : FrozenSystemState := {
    objects := fm
    irqHandlers := freezeMap (RHTable.empty 16)
    asidTable := freezeMap (RHTable.empty 16)
    serviceRegistry := freezeMap (RHTable.empty 16)
    interfaceRegistry := freezeMap (RHTable.empty 16)
    services := freezeMap (RHTable.empty 16)
    cdtChildMap := freezeMap (RHTable.empty 16)
    cdtParentMap := freezeMap (RHTable.empty 16)
    cdtSlotNode := freezeMap (RHTable.empty 16)
    cdtNodeSlot := freezeMap (RHTable.empty 16)
    cdtEdges := []
    cdtNextNode := ⟨0⟩
    scheduler := {
      byPriority := freezeMap (RHTable.empty 16)
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap (RHTable.empty 16)
      current := none
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
    }
    objectTypes := freezeMap (RHTable.empty 16)
    capabilityRefs := freezeMap (RHTable.empty 16)
    machine := default
    objectIndex := []
    objectIndexSet := freezeMap (RHTable.empty 16)
  }
  match frozenLookupObject ⟨1⟩ fst with
  | .ok (obj, _) =>
      expect "FO-001a lookup found object" (obj.objectType == .tcb)
  | .error _ =>
      throw <| IO.userError "FO-001a lookup should succeed"

/-- FO-002: frozenLookupObject — missing object returns error -/
private def fo002_lookupMissing : IO Unit := do
  let fm : FrozenMap ObjId FrozenKernelObject := freezeMap (RHTable.empty 16)
  let fst : FrozenSystemState := {
    objects := fm
    irqHandlers := freezeMap (RHTable.empty 16)
    asidTable := freezeMap (RHTable.empty 16)
    serviceRegistry := freezeMap (RHTable.empty 16)
    interfaceRegistry := freezeMap (RHTable.empty 16)
    services := freezeMap (RHTable.empty 16)
    cdtChildMap := freezeMap (RHTable.empty 16)
    cdtParentMap := freezeMap (RHTable.empty 16)
    cdtSlotNode := freezeMap (RHTable.empty 16)
    cdtNodeSlot := freezeMap (RHTable.empty 16)
    cdtEdges := []
    cdtNextNode := ⟨0⟩
    scheduler := {
      byPriority := freezeMap (RHTable.empty 16)
      threadPriority := freezeMap (RHTable.empty 16)
      membership := freezeMap (RHTable.empty 16)
      current := none
      activeDomain := ⟨0⟩
      domainTimeRemaining := 5
      domainSchedule := []
      domainScheduleIndex := 0
    }
    objectTypes := freezeMap (RHTable.empty 16)
    capabilityRefs := freezeMap (RHTable.empty 16)
    machine := default
    objectIndex := []
    objectIndexSet := freezeMap (RHTable.empty 16)
  }
  match frozenLookupObject ⟨99⟩ fst with
  | .ok _ => throw <| IO.userError "FO-002 lookup should fail"
  | .error e => expect "FO-002 missing returns objectNotFound" (e == .objectNotFound)

end SeLe4n.Testing.FrozenOpsSuite

open SeLe4n.Testing.FrozenOpsSuite in
def main : IO Unit := do
  IO.println "=== Q7 Frozen Operations Test Suite ==="
  fo001_lookupExisting
  fo002_lookupMissing
  IO.println "=== All Q7 frozen ops tests passed ==="
