/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Kernel.Architecture.IpcBufferValidation
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture.IpcBufferValidation
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Kernel.RobinHood

namespace SeLe4n.Testing.IpcBufferSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"ipc_buffer check passed [{label}]"
  else
    throw <| IO.userError s!"ipc_buffer check failed [{label}]"

/-- Helper: construct a test TCB with given VSpace root. -/
private def mkTcb (tid : Nat) (vsRoot : Nat := 100)
    (buf : Nat := 0) (state : ThreadState := .Ready) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨10⟩, domain := ⟨0⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨vsRoot⟩, ipcBuffer := ⟨buf⟩,
    threadState := state }

/-- Helper: create writable page permissions. -/
private def writablePerms : PagePermissions :=
  { read := true, write := true, execute := false, user := true, cacheable := true }

/-- Helper: create read-only page permissions. -/
private def readOnlyPerms : PagePermissions :=
  { read := true, write := false, execute := false, user := true, cacheable := true }

/-- Helper: build a VSpaceRoot with given mappings. -/
private def mkVSpaceRoot (mappings : List (VAddr × (PAddr × PagePermissions)))
    (asid : Nat := 1) : VSpaceRoot :=
  let table := mappings.foldl (fun acc (va, entry) => acc.insert va entry) (RHTable.empty 16)
  { asid := ⟨asid⟩, mappings := table }

/-- Helper: build a minimal SystemState with given objects. -/
private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs
    current := current
  }
  builder.build

-- ============================================================================
-- D3-J1: setIPCBufferOp success cases
-- ============================================================================

/-- IB-001: setIPCBuffer with valid aligned mapped writable address succeeds. -/
private def ib001_setIPCBufferValidAddress : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let vsRoot := mkVSpaceRoot [(⟨512⟩, (⟨0x1000⟩, writablePerms))]
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨512⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "IB-001 ipcBuffer updated to 512" (tcb.ipcBuffer == ⟨512⟩)
    | _ => throw <| IO.userError "IB-001 TCB not found after update"
  | .error e => throw <| IO.userError s!"IB-001 setIPCBuffer should succeed, got {repr e}"

/-- IB-002: setIPCBuffer with address 0 (trivially aligned, must be mapped). -/
private def ib002_setIPCBufferZeroAddress : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let vsRoot := mkVSpaceRoot [(⟨0⟩, (⟨0x2000⟩, writablePerms))]
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨0⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      expect "IB-002 ipcBuffer set to 0" (tcb.ipcBuffer == ⟨0⟩)
    | _ => throw <| IO.userError "IB-002 TCB not found"
  | .error e => throw <| IO.userError s!"IB-002 setIPCBuffer at 0 should succeed, got {repr e}"

/-- IB-003: setIPCBuffer on running thread succeeds (no suspend required). -/
private def ib003_setIPCBufferRunningThread : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let vsRoot := mkVSpaceRoot [(⟨1024⟩, (⟨0x3000⟩, writablePerms))]
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1 (state := .Running))),
    (⟨100⟩, .vspaceRoot vsRoot)
  ] (current := some ⟨1⟩)
  match setIPCBufferOp st tid ⟨1024⟩ with
  | .ok _ => expect "IB-003 setIPCBuffer on running thread succeeds" true
  | .error e => throw <| IO.userError s!"IB-003 should succeed on running thread, got {repr e}"

-- ============================================================================
-- D3-J2: setIPCBufferOp error cases
-- ============================================================================

/-- IB-004: Unaligned address returns alignmentError. -/
private def ib004_unalignedAddress : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let vsRoot := mkVSpaceRoot [(⟨100⟩, (⟨0x4000⟩, writablePerms))]
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨100⟩ with
  | .ok _ => throw <| IO.userError "IB-004 unaligned address should fail"
  | .error e => expect "IB-004 unaligned returns alignmentError" (e == .alignmentError)

/-- IB-005: Unmapped address returns translationFault. -/
private def ib005_unmappedAddress : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  -- VSpaceRoot with no mapping at address 512
  let vsRoot := mkVSpaceRoot []
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨512⟩ with
  | .ok _ => throw <| IO.userError "IB-005 unmapped address should fail"
  | .error e => expect "IB-005 unmapped returns translationFault" (e == .translationFault)

/-- IB-006: Address beyond canonical bound returns addressOutOfBounds. -/
private def ib006_addressBeyondCanonical : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let vsRoot := mkVSpaceRoot []
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  -- 2^48 is beyond canonical bound (ARM64 48-bit VA space)
  -- Must also be aligned to 512
  let beyondCanonical := VAddr.canonicalBound
  match setIPCBufferOp st tid ⟨beyondCanonical⟩ with
  | .ok _ => throw <| IO.userError "IB-006 beyond canonical should fail"
  | .error e => expect "IB-006 beyond canonical returns addressOutOfBounds" (e == .addressOutOfBounds)

/-- IB-007: Read-only page returns translationFault. -/
private def ib007_readOnlyPage : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let vsRoot := mkVSpaceRoot [(⟨512⟩, (⟨0x5000⟩, readOnlyPerms))]
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨512⟩ with
  | .ok _ => throw <| IO.userError "IB-007 read-only page should fail"
  | .error e => expect "IB-007 read-only returns translationFault" (e == .translationFault)

/-- IB-008: Missing thread returns objectNotFound. -/
private def ib008_missingThread : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨99⟩  -- nonexistent
  let vsRoot := mkVSpaceRoot [(⟨512⟩, (⟨0x6000⟩, writablePerms))]
  let st := mkState [
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨512⟩ with
  | .ok _ => throw <| IO.userError "IB-008 missing thread should fail"
  | .error e => expect "IB-008 missing thread returns objectNotFound" (e == .objectNotFound)

/-- IB-009: Invalid VSpace root returns invalidArgument. -/
private def ib009_invalidVSpaceRoot : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  -- VSpace root ObjId points to a non-VSpaceRoot object (endpoint)
  let st := mkState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .endpoint {})
  ]
  match setIPCBufferOp st tid ⟨512⟩ with
  | .ok _ => throw <| IO.userError "IB-009 invalid vspace root should fail"
  | .error e => expect "IB-009 invalid vspace returns invalidArgument" (e == .invalidArgument)

-- ============================================================================
-- D3-J3: Field preservation
-- ============================================================================

/-- IB-010: setIPCBuffer preserves all other TCB fields. -/
private def ib010_fieldPreservation : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let origTcb := mkTcb 1 (buf := 0)
  let vsRoot := mkVSpaceRoot [(⟨1024⟩, (⟨0x7000⟩, writablePerms))]
  let st := mkState [
    (⟨1⟩, .tcb origTcb),
    (⟨100⟩, .vspaceRoot vsRoot)
  ]
  match setIPCBufferOp st tid ⟨1024⟩ with
  | .ok st' =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) => do
      expect "IB-010 priority preserved" (tcb.priority == origTcb.priority)
      expect "IB-010 domain preserved" (tcb.domain == origTcb.domain)
      expect "IB-010 vspaceRoot preserved" (tcb.vspaceRoot == origTcb.vspaceRoot)
      expect "IB-010 cspaceRoot preserved" (tcb.cspaceRoot == origTcb.cspaceRoot)
      expect "IB-010 threadState preserved" (tcb.threadState == origTcb.threadState)
      expect "IB-010 ipcState preserved" (tcb.ipcState == origTcb.ipcState)
      expect "IB-010 ipcBuffer updated" (tcb.ipcBuffer == ⟨1024⟩)
    | _ => throw <| IO.userError "IB-010 TCB not found"
  | .error e => throw <| IO.userError s!"IB-010 should succeed, got {repr e}"

-- ============================================================================
-- D3-J4: Frozen operations
-- ============================================================================

/-- Helper: construct a minimal empty FrozenSystemState. -/
private def emptyFrozenState : FrozenSystemState := {
  objects := freezeMap (RHTable.empty 16)
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
    configDefaultTimeSlice := 5
  }
  objectTypes := freezeMap (RHTable.empty 16)
  capabilityRefs := freezeMap (RHTable.empty 16)
  machine := default
  objectIndex := []
  objectIndexSet := freezeMap (RHTable.empty 16)
  tlb := TlbState.empty
}

/-- Helper: build a minimal FrozenSystemState with given objects. -/
private def mkFrozenState (objs : List (ObjId × FrozenKernelObject)) : FrozenSystemState :=
  let rt := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  { emptyFrozenState with objects := freezeMap rt }

/-- Helper: create frozen VSpaceRoot with mappings. -/
private def mkFrozenVSpaceRoot (mappings : List (VAddr × (PAddr × PagePermissions)))
    (asid : Nat := 1) : FrozenVSpaceRoot :=
  let table := mappings.foldl (fun acc (va, entry) => acc.insert va entry) (RHTable.empty 16)
  { asid := ⟨asid⟩, mappings := freezeMap table }

/-- IB-011: Frozen setIPCBuffer with valid address succeeds. -/
private def ib011_frozenSetIPCBuffer : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fvs := mkFrozenVSpaceRoot [(⟨512⟩, (⟨0x8000⟩, writablePerms))]
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot fvs)
  ]
  match frozenSetIPCBuffer tid ⟨512⟩ fst with
  | .ok ((), fst') =>
    match fst'.objects.get? ⟨1⟩ with
    | some (.tcb tcb) =>
      expect "IB-011 frozen ipcBuffer updated" (tcb.ipcBuffer == ⟨512⟩)
    | _ => throw <| IO.userError "IB-011 frozen TCB not found"
  | .error e => throw <| IO.userError s!"IB-011 frozen setIPCBuffer should succeed, got {repr e}"

/-- IB-012: Frozen setIPCBuffer with unaligned address fails. -/
private def ib012_frozenUnaligned : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fvs := mkFrozenVSpaceRoot [(⟨100⟩, (⟨0x9000⟩, writablePerms))]
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot fvs)
  ]
  match frozenSetIPCBuffer tid ⟨100⟩ fst with
  | .ok _ => throw <| IO.userError "IB-012 frozen unaligned should fail"
  | .error e => expect "IB-012 frozen unaligned returns alignmentError" (e == .alignmentError)

/-- IB-013: Frozen setIPCBuffer with read-only page fails. -/
private def ib013_frozenReadOnly : IO Unit := do
  let tid : SeLe4n.ThreadId := ⟨1⟩
  let fvs := mkFrozenVSpaceRoot [(⟨512⟩, (⟨0xA000⟩, readOnlyPerms))]
  let fst := mkFrozenState [
    (⟨1⟩, .tcb (mkTcb 1)),
    (⟨100⟩, .vspaceRoot fvs)
  ]
  match frozenSetIPCBuffer tid ⟨512⟩ fst with
  | .ok _ => throw <| IO.userError "IB-013 frozen read-only should fail"
  | .error e => expect "IB-013 frozen read-only returns translationFault" (e == .translationFault)

end SeLe4n.Testing.IpcBufferSuite

open SeLe4n.Testing.IpcBufferSuite in
def main : IO Unit := do
  IO.println "=== D3 IPC Buffer Configuration Test Suite ==="
  IO.println "--- D3-J1: setIPCBuffer success cases ---"
  ib001_setIPCBufferValidAddress
  ib002_setIPCBufferZeroAddress
  ib003_setIPCBufferRunningThread
  IO.println "--- D3-J2: setIPCBuffer error cases ---"
  ib004_unalignedAddress
  ib005_unmappedAddress
  ib006_addressBeyondCanonical
  ib007_readOnlyPage
  ib008_missingThread
  ib009_invalidVSpaceRoot
  IO.println "--- D3-J3: Field preservation ---"
  ib010_fieldPreservation
  IO.println "--- D3-J4: Frozen operations ---"
  ib011_frozenSetIPCBuffer
  ib012_frozenUnaligned
  ib013_frozenReadOnly
  IO.println "=== All D3 IPC buffer tests passed (13 tests) ==="
