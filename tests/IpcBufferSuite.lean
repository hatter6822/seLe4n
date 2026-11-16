-- SPDX-License-Identifier: GPL-3.0-or-later
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

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture.IpcBufferValidation
open SeLe4n.Kernel.FrozenOps

/-! # IPC buffer configuration (`seL4_TCB_SetIPCBuffer`)

WS-SX SX6.6: the buffer's frame capability is extra capability 0, resolved as a
slot through the caller's CSpace, as in seL4 MCS's `decodeSetIPCBuffer`.  A
nonzero address must name a non-device frame capability (seL4_IllegalOperation
otherwise) and be aligned (seL4_AlignmentError); the derived capability replaces
the thread's buffer slot with a copy edge, and the thread need not be suspended.
A zero address empties the slot. -/

namespace SeLe4n.Testing.IpcBufferSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"ipc_buffer check passed [{label}]"
  else
    throw <| IO.userError s!"ipc_buffer check failed [{label}]"

/-- The caller's CSpace root: CNode 10, radix 3, behind a 61-bit guard so a
64-bit CPtr names its slot by its low three bits. -/
private def rootCap : Capability :=
  { target := .object ⟨10⟩, rights := AccessRightSet.ofList [.read, .write, .grant],
    cnodeGuardSize := 61 }

private def frameCap (id : Nat) : Capability :=
  { target := .object ⟨id⟩, rights := AccessRightSet.ofList [.read, .write] }

/-- A thread whose CSpace root is `rootCap` and VSpace root is object 100. -/
private def mkTcb (tid : Nat) (state : ThreadState := .Ready)
    (bufferSlot : Option Capability := none) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨10⟩, domain := ⟨0⟩,
    spaceCells := #v[some rootCap,
      TCB.spaceCellOf ⟨100⟩ TCB.vspaceRootRights, bufferSlot],
    ipcBuffer := SeLe4n.VAddr.ofNat 0, threadState := state }

/-- CNode 10's slots: 3 a frame, 4 a device frame, 5 an endpoint, 6 empty. -/
private def rootCNode : CNode :=
  CNode.ofList 3
    [(SeLe4n.Slot.ofNat 3, frameCap 50),
     (SeLe4n.Slot.ofNat 4, frameCap 51),
     (SeLe4n.Slot.ofNat 5, { target := .object ⟨60⟩, rights := AccessRightSet.ofList [.read] })]

private def mkState (objs : List (ObjId × KernelObject))
    (current : Option SeLe4n.ThreadId := none) : SystemState :=
  let builder : SeLe4n.Testing.BootstrapBuilder := {
    objects := objs ++
      [(⟨10⟩, .cnode rootCNode),
       (⟨50⟩, .frame { base := SeLe4n.PAddr.ofNat 0x10000 }),
       (⟨51⟩, .frame { base := SeLe4n.PAddr.ofNat 0x20000, isDevice := true }),
       (⟨60⟩, .endpoint {}),
       (⟨100⟩, .vspaceRoot { asid := ⟨1⟩, mappings := {} })]
    current := current
  }
  builder.buildChecked

private def vtid2 : SeLe4n.ValidThreadId := ⟨⟨2⟩, by decide⟩

private def setBuffer (st : SystemState) (cap? : Option Nat) (addr : Nat) :
    Except KernelError SystemState :=
  setIPCBufferOp SeLe4n.Kernel.Concurrency.bootCoreId st vtid2 ⟨1⟩ (cap?.map SeLe4n.CPtr.ofNat) (SeLe4n.VAddr.ofNat addr)

private def twoThreads (state : ThreadState := .Ready) (current : Option SeLe4n.ThreadId := none)
    (bufferSlot : Option Capability := none) : SystemState :=
  mkState [(⟨1⟩, .tcb (mkTcb 1)), (⟨2⟩, .tcb (mkTcb 2 state bufferSlot))] current

private def slotTarget (st : SystemState) : Option CapTarget :=
  (st.getTcb? ⟨2⟩).bind (fun t => t.spaceCells[2].map (·.target))

private def bufferAddr (st : SystemState) : Option Nat :=
  (st.getTcb? ⟨2⟩).map (·.ipcBuffer.toNat)

-- ============================================================================
-- Admitted changes
-- ============================================================================

/-- IB-001: an aligned address with a frame capability installs the derived
capability in the buffer slot and writes the address. -/
private def ib001_frameCapInstalled : IO Unit := do
  match setBuffer (twoThreads) (some 3) 1024 with
  | .ok st' =>
    expect "ipcBuffer written" (bufferAddr st' == some 1024)
    expect "buffer slot holds the frame" (slotTarget st' == some (.object ⟨50⟩))
    expect "the source keeps its capability"
      ((st'.getCNode? ⟨10⟩).bind (·.lookup (SeLe4n.Slot.ofNat 3)) |>.isSome)
  | .error e => throw <| IO.userError s!"set with a frame capability must succeed, got {repr e}"

/-- IB-002: a zero address empties the buffer slot, even when the extra
capability names no frame (seL4's null capability). -/
private def ib002_zeroAddressEmptiesSlot : IO Unit := do
  match setBuffer (twoThreads (bufferSlot := some (frameCap 50))) (some 6) 0 with
  | .ok st' =>
    expect "ipcBuffer zero" (bufferAddr st' == some 0)
    expect "buffer slot emptied" (slotTarget st' == none)
  | .error e => throw <| IO.userError s!"a zero address must succeed, got {repr e}"

/-- IB-003: the thread need not be suspended. -/
private def ib003_runningThread : IO Unit := do
  match setBuffer (twoThreads (state := .Running) (current := some ⟨2⟩)) (some 3) 2048 with
  | .ok st' => expect "set on a running thread succeeds" (bufferAddr st' == some 2048)
  | .error e => throw <| IO.userError s!"must succeed on a running thread, got {repr e}"

/-- IB-004: a second set replaces the slot's earlier capability. -/
private def ib004_replacesEarlierCap : IO Unit := do
  match setBuffer (twoThreads (bufferSlot := some (frameCap 50))) (some 3) 3072 with
  | .ok st' =>
    expect "replaced address" (bufferAddr st' == some 3072)
    expect "slot still names the frame" (slotTarget st' == some (.object ⟨50⟩))
  | .error e => throw <| IO.userError s!"a replacing set must succeed, got {repr e}"

-- ============================================================================
-- Refusals, in seL4's order
-- ============================================================================

private def expectErr (label : String) (r : Except KernelError SystemState)
    (ok : KernelError → Bool) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"ipc_buffer check failed [{label}]: admitted"
  | .error e => expect s!"{label} ({repr e})" (ok e)

/-- IB-005: no extra capability is a truncated message. -/
private def ib005_noExtraCap : IO Unit :=
  expectErr "no extra capability" (setBuffer twoThreads none 1024) (· == .truncatedMessage)

/-- IB-006: an extra capability the caller's CSpace cannot resolve is a lookup
failure. -/
private def ib006_lookupFails : IO Unit := do
  let st := mkState [(⟨1⟩, .tcb { mkTcb 1 with spaceCells := #v[none, none, none] }),
    (⟨2⟩, .tcb (mkTcb 2))]
  expectErr "unresolvable extra capability" (setBuffer st (some 3) 1024)
    (fun e => match e with | .failedLookup _ _ => true | _ => false)

/-- IB-007: an empty slot, an endpoint and a device frame are each seL4's
IllegalOperation for a nonzero address. -/
private def ib007_notAFrame : IO Unit := do
  expectErr "empty slot" (setBuffer twoThreads (some 6) 1024) (· == .illegalState)
  expectErr "endpoint capability" (setBuffer twoThreads (some 5) 1024) (· == .illegalState)
  expectErr "device frame" (setBuffer twoThreads (some 4) 1024) (· == .illegalState)

/-- IB-008: a misaligned address is an alignment error, checked after the
capability. -/
private def ib008_misaligned : IO Unit := do
  expectErr "misaligned" (setBuffer twoThreads (some 3) 100) (· == .alignmentError)
  -- 512-aligned but not 1024-aligned: a buffer there could cross its page.
  expectErr "512-aligned" (setBuffer twoThreads (some 3) 0xE00) (· == .alignmentError)
  expectErr "misaligned with no frame is IllegalOperation first"
    (setBuffer twoThreads (some 6) 100) (· == .illegalState)

/-- IB-009: a missing target thread is objectNotFound. -/
private def ib009_missingThread : IO Unit :=
  expectErr "missing thread" (setBuffer (mkState [(⟨1⟩, .tcb (mkTcb 1))]) (some 3) 1024)
    (· == .objectNotFound)

-- ============================================================================
-- Field preservation and the frozen phase
-- ============================================================================

/-- IB-010: the set keeps every other field of the thread. -/
private def ib010_fieldPreservation : IO Unit := do
  let st := twoThreads
  match setBuffer st (some 3) 1024, st.getTcb? ⟨2⟩ with
  | .ok st', some orig =>
    match st'.getTcb? ⟨2⟩ with
    | some t =>
      expect "priority preserved" (t.priority == orig.priority)
      expect "domain preserved" (t.domain == orig.domain)
      expect "vspaceRoot preserved" (t.vspaceRoot == orig.vspaceRoot)
      expect "cspaceRoot preserved" (t.cspaceRoot == orig.cspaceRoot)
      expect "threadState preserved" (t.threadState == orig.threadState)
      expect "ipcState preserved" (t.ipcState == orig.ipcState)
    | none => throw <| IO.userError "TCB not found"
  | _, _ => throw <| IO.userError "the set must succeed"

/-- IB-011: the frozen phase has no buffer set: it would write the derivation
tree, which the frozen phase does not model. -/
private def ib011_noFrozenSet : IO Unit :=
  expect "tcbSetIPCBuffer has no frozen operation" (frozenOpCoverage .tcbSetIPCBuffer == false)

end SeLe4n.Testing.IpcBufferSuite

open SeLe4n.Testing.IpcBufferSuite in
def main : IO Unit := do
  IO.println "=== IPC Buffer Configuration Test Suite ==="
  ib001_frameCapInstalled
  ib002_zeroAddressEmptiesSlot
  ib003_runningThread
  ib004_replacesEarlierCap
  ib005_noExtraCap
  ib006_lookupFails
  ib007_notAFrame
  ib008_misaligned
  ib009_missingThread
  ib010_fieldPreservation
  ib011_noFrozenSet
  IO.println "=== All IPC buffer tests passed (11 tests) ==="
