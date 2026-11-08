-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report

/-!
# The overflowed route's arm, out of line

The routed entry's `.overflowed` arm (`syscallEntryCheckedK`): a signal, a wait
or a receive whose message runs past the inline words, every overflow word of
which sits on the page of the caller's IPC buffer that holds slot 0, as its own
function.  Slot 0 read, the call is dispatched as its short route is, on the
state with this core's TLB holding the buffer's translation, a refusal handing
back the TLB the entry held; one whose overflow words cross a page takes the
specification's decode and dispatch.  The syscall, the operand's address and
the message length cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The overflowed dispatch as it runs: the short route's operand dispatch for
the signal, the wait and the receive (`overflowedOperandR_eq`). -/
@[inline] def overflowedOperandR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  match sid with
  | .notificationSignal =>
    dispatchOperandCheckedR capAddr tid executingCore
      (signalOperandArmThenTaintR ctx (.ok { badge := Badge.ofWord (readRegWord rf ⟨2⟩) }) tid
        executingCore (syscallRequiredRight .notificationSignal))
  | .notificationWait =>
    dispatchOperandCheckedR capAddr tid executingCore
      (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))
  | .receive =>
    dispatchOperandCheckedR capAddr tid executingCore
      (receiveOperandArmThenTaintR ctx tid len (SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩))
        executingCore (syscallRequiredRight .receive))
  | _ => fun st => .error (.illegalState, st)

theorem overflowedOperandR_eq (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    overflowedOperandR ctx sid capAddr rf len tid executingCore =
      dispatchOverflowedCheckedR ctx sid capAddr rf len tid executingCore := by
  cases sid <;> rfl

/-- **The overflowed arm**: slot 0 read, then the short route's operand dispatch
on the state whose TLB holds the buffer's translation, a refusal handing back
the TLB the entry held; a call whose overflow words cross a page takes the
checked entry.  Its result reported under the entry's first continuation. -/
@[noinline] def overflowedRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (length : Nat)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    if SeLe4n.Kernel.Architecture.overflowSlotsOnFirstPage tcb.ipcBuffer 0 (length - 4) then
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun _ => entryReportGeneral (
          if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid then
            overflowedOperandR ctx sid (SeLe4n.CPtr.ofWord capWord) tcb.registerContext length tid
              executingCore st
          else
            let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
            match overflowedOperandR ctx sid (SeLe4n.CPtr.ofWord capWord) tcb.registerContext
                length tid executingCore
                (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) with
            | .error (e, stF) =>
              .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
            | .ok r => .ok r))
    else
      entryReportGeneral (RefusalCarrying.ofKernel
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
