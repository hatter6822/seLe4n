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
# The long-send route's arm, out of line

The routed entry's `.sendLong` arm (`syscallEntryCheckedK`): a send of more
than the inline words, every overflow word of which sits on the page of the
caller's IPC buffer that holds slot 0, as its own function.  Slot 0 read, the
send is dispatched as the short send is (`sendOperandArmThenTaintR`) on the
state with this core's TLB holding the buffer's translation, a refusal handing
back the TLB the entry held; a long send whose overflow words cross a page
takes the specification's decode and dispatch.  The operand's address and the
message length cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).  The caller's TCB is read here,
off the state the arm is handed, rather than crossing the call.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The long-send arm**: slot 0 read, then the send's operand dispatch on the
state whose TLB holds the buffer's translation, a refusal handing back the
TLB the entry held; a send whose overflow words cross a page takes the
checked entry.  Its result reported under the entry's first continuation. -/
@[noinline] def sendLongRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length : Nat) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    if SeLe4n.Kernel.Architecture.overflowSlotsOnFirstPage tcb.ipcBuffer 0 (length - 4) then
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun _ => entryReportGeneral (
          if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid then
            dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
              (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                length tid executingCore (syscallRequiredRight .send)) st
          else
            let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
            match dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
                (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                  length tid executingCore (syscallRequiredRight .send))
                (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) with
            | .error (e, stF) =>
              .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
            | .ok r => .ok r))
    else
      entryReportGeneral (RefusalCarrying.ofKernel
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
