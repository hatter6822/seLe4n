-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report
import SeLe4n.Kernel.RoutedArms.Call

/-!
# The long-call route's arm, out of line

The routed entry's `.callLong` arm (`syscallEntryCheckedK`): a call of more
than the inline words, as its own function, read and filled as the long send's
(`callLongRoutedArm`).  Its overflow words lie on the
page of the caller's IPC buffer that holds slot 0 and at most the next
(`firstPageSlots`): slot 0 and the next page's first slot read (slot 0 again
when the words fit one page), the call is dispatched through the long call's arm
(`callLongOperandArmThenTaintR`) on the state with this core's TLB holding the
buffer's translations, a refusal handing back the TLB the entry held.  The
operand's address and the
message length cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).  The caller's TCB is read here,
off the state the arm is handed, rather than crossing the call.

An overflow slot that does not read clamps the message to its four inline
words, as seL4's `handleInvocation` clamps a message with no IPC buffer, and
the short route's arm runs on it (`callRoutedArm`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The long-call arm**: slot 0 and the next page's first slot read, then the
call's operand dispatch on the state whose TLB holds the buffer's
translations, a refusal handing back the TLB the entry held; a refusal reported
under the entry's resolved or lookup continuation as the dispatch told them
apart, a result under the first. -/
@[noinline] def callLongRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length : Nat) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => callRoutedArm ctx executingCore tid capWord 4 st)
        (fun _ =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => callRoutedArm ctx executingCore tid capWord 4 st)
            (fun _ => longOperandK .call (SeLe4n.CPtr.ofWord capWord) tid executingCore
                  (callLongOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                    length tid executingCore (syscallRequiredRight .call))
                  (length - 4) st entryReportGeneral entryReportResolved entryReportLookup))
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
