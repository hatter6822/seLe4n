-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report
import SeLe4n.Kernel.RoutedArms.Reply

/-!
# The long-reply route's arm, out of line

The routed entry's `.replyLong` arm (`syscallEntryCheckedK`): a reply of more
than the inline words, as its own function, read and filled as the long send's
(`replyLongRoutedArm`).  Its overflow words lie on the
page of the replier's IPC buffer that holds slot 0 and at most the next
(`firstPageSlots`): slot 0 and the next page's first slot read (slot 0 again
when the words fit one page), the reply is dispatched through the long reply's arm
(`replyLongOperandArmThenTaintR`) on the state with this core's TLB holding the
buffer's translations, a refusal handing back the TLB the entry held.  The
operand's address and the
message info's fields cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).  The replier's TCB is read here,
off the state the arm is handed, rather than crossing the call.

An overflow slot that does not read clamps the message to its four inline
words, as seL4's `handleInvocation` clamps a message with no IPC buffer, and
the short route's arm runs on it (`replyRoutedArm`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The long-reply arm**: slot 0 and the next page's first slot read, then the
reply's operand dispatch on the state whose TLB holds the buffer's
translations, a refusal handing back the TLB the entry held; a refusal reported
under the entry's resolved or lookup continuation as the dispatch told them
apart, a result under the first. -/
@[noinline] def replyLongRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length extraCaps label : Nat) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => replyRoutedArm ctx executingCore tid capWord 4 extraCaps label st)
        (fun _ =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => replyRoutedArm ctx executingCore tid capWord 4 extraCaps label st)
            (fun _ => longOperandKW .reply (SeLe4n.CPtr.ofWord capWord) tid executingCore
                  (replyLongOperandArmThenTaintR ctx tcb.registerContext length extraCaps label tid
                    executingCore (syscallRequiredRight .reply))
                  (length - 4) st entryReportGeneral (entryReportPushOk 1) (entryReportPushErrorW 1)
                  entryReportLookup entryReportLookupW))
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
