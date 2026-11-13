-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report
import SeLe4n.Kernel.RoutedArms.ReplyRecv

/-!
# The long reply-receive route's arm, out of line

The routed entry's `.replyRecvLong` arm (`syscallEntryCheckedK`): a
reply-receive of more than the inline words, as its own function, read and
filled as the long reply's (`replyRecvLongRoutedArm`): slot 0 and the next
page's first slot read, the reply-receive dispatched through its long arm
(`replyRecvLongOperandArmThenTaintR`) on the state with this core's TLB holding
the buffer's translations, a refusal handing back the TLB the entry held.  The
replier's TCB is read here, off the state the arm is handed.

An overflow slot that does not read clamps the message to its four inline
words, as seL4's `handleInvocation` clamps a message with no IPC buffer, and
the short route's arm runs on it (`replyRecvRoutedArm`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The long reply-receive arm**: slot 0 and the next page's first slot read, then the
reply-receive's operand dispatch on the state whose TLB holds the buffer's
translations, a refusal handing back the TLB the entry held; a refusal reported
under the entry's resolved or lookup continuation as the dispatch told them
apart, a result under the first. -/
@[noinline] def replyRecvLongRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length extraCaps label : Nat) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => replyRecvRoutedArm ctx executingCore tid capWord 4 extraCaps label st)
        (fun _ =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => replyRecvRoutedArm ctx executingCore tid capWord 4 extraCaps label st)
            (fun _ => longOperandKW .replyRecv (SeLe4n.CPtr.ofWord capWord) tid executingCore
                  (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext length extraCaps label tid
                    executingCore (syscallRequiredRight .replyRecv))
                  (length - 4) st entryReportGeneral (entryReportPushOk 1) (entryReportPushErrorW 1)
                  entryReportLookup entryReportLookupW))
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
