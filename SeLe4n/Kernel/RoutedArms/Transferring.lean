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
# The capability-carrying send and call route's arm, out of line

The routed entry's `.transferring` arm (`syscallEntryCheckedK`): a send or a
call whose message carries capabilities, as its own function
(`transferringRoutedArm`).  Within the inline words it is the operand
dispatch over the transferring arm (`transferringOperandArmThenTaintR`);
past them, slot 0 and the next page's first slot are read and the dispatch
runs on the state with this core's TLB holding the buffer's translations, a
refusal handing back the TLB the entry held, as the long send's.  The
caller's TCB is read here, off the state the arm is handed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The capability-carrying send or call arm**: the operand dispatch over
the transferring arm, its results reported; past the inline words, read and
filled first as the long send's. -/
@[noinline] def transferringRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (length : Nat)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    if length ≤ 4 then
      dispatchOperandCheckedK (SeLe4n.CPtr.ofWord capWord) tid executingCore
        (transferringOperandArmThenTaintR ctx sid tcb.registerContext length tid executingCore
          (syscallRequiredRight sid))
        st entryReportGeneral entryReportResolved entryReportLookup
    else
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun _ =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
            (fun _ => longOperandK (SeLe4n.CPtr.ofWord capWord) tid executingCore
                  (transferringOperandArmThenTaintR ctx sid tcb.registerContext length tid
                    executingCore (syscallRequiredRight sid))
                  (length - 4) st entryReportGeneral entryReportResolved entryReportLookup))
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
