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
# The one-overflow-word route's arm, out of line

The routed entry's `.overflowOne` arm (`syscallEntryCheckedK`): a
scheduling-context configure, a service register or a CNode mint, its fifth
word read from overflow slot 0 of the caller's IPC buffer, as its own function.  The syscall
and the operand's address cross as words, the state owned, and the result is
the state with its report pushed (`RoutedArms.Report`); the read, the TLB
fill and its undo are the entry's own.
The caller's saved register file is read here, off the state the arm is
handed, rather than crossing the call: passed in, it would be held across the
whole arm by the entry's reference, and every write to it the arm makes would
copy it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The short-arguments arm**: `dispatchOperandCheckedK` on the operand and the
refusal of a five-word invocation short of its fifth word
(`shortArgsOperandArmR`), its results reported.  The `.shortArgs` route runs
it, and so does a five-word invocation whose overflow slot does not read: its
message clamped to the inline words, as seL4's `handleInvocation` clamps a
message with no IPC buffer, it is short of its fifth argument. -/
@[noinline] def shortArgsRoutedArm (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (sid : SyscallId) (capWord : UInt64) (st : SystemState) : SystemState :=
  dispatchOperandCheckedK sid (SeLe4n.CPtr.ofWord capWord) tid executingCore
    (shortArgsOperandArmR sid) st entryReportGeneral entryReportResolved entryReportLookup

/-- **The one-overflow-word arm**: the overflow word read, then
`dispatchOverflowOneCheckedR` on the state with this core's TLB holding the
buffer's translation, a refusal handing back the TLB the entry held; its
refusal reported under the entry's resolved or lookup continuation as the
dispatch told them apart, a result under the first. -/
@[noinline] def overflowOneRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
      (fun _ => shortArgsRoutedArm executingCore tid sid capWord st)
      (fun w => overflowOneOperandK sid (SeLe4n.CPtr.ofWord capWord) tid executingCore
        (overflowOneOperandArmR ctx sid tcb.registerContext w tid) st entryReportGeneral
        entryReportResolved entryReportLookup)
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
