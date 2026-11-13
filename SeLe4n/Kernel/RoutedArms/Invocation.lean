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
# The invocation route's arm, out of line

The routed entry's `.invoke` arm (`syscallEntryCheckedK`): a capability
invocation outside IPC, its arguments in the caller's registers, as its own
function.  The syscall and the operand's address cross as words, the state
owned, and the result is the state with its report pushed
(`RoutedArms.Report`).
The caller's saved register file is read here, off the state the arm is
handed, rather than crossing the call: passed in, it would be held across the
whole arm by the entry's reference, and every write to it the arm makes would
copy it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The invocation arm**: `dispatchOperandCheckedK` on the operand and the
invocation's arm (`invocationOperandArmR`) over the caller's registers, its
results reported, the arm's refusal pushed from its words
(`dispatchOperandCheckedKW`), so a refusal with a payload builds no error. -/
@[noinline] def invocationRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    dispatchOperandCheckedKW sid (SeLe4n.CPtr.ofWord capWord) tid executingCore
      (invocationOperandArmR ctx sid (SeLe4n.CPtr.ofWord capWord) tcb.registerContext tid
        executingCore)
      st entryReportGeneral (entryReportPushOk 1) (entryReportPushErrorW 1) entryReportLookup
      entryReportLookupW
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
