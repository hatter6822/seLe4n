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
# The reply route's arm, out of line

The routed entry's `.reply` arm (`syscallEntryCheckedK`) as its own function:
the operand's address and the message info's length, capability count and
label cross as words, the state owned, and the result is the state with its
report pushed (`RoutedArms.Report`).
The caller's saved register file is read here, off the state the arm is
handed, rather than crossing the call: passed in, it would be held across the
whole arm by the entry's reference, and every write to it the arm makes would
copy it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The reply arm**: `dispatchOperandCheckedK` on the operand and the
reply's arm and taint step (`replyOperandArmThenTaintR`) over the caller's
message registers, its results reported. -/
@[noinline] def replyRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length extraCaps label : Nat)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    dispatchOperandCheckedK (SeLe4n.CPtr.ofWord capWord) tid executingCore
      (replyOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext length
        extraCaps label tid executingCore (syscallRequiredRight .reply))
      st entryReportGeneral entryReportResolved entryReportLookup
  | _ => entryReportGeneral (.error (.illegalState, st))

end SeLe4n.Kernel
