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
# The receive route's arm, out of line

The routed entry's `.receive` arm (`syscallEntryCheckedK`) as its own
function: the operand's address, the message length and the reply object's
address cross as words, the state owned, and the result is the state with its
report pushed (`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The receive arm**: `dispatchOperandCheckedK` on the operand and the
receive's arm and taint step (`receiveOperandArmThenTaintR`), its results
reported. -/
@[noinline] def receiveRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length : Nat) (replyWord : UInt64)
    (st : SystemState) : SystemState :=
  dispatchOperandCheckedK (SeLe4n.CPtr.ofWord capWord) tid executingCore
    (receiveOperandArmThenTaintR ctx tid length (SeLe4n.CPtr.ofWord replyWord) executingCore
      (syscallRequiredRight .receive))
    st entryReportGeneral entryReportResolved entryReportLookup

end SeLe4n.Kernel
