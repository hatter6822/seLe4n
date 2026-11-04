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
# The wait route's arm, out of line

The routed entry's `.wait` arm (`syscallEntryCheckedK`) as its own function:
the operand's address crosses as a word, the state owned, and the result is
the state with its report pushed (`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The wait arm**: `dispatchOperandCheckedK` on the operand and the wait's
arm and taint step (`waitOperandArmThenTaintR`), its results reported. -/
@[noinline] def waitRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (st : SystemState) : SystemState :=
  dispatchOperandCheckedK (SeLe4n.CPtr.ofWord capWord) tid executingCore
    (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))
    st entryReportGeneral entryReportResolved entryReportLookup

end SeLe4n.Kernel
