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
# The decoded route's arm, out of line

The routed entry's `.viaDecode` arm (`syscallEntryCheckedK`) as its own
function: every call the register file does not route takes the
specification's decode and dispatch (`syscallEntryChecked`), refusing in the
state it was handed (`RefusalCarrying.ofKernel`); the state owned, and the
result is the state with its report pushed (`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The decoded arm**: the checked entry on the hardware's register layout,
its result reported under the entry's first continuation. -/
@[noinline] def decodedRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  entryReportGeneral
    (RefusalCarrying.ofKernel (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)

end SeLe4n.Kernel
