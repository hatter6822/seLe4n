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
# The yield route's arm, out of line

The routed entry's `.yield` arm (`syscallEntryCheckedK`) as its own function:
the state owned, and the result is the state with its report pushed
(`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The yield arm**: `yieldOnCoreR` on the executing core, its result
reported under the entry's first continuation. -/
@[noinline] def yieldRoutedArm (executingCore : Concurrency.CoreId) (st : SystemState) :
    SystemState :=
  entryReportGeneral (match yieldOnCoreR st executingCore with
    | .error r => .error r
    | .ok st' => .ok ((), st'))

end SeLe4n.Kernel
