-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Scheduler.Operations.Preservation

/-! # Scheduler Operations — Re-export Hub

This module re-exports all scheduler operation submodules. The implementation
is decomposed into:

- **Selection**: EDF three-level scheduling predicates, comparison proofs,
  thread selection, and context save/restore definitions.
- **Core**: Context save/restore frame lemmas and core scheduler transitions
  (schedule, handleYield, timerTick, switchDomain, scheduleDomain).
- **Preservation**: All scheduler invariant preservation theorems (base bundle,
  domain-awareness, time-slice, EDF, context-matches, full bundle composition).
-/
