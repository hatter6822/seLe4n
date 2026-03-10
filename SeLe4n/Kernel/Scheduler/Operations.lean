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
