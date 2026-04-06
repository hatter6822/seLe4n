/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Invariant.Defs

/-! # SchedContext Invariant — Re-export Hub

Thin re-export hub for SchedContext invariant definitions and proofs.
Follows the project convention of `Invariant.lean` → `Invariant/Defs.lean`.

**Note (AD1/F-01):** `Preservation.lean` (Z5 per-operation preservation) and
`PriorityPreservation.lean` (D2 transport lemmas, authority bounds) are NOT
imported here due to an import-cycle constraint: this hub is transitively
imported by `Object/Types.lean` via `SchedContext.lean`, and both preservation
modules depend on `Operations.lean` → `Model.State` → `Object/Types.lean`.
Instead, they are integrated via `CrossSubsystem.lean`, which sits downstream
of the cycle boundary and is the natural home for cross-subsystem preservation
theorem composition.
-/
