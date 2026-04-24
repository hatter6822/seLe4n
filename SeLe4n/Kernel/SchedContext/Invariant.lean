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

## AN5-D (SC-M03) — DO NOT IMPORT PRESERVATION HERE

**Import-cycle banner.** `Preservation.lean` (Z5 per-operation preservation)
and `PriorityPreservation.lean` (D2 transport lemmas, authority bounds)
MUST NOT be imported from this hub. See WS-AB.D2 for the original
import-cycle analysis. Breaking this rule introduces a cycle because:

* This hub (`SchedContext.Invariant`) is transitively imported by
  `Object/Types.lean` via `SchedContext.lean`.
* Both `Preservation.lean` and `PriorityPreservation.lean` depend on
  `Operations.lean`, which itself depends on `Model.State`, which
  transitively depends on `Object/Types.lean`.

The preservation theorems are therefore integrated via
`CrossSubsystem.lean`, which sits downstream of the cycle boundary and
is the natural home for cross-subsystem preservation-theorem
composition. If you find yourself wanting to import them here, stop —
the right fix is to lift the consumer downstream of `CrossSubsystem.lean`.

**Compile-time guard (AN5-D)**: the `example` below re-derives
`SchedContextInvariant` from `Defs.lean` so any future commit that
accidentally removes the `import SeLe4n.Kernel.SchedContext.Invariant.Defs`
line fails to build. A companion guard at `CrossSubsystem.lean` ensures
the preservation surface remains reachable through that module.
-/

/-- AN5-D (SC-M03): Compile-time import-cycle guard.

This `example` block references the canonical `schedContextWellFormed`
predicate from `Invariant/Defs.lean`. If a future commit removes the
import line or renames the target predicate, this block fails to
elaborate — catching regressions at build time. -/
example (sc : SeLe4n.Kernel.SchedContext) (_hWf : SeLe4n.Kernel.schedContextWellFormed sc) :
    SeLe4n.Kernel.schedContextWellFormed sc := _hWf
