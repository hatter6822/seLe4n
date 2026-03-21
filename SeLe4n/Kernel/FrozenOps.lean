/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.FrozenOps.Core
import SeLe4n.Kernel.FrozenOps.Operations
import SeLe4n.Kernel.FrozenOps.Commutativity
import SeLe4n.Kernel.FrozenOps.Invariant

/-!
# Q7: Frozen Kernel Operations — Re-export Hub

Thin import hub for the Q7 frozen kernel operations subsystem.

## Submodules

- `Core.lean`: FrozenKernel monad, lookup/store primitives
- `Operations.lean`: 12 per-subsystem frozen operations
- `Commutativity.lean`: FrozenMap set/get? roundtrip proofs
- `Invariant.lean`: Frame lemmas (frozenStoreObject preservation)
-/
