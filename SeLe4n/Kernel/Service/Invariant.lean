/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Invariant.Policy
import SeLe4n.Kernel.Service.Invariant.Acyclicity

/-! # Service Invariant Preservation — Re-export Hub

Decomposed into:
- **Policy**: Policy surface definitions, bridge theorems, service lifecycle
  invariant bundles, and cross-subsystem composition.
- **Acyclicity**: Service dependency acyclicity proofs (TPI-D07), BFS
  completeness bridge, graph traversal, and preservation under registration.
-/
