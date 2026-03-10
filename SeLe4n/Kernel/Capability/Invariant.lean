/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Defs
import SeLe4n.Kernel.Capability.Invariant.Authority
import SeLe4n.Kernel.Capability.Invariant.Preservation

/-! # Capability Invariant Preservation — Re-export Hub

Decomposed into:
- **Defs**: Core invariant definitions (capabilityInvariantBundle, WS-H4
  transfer theorems, WS-H13 depth consistency, composite path transfers).
- **Authority**: Authority reduction, attenuation proofs, badge/notification
  routing consistency, invariant establishment.
- **Preservation**: Operation preservation (lookup, insert, mint, delete, revoke,
  copy, move, mutate, CDT revocation, lifecycle integration, composed bundles).
-/
