/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RadixTree.Core
import SeLe4n.Kernel.RadixTree.Invariant
import SeLe4n.Kernel.RadixTree.Bridge

/-!
# Q4: CNode Radix Tree — Re-export Hub

Thin re-export module for backward compatibility. All `import SeLe4n.Kernel.RadixTree`
statements bring in core types, operations, invariants, and the builder bridge.

Submodules:
- `Core.lean`: `CNodeRadix` type, `extractBits`, lookup/insert/erase/fold/toList
- `Invariant.lean`: 12 correctness proofs (lookup roundtrip, WF preservation, etc.)
- `Bridge.lean`: `buildCNodeRadix` (RHTable → CNodeRadix), equivalence bridge
-/
