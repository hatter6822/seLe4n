/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Compute
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Preservation
import SeLe4n.Kernel.Scheduler.PriorityInheritance.BoundedInversion

/-! # D4: Priority Inheritance Protocol — Re-export Hub

Re-exports all PIP submodules for convenient import:
- `BlockingGraph`: Blocking relation, chain walk, acyclicity, depth bound
- `Compute`: `computeMaxWaiterPriority`
- `Propagate`: `updatePipBoost`, `propagatePriorityInheritance`, `revertPriorityInheritance`
- `Preservation`: Frame lemmas for scheduler, IPC, and cross-subsystem invariants
- `BoundedInversion`: Parametric WCRT bound, determinism -/
