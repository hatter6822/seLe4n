-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.Predicate
import SeLe4n.Kernel.SlotConfinement.Legs
import SeLe4n.Kernel.SlotConfinement.IpcArms
import SeLe4n.Kernel.SlotConfinement.SchedContextArms
import SeLe4n.Kernel.SlotConfinement.PriorityArms
import SeLe4n.Kernel.SlotConfinement.MemoryArms

/-!
# Per-core slot confinement

Import hub.  `Predicate.lean` defines `observableSlotsConfinedToCores`; the
other five modules bound every transition the syscall seam declares a lock
footprint for by a write set computed from the pre-state, in the order the
arms compose (`Legs` → `IpcArms` → `SchedContextArms` → `PriorityArms` →
`MemoryArms`).  `SyscallSchedContainment.lean` turns each `*_confinedToCores`
theorem into coverage of the arm's declared footprint
(`footprintCoversWrites_of_confined`); the staged
`InformationFlow/NonInterferenceCrossCore.lean` turns each into the
non-interference statement for a remote observer.
-/
