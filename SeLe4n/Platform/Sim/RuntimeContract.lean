/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Assumptions

/-!
# Simulation Platform — Runtime Contracts

Simulation-target runtime boundary contracts for trace harness execution and
testing. These mirror the fixtures in `SeLe4n.Testing.RuntimeContractFixtures`
but are organized under the `Platform.Sim` namespace as part of the H3-prep
platform-binding architecture.

**Non-production:** These contracts are intentionally broad (accept-all) or
intentionally restrictive (deny-all) for testing purposes. They MUST NOT be
used by production kernel modules under `SeLe4n/Kernel/`.
-/

namespace SeLe4n.Platform.Sim

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- Permissive runtime contract that accepts all timer, register, and memory operations.
    Used for success-path testing in trace harnesses. -/
def simRuntimeContractPermissive : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => True
    memoryAccessAllowed := fun _ _ => True
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; infer_instance
    memoryAccessAllowedDecidable := by intro st addr; infer_instance
  }

/-- Restrictive runtime contract that denies all runtime operations.
    Used for error-path testing in trace harnesses. -/
def simRuntimeContractRestrictive : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun _ _ => False
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ _ => False
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; infer_instance
    memoryAccessAllowedDecidable := by intro st addr; infer_instance
  }

end SeLe4n.Platform.Sim
