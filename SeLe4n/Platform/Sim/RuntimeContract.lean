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

/-- S5-D: Substantive simulation runtime contract mirroring the RPi5 contract
    structure with simulation-appropriate bounds. This replaces the all-False
    restrictive contract for non-trivial validation:

    - **Timer monotonicity**: ARM Generic Timer semantics — CNTPCT_EL0 is
      monotonically non-decreasing (same predicate as RPi5 production).
    - **Register context stability**: Denied (same as RPi5 restrictive). Needed
      because `contextMatchesCurrent` requires full register-file equality, and
      arbitrary register writes break this invariant.
    - **Memory access**: Restricted to the simulation RAM region (0x0 to 256 MiB).
      Mirrors RPi5's `memoryMap.any (kind == .ram && contains addr)` pattern
      using `simMachineConfig`'s single 256 MiB RAM region.

    This contract enables substantive preservation proofs: timer advancement is
    validated (not vacuously true), and memory reads are checked against bounds. -/
def simRuntimeContractSubstantive : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ addr =>
      -- S5-D: Restrict memory access to the simulation RAM region (0 to 256 MiB).
      -- Mirrors RPi5's memoryMap-based predicate using inline region bounds.
      addr.toNat < 256 * 1024 * 1024
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; infer_instance
    memoryAccessAllowedDecidable := by intro _ addr; infer_instance
  }

end SeLe4n.Platform.Sim
