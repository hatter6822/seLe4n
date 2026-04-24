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

**AN7-C (H-16) audit note**: the permissive contract's three predicates all
return `True` unconditionally; this is an INTENTIONAL "accept-all" harness
and is not a silent-true pathology in the same class as the AK9-E hole it
pre-dates.  It is namespaced under `Platform.Sim` precisely so production
code cannot accidentally import it.  The substantive contract
(`simRuntimeContractSubstantive`) replaces the permissive register-context
check with the `False` predicate and gates memory access through the
`simSubstantiveMemoryMap.any` bounds, mirroring the RPi5 contract's
structure.
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

/-- S5-D: Simulation memory map — single 256 MiB RAM region at physical address 0.
    Used by the substantive runtime contract (below) and referenced by
    `simMachineConfig.memoryMap` in `Platform/Sim/Contract.lean` via
    the compile-time consistency theorem `simSubstantiveMemoryMap_eq_machineConfig`.

    U8-A/U-L16: This definition is the single source of truth for the
    simulation memory map. `simMachineConfig` in `Contract.lean` must use
    this exact value. The consistency theorem in `Contract.lean` enforces
    this at compile time. -/
def simSubstantiveMemoryMap : List SeLe4n.MemoryRegion :=
  [ { base := SeLe4n.PAddr.ofNat 0
      size := 256 * 1024 * 1024  -- 256 MiB
      kind := .ram } ]

/-- S5-D: Substantive simulation runtime contract mirroring the RPi5 contract
    structure with simulation-appropriate bounds. This replaces the all-False
    restrictive contract for non-trivial validation:

    - **Timer monotonicity**: ARM Generic Timer semantics — CNTPCT_EL0 is
      monotonically non-decreasing (same predicate as RPi5 production).
    - **Register context stability**: Denied (same as RPi5 restrictive). Needed
      because `contextMatchesCurrent` requires full register-file equality, and
      arbitrary register writes break this invariant.
    - **Memory access**: Restricted to declared RAM regions in the simulation
      memory map using the same `memoryMap.any` pattern as RPi5. The simulation
      declares a single 256 MiB RAM region at PA 0.

    This contract enables substantive preservation proofs: timer advancement is
    validated (not vacuously true), and memory reads are checked against bounds. -/
def simRuntimeContractSubstantive : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ addr =>
      -- S5-D: Same memoryMap.any pattern as RPi5 (rpi5RuntimeContract line 58-60).
      simSubstantiveMemoryMap.any fun region =>
        region.kind == .ram && region.contains addr
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; infer_instance
    memoryAccessAllowedDecidable := by
      intro _ addr
      simp only [simSubstantiveMemoryMap]
      infer_instance
  }

end SeLe4n.Platform.Sim
