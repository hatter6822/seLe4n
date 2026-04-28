-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Contract
import SeLe4n.Platform.Sim.RuntimeContract
import SeLe4n.Platform.Sim.BootContract
import SeLe4n.Platform.Sim.ProofHooks

/-!
# Simulation Platform Binding

> **STATUS: production binding** (typeclass instance reachable from
> `SeLe4n.lean`).  The simulation `PlatformBinding` instance composed
> here is in the production import chain; the substantive simulation
> path is exercised by `SeLe4n.Testing.MainTraceHarness` and the test
> tier suites.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation
> roadmap.

Composed `PlatformBinding` instance for the simulation target. This is the
platform used by trace harnesses, negative-state suites, and development
testing. It bundles permissive runtime contracts with trivially-true boot
and interrupt contracts.

## Machine configuration

The simulation platform declares an idealized 64-bit machine with:
- 64-bit registers and 48-bit virtual / 52-bit physical addressing
- 4 KiB pages
- 16-bit ASID space (65536 entries)
- A single 256 MiB RAM region starting at physical address 0

These values match common ARM64 defaults and enable the trace harness to
exercise scheduler, IPC, and VSpace paths without hitting artificial bounds.
-/

namespace SeLe4n.Platform.Sim

/-- Marker type for the simulation platform. -/
structure SimPlatform where
  deriving Repr

/-- Simulation machine configuration: idealized 64-bit ARM64 parameters.
    U8-A/U-L16: Memory map uses the shared `simSubstantiveMemoryMap` definition
    from `RuntimeContract.lean` to eliminate duplication.
    AJ-L11: `physicalAddressWidth := 52` intentionally diverges from RPi5's
    44-bit PA width (Board.lean:122). The simulation platform uses the maximum
    ARMv8-A PA width to avoid false negatives in address validation tests.
    RPi5-specific PA bounds checking uses `Board.bcm2712PhysicalAddressWidth`
    (44 bits) via the RPi5 platform contract. -/
def simMachineConfig : SeLe4n.MachineConfig :=
  {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := 52
    pageSize := 4096
    maxASID := 65536
    memoryMap := simSubstantiveMemoryMap
  }

/-- The simulation platform binding instance. -/
instance simPlatformBinding : SeLe4n.Platform.PlatformBinding SimPlatform where
  name := "Simulation (permissive)"
  machineConfig := simMachineConfig
  runtimeContract := simRuntimeContractPermissive
  bootContract := simBootContract
  interruptContract := simInterruptContract

/-- S5-D: Marker type for the simulation restrictive (substantive) platform. -/
structure SimRestrictivePlatform where
  deriving Repr

/-- S5-D: Simulation restrictive platform binding with substantive contracts.

Uses `simRuntimeContractSubstantive` which mirrors RPi5 contract structure:
- Timer monotonicity validated (substantive, not vacuous)
- Memory access restricted to 256 MiB RAM region
- Register writes denied (enables proof hooks)

This platform variant catches contract-level bugs in simulation that would
otherwise only surface on hardware. Test harnesses using this binding exercise
the same contract validation logic as the RPi5 production platform. -/
instance simRestrictivePlatformBinding :
    SeLe4n.Platform.PlatformBinding SimRestrictivePlatform where
  name := "Simulation (substantive-restrictive)"
  machineConfig := simMachineConfig
  runtimeContract := simRuntimeContractSubstantive
  bootContract := simBootContract
  interruptContract := simInterruptContract

/-- U8-A/U-L16: Compile-time consistency theorem proving that the
    `simSubstantiveMemoryMap` used in `RuntimeContract.lean` is identical to
    `simMachineConfig.memoryMap`. This eliminates the risk of the two memory
    map definitions drifting out of sync — any change to either side will
    cause this proof to fail at build time. -/
theorem simSubstantiveMemoryMap_eq_machineConfig :
    simSubstantiveMemoryMap = simMachineConfig.memoryMap := by rfl

end SeLe4n.Platform.Sim
