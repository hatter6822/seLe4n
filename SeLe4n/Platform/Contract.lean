/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Assumptions

/-!
# Platform Binding Contract (H3 preparation)

This module defines the `PlatformBinding` typeclass — the formal interface that
any hardware platform must satisfy to instantiate the seLe4n kernel. A platform
binding bundles:

1. **MachineConfig** — architectural constants (register width, page size, ASID
   limits, physical memory map).
2. **RuntimeBoundaryContract** — decidable predicates on timer monotonicity,
   register context stability, and memory access permissions.
3. **BootBoundaryContract** — propositions about initial object-store and
   capability-ref consistency.
4. **InterruptBoundaryContract** — predicates on supported IRQ lines and handler
   mappings.

## Design rationale

The typeclass approach makes platform selection a type parameter rather than a
value parameter. Kernel transitions remain platform-agnostic (they do not
mention any `PlatformBinding` instance). Only architecture-adapter entrypoints
and test harnesses instantiate a concrete platform.

## Current instantiations

- `SeLe4n.Platform.Sim.simPlatformBinding` — simulation target for trace
  harness and test execution. Defines permissive contracts parallel to
  `SeLe4n.Testing.RuntimeContractFixtures` (functionally equivalent but
  organized under the Platform namespace).
- `SeLe4n.Platform.RPi5.rpi5PlatformBinding` — Raspberry Pi 5 (BCM2712/ARM64)
  stub for H3 hardware binding.
-/

namespace SeLe4n.Platform

open SeLe4n.Kernel.Architecture

/-- A complete platform binding bundles all architecture-boundary contracts
    together with the platform's machine configuration.

    Platform implementors provide an instance of this class. Kernel code
    never depends on a specific instance — it is parameterized over the
    typeclass when adapter operations need platform-specific contracts. -/
class PlatformBinding (platform : Type) where
  /-- Platform name used for diagnostics and trace output. -/
  name : String
  /-- Hardware architectural parameters. -/
  machineConfig : SeLe4n.MachineConfig
  /-- Runtime boundary contract governing timer, register, and memory access. -/
  runtimeContract : RuntimeBoundaryContract
  /-- Boot-time boundary contract governing initial state consistency. -/
  bootContract : BootBoundaryContract
  /-- Interrupt routing contract governing IRQ line support and handler mapping. -/
  interruptContract : InterruptBoundaryContract

/-- Extract the runtime contract from a platform binding instance. -/
@[inline] def PlatformBinding.runtime [PlatformBinding platform] : RuntimeBoundaryContract :=
  PlatformBinding.runtimeContract (platform := platform)

/-- Extract the boot contract from a platform binding instance. -/
@[inline] def PlatformBinding.boot [PlatformBinding platform] : BootBoundaryContract :=
  PlatformBinding.bootContract (platform := platform)

/-- Extract the interrupt contract from a platform binding instance. -/
@[inline] def PlatformBinding.interrupt [PlatformBinding platform] : InterruptBoundaryContract :=
  PlatformBinding.interruptContract (platform := platform)

/-- Extract the machine configuration from a platform binding instance. -/
@[inline] def PlatformBinding.config [PlatformBinding platform] : SeLe4n.MachineConfig :=
  PlatformBinding.machineConfig (platform := platform)

end SeLe4n.Platform
