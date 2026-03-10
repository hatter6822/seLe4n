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

/-!
# Simulation Platform Binding

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

/-- Simulation machine configuration: idealized 64-bit ARM64 parameters. -/
def simMachineConfig : SeLe4n.MachineConfig :=
  {
    registerWidth := 64
    virtualAddressWidth := 48
    physicalAddressWidth := 52
    pageSize := 4096
    maxASID := 65536
    memoryMap := [
      { base := SeLe4n.PAddr.ofNat 0
        size := 256 * 1024 * 1024  -- 256 MiB
        kind := .ram }
    ]
  }

/-- The simulation platform binding instance. -/
instance simPlatformBinding : SeLe4n.Platform.PlatformBinding SimPlatform where
  name := "Simulation (permissive)"
  machineConfig := simMachineConfig
  runtimeContract := simRuntimeContractPermissive
  bootContract := simBootContract
  interruptContract := simInterruptContract

end SeLe4n.Platform.Sim
