/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Contract
import SeLe4n.Platform.RPi5.RuntimeContract
import SeLe4n.Platform.RPi5.BootContract
import SeLe4n.Platform.RPi5.ProofHooks
import SeLe4n.Platform.RPi5.MmioAdapter

/-!
# Raspberry Pi 5 — Platform Binding

> **STATUS: staged for H3 hardware binding** (AN7-D.6 / PLT-M07).  This
> module is wired into `SeLe4n.Platform.Staged` so every CI run verifies
> it compiles.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation
> roadmap.

Composed `PlatformBinding` instance for the Raspberry Pi 5 (BCM2712, ARM64).
This is the first hardware target for seLe4n.

## Hardware profile

- **SoC**: Broadcom BCM2712, quad-core ARM Cortex-A76 @ 2.4 GHz
- **Architecture**: ARMv8.2-A (AArch64)
- **RAM**: Up to 8 GB LPDDR4X (4 GB modeled here)
- **Interrupt controller**: GIC-400 (ARM Generic Interrupt Controller v2)
- **Timer**: ARM Generic Timer, 54 MHz crystal
- **Debug**: PL011 UART at 0xFE201000

## Status

H3-prep stub. The binding is structurally complete (all contract fields
populated) but uses placeholder values for boot and interrupt contracts.
The H3 workstream will replace these with hardware-validated contracts
and add:
- ARMv8 multi-level page table walk semantics
- GIC-400 IRQ routing and acknowledgment
- ARM Generic Timer CNTPCT_EL0 binding
- MMU TTBR0/TTBR1 and TLB invalidation operations
- Verified boot sequence (ATF → U-Boot → kernel entry)
-/

namespace SeLe4n.Platform.RPi5

/-- Marker type for the Raspberry Pi 5 platform. -/
structure RPi5Platform where
  deriving Repr

/-- The Raspberry Pi 5 platform binding instance. -/
instance rpi5PlatformBinding : SeLe4n.Platform.PlatformBinding RPi5Platform where
  name := "Raspberry Pi 5 (BCM2712 / ARM64)"
  machineConfig := rpi5MachineConfig
  runtimeContract := rpi5RuntimeContract
  bootContract := rpi5BootContract
  interruptContract := rpi5InterruptContract

end SeLe4n.Platform.RPi5
