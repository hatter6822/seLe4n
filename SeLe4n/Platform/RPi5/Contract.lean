-- SPDX-License-Identifier: GPL-3.0-or-later
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
-- WS-RC R3 (DEEP-BOOT-01): the canonical RPi5 boot VSpaceRoot exposed
-- to the platform binding so `bootFromPlatformChecked` can install it
-- via `installBootVSpaceRoot` during the gated boot pipeline.
import SeLe4n.Platform.RPi5.VSpaceBoot

/-!
# Raspberry Pi 5 — Platform Binding

> **STATUS: production binding** (typeclass instance reachable from
> `SeLe4n.lean`).  The Lean-side `PlatformBinding` instance composed
> here is in the production import chain; the substantive hardware
> path activation (FFI dispatch into `syscallEntryChecked` and
> `suspendThread`) is staged behind WS-RC R2 (the FFI wiring).
> See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation roadmap.

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

/-- **WS-RC R3 (DEEP-BOOT-01)**: Reserved ObjId for the canonical RPi5
    boot VSpaceRoot.  Production boot configs (and the trace harness
    when exercising the hardware path) should NOT reuse this ObjId for
    any `initialObjects` entry — `bootVSpaceRootObjIdDistinct` (in
    `Platform.Boot`) enforces this at the gated boot path.  Chosen as
    `0` to land in the kernel-reserved low-ObjId range; user-mode
    objects are typically allocated above 1024 by the seL4 reference
    boot. -/
def rpi5BootVSpaceRootObjId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 0

/-- **WS-RC R3 (DEEP-BOOT-01)**: The canonical RPi5
    `BootVSpaceRootEntry` — composes the reserved ObjId with the
    proven-W^X-compliant `rpi5BootVSpaceRoot` data structure and its
    `mappings.invExt` discharge witness. -/
def rpi5BootVSpaceRootEntry : SeLe4n.Platform.BootVSpaceRootEntry where
  id := rpi5BootVSpaceRootObjId
  root := SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot
  hMappings := SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot_mappings_invExt

/-- The Raspberry Pi 5 platform binding instance.

    **WS-RC R3 (DEEP-BOOT-01)**: `bootVSpaceRoot` is now populated with
    the canonical RPi5 boot VSpaceRoot entry, threading the
    proven-W^X-compliant `rpi5BootVSpaceRoot` through the platform
    binding so `bootFromPlatformChecked` can install it via
    `installBootVSpaceRoot` during gated boot.  The standalone
    pre-R3 binding left this field implicit (`none`) and the verified
    boot VSpace data structure was inert; per the implement-the-
    improvement rule, the verified structure is the better state. -/
instance rpi5PlatformBinding : SeLe4n.Platform.PlatformBinding RPi5Platform where
  name := "Raspberry Pi 5 (BCM2712 / ARM64)"
  machineConfig := rpi5MachineConfig
  runtimeContract := rpi5RuntimeContract
  bootContract := rpi5BootContract
  interruptContract := rpi5InterruptContract
  bootVSpaceRoot := some rpi5BootVSpaceRootEntry

end SeLe4n.Platform.RPi5
