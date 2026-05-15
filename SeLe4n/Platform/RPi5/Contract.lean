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

**Production binding** (WS-RC R3 closure, v0.30.11).  All five
`PlatformBinding` typeclass fields are populated with substantive
values:

- `machineConfig` — BCM2712 hardware constants (44-bit PA, 48-bit VA,
  4 KiB pages, 65 536 ASIDs).
- `runtimeContract` — `rpi5RuntimeContract` (timer monotonicity,
  RAM-bounded memory access, deny register writes).
- `bootContract` — `rpi5BootContract` (empty initial object store,
  GIC-400 IRQ range bounded).
- `interruptContract` — `rpi5InterruptContract` (GIC-400 dispatch).
- `bootVSpaceRoot` — `some rpi5BootVSpaceRootEntry` (W^X-compliant
  identity-mapped boot VSpace; canonical six-mapping table covering
  kernel text RX, kernel data RW, kernel stack RW, UART0,
  GIC distributor, GIC CPU interface; **WS-RC R3 / DEEP-BOOT-01**).

ARMv8 multi-level page table walk semantics, MMU TTBR0/TTBR1 + TLB
invalidation, ARM Generic Timer CNTPCT_EL0 binding, and full boot
sequence (ATF → U-Boot → kernel entry) live in the AG6 / WS-RC R2
+ WS-RC R3 portfolio; remaining hardware integration items
(SMP secondary core bring-up, CCI-400 interconnect coherency,
out-of-Lean firmware handoff) are tracked per-ID in
`docs/audits/AUDIT_v0.30.11_DEFERRED.md` (post-1.0 hardening).
-/

namespace SeLe4n.Platform.RPi5

/-- Marker type for the Raspberry Pi 5 platform. -/
structure RPi5Platform where
  deriving Repr

/-- **WS-RC R3 (DEEP-BOOT-01)**: Reserved ObjId for the canonical RPi5
    boot VSpaceRoot.  Production boot configs (and the trace harness
    when exercising the hardware path) MUST NOT reuse this ObjId for
    any `initialObjects` entry — `bootVSpaceRootObjIdDistinct` (in
    `Platform.Boot`) enforces this at the gated boot path.

    **Value choice**: `ObjId.ofNat 1` — the smallest non-sentinel ObjId.
    Per `Prelude.lean` H-06/WS-E3, `ObjId.sentinel = ⟨0⟩` is reserved
    as the "unallocated" sentinel, so the boot VSpaceRoot MUST NOT use
    that value.  Using `1` keeps the reserved range compact and clearly
    distinguishable from sentinel.  Test suites that allocate ObjIds
    starting from `1` (e.g., `MainTraceHarness` threads 1-5) do NOT
    exercise `bootFromPlatformChecked` with this entry, so there is no
    runtime collision; the gate above defends against any future config
    that does. -/
def rpi5BootVSpaceRootObjId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 1

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
  -- WS-SM SM0.G: BCM2712 is a single-cluster quad-core Cortex-A76
  -- SoC.  All four cores share the inner-shareable domain.  Boot
  -- proceeds on Aff0 = 0 (the cluster's core-0); secondaries are
  -- Aff0 = 1, 2, 3 (see `rust/sele4n-hal/src/smp.rs::SECONDARY_MPIDR_TABLE`).
  coreCount := 4
  coreCountPos := by decide
  bootCoreId := ⟨0, by decide⟩
  sharingDomain := .inner

/-- **WS-SM SM0.E / SM0.G**: structural pinning of the
    `Concurrency.numCores` literal to the RPi5 binding's
    `coreCount` field.  Build-time `rfl` discharge — if either
    side changes without the other being updated in lockstep, this
    theorem fails to elaborate, blocking the offending PR.

    The two values are intentionally pinned: SM0.E keeps
    `Concurrency.numCores` as a platform-agnostic literal (no
    Platform import in the foundational types module), while the
    RPi5 binding is the single source of truth for the actual
    core count.  This theorem is the bridge that makes the
    drift-detection structural rather than convention-based. -/
theorem numCores_eq_rpi5_coreCount :
    SeLe4n.Kernel.Concurrency.numCores =
      SeLe4n.Platform.PlatformBinding.coreCount (platform := RPi5Platform) := by
  rfl

/-- **WS-SM SM0.E / SM0.G**: parallel pinning for `bootCoreId.val`.
    Both the SM0.E literal (`bootCoreId := ⟨0, _⟩`) and the RPi5
    binding (`bootCoreId := ⟨0, _⟩`) agree on the underlying core
    index; this theorem witnesses the agreement. -/
theorem bootCoreId_val_eq_rpi5 :
    SeLe4n.Kernel.Concurrency.bootCoreId.val =
      (SeLe4n.Platform.PlatformBinding.bootCoreId (platform := RPi5Platform)).val := by
  rfl

/-- **WS-SM SM0.G**: RPi5 is single-cluster, so the sharing domain
    is `.inner`.  Surfaced as a named theorem so SM3 lock primitives
    can `rfl`-rewrite `PlatformBinding.sharingDomain RPi5Platform`
    to `.inner` when emitting DSB ISH barriers on the RPi5 build
    profile. -/
theorem rpi5_sharingDomain :
    SeLe4n.Platform.PlatformBinding.sharingDomain (platform := RPi5Platform) =
      SeLe4n.Kernel.Concurrency.SharingDomain.inner := by
  rfl

end SeLe4n.Platform.RPi5
