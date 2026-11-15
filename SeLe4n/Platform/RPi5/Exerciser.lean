-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Exerciser.Deployment

/-!
# Raspberry Pi 5 — the allocation exerciser's boot (WS-RB RB3)

The exerciser's deployment (`SeLe4n/Platform/Exerciser/Deployment.lean`) on
the Raspberry Pi 5's memory, at the RPi5 binding with the exerciser's labeling
and the service interface the scenarios register on.  The exerciser image is
the Raspberry Pi 5 image with `smp_exercisers`; it runs on rpi5_machine's
`raspi5b` (`scripts/qemu_exerciser_lib.sh`), and `virt` is the second lane
(`SeLe4n/Platform/QemuVirt/Exerciser.lean`).

The device tree decides the board here as it does for the shipped entry: the
same verified parse and the same check of the board against the binding
(`Platform.FFI.rpi5PlatformConfigFromDtb`), the objects a function of the
variant the parse selects (`rpi5ExerciserInitialObjectsFor`), the RAM the boot
maps that variant's (`rpi5BootRamExtensionsFor`).  The root task's untypeds
tile the first gigabyte's part the firmware reports, and a board past the
first gigabyte gets one more untyped over the rest, so the RAM the boot maps
is the RAM the root task owns on every variant.  Every gate of the checked
boot is decided on the configuration rpi5_machine's `raspi5b` presents with
`-m 1G` (`rpi5ExerciserMeasuredVariant`), the one the exerciser measures on.

The shipped entry (`RPi5.kernelMain`, `lean_kernel_main`) is untouched:
`SeLe4n/Testing/BootEntryContract.lean` holds it to the shipped boot call and
refuses this image's call under it.  The HAL calls this entry only on a
Raspberry Pi 5 image built with `smp_exercisers`
(`rust/sele4n-hal/src/lean_entry.rs`).
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI

/-- The allocation exerciser's Raspberry Pi 5 deployment. -/
structure RPi5ExerciserPlatform where

/-- The exerciser's binding: the RPi5 binding with the exerciser's labeling and
    the service interface its registration scenarios name (the one the `virt`
    binding installs, `qemuVirtExerciserInterface`). -/
instance rpi5ExerciserPlatformBinding : PlatformBinding RPi5ExerciserPlatform :=
  { (rpi5PlatformBinding : PlatformBinding RPi5Platform) with
    name := "Raspberry Pi 5 allocation exerciser (BCM2712 / ARM64)"
    serviceInterfaces := [SeLe4n.Platform.QemuVirt.qemuVirtExerciserInterface]
    deploymentLabeling := Exerciser.deploymentLabeling
    witnessesOffBootVSpaceRoot := by decide }

/-- The exerciser's labeling partitions at the shipped boundary with the
    shipped lower witness. -/
theorem rpi5Exerciser_boundary :
    Exerciser.upperDomainBase = rpi5UpperDomainBase ∧
    Exerciser.lowerWitnessIndex = rpi5LowerWitnessIndex := ⟨rfl, rfl⟩

/-- The exerciser's initial objects on a board bound to `v`: over the
    extensions the boot maps for it. -/
def rpi5ExerciserInitialObjectsFor (v : BCM2712Config) : List ObjectEntry :=
  Exerciser.initialObjects rpi5BootTablePage (rpi5BootRamExtensions v)

/-- The configuration the exerciser's boot checks on a board bound to `v`. -/
def rpi5ExerciserBoundPlatformConfigAt (v : BCM2712Config) : PlatformConfig :=
  { initialObjects := rpi5ExerciserInitialObjectsFor v
    machineConfig := rpi5MachineConfigForVariant v
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := RPi5ExerciserPlatform)
    initialThreads := PlatformBinding.initialThreads (platform := RPi5ExerciserPlatform)
    initialInterfaces := PlatformBinding.serviceInterfaces (platform := RPi5ExerciserPlatform) }

/-- **The configuration the exerciser measures on**: rpi5_machine's `raspi5b`
    with `-m 1G` reports the first gigabyte less the VideoCore's 4 MiB, as a
    1 GiB Pi 5's firmware does (`tests/fixtures/rpi5_machine_dtb.hex`, which
    `tests/Ak9PlatformSuite.lean` holds the bridge to binding at this top). -/
def rpi5ExerciserMeasuredVariant : BCM2712Config :=
  { ramSize := 1 * 1024 * 1024 * 1024, lowRamTop := 0x3FC0_0000 }

theorem rpi5ExerciserMeasuredVariant_admissible : rpi5ExerciserMeasuredVariant.Admissible :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- The boot, and the entry
-- ============================================================================

/-- **The exerciser image's only correct boot call** — the RPi5 device-tree
    boot (`rpi5PlatformConfigFromDtb`, the shipped entry's own check of the
    board) at the exerciser's binding: an accepted board's RAM mapped
    (`rpi5BootRamExtensionsFor`), then the checked boot with its failure
    handled (`Exerciser.bootAndInitialiseOrHalt`).  What
    `lean_kernel_main_rpi5_exerciser` is, and what
    `SeLe4n/Testing/BootEntryContract.lean` holds that entry to. -/
def bootAndInitialiseRPi5ExerciserFromDtbOrHalt (blob : ByteArray)
    (initialObjectsFor : BCM2712Config → List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) : BaseIO Unit :=
  match rpi5PlatformConfigFromDtb blob initialObjectsFor bootVSpaceRoot with
  | .error _ => ffiFatalHaltAll
  | .ok config => do
      extendBootRamMap (rpi5BootRamExtensionsFor config.machineConfig)
      Exerciser.bootAndInitialiseOrHalt RPi5ExerciserPlatform config

/-- The exerciser image's boot entry: `lean_kernel_main_rpi5_exerciser`, which
    `rust/sele4n-hal/src/lean_entry.rs` calls in place of `lean_kernel_main`
    on a Raspberry Pi 5 image built with `smp_exercisers`. -/
@[export lean_kernel_main_rpi5_exerciser]
def exerciserKernelMain (dtb : ByteArray) : BaseIO Unit :=
  bootAndInitialiseRPi5ExerciserFromDtbOrHalt dtb rpi5ExerciserInitialObjectsFor none

-- ============================================================================
-- What differs, and what does not
-- ============================================================================

/-- **The shipped RPi5 labeling refuses the four calls the exerciser measures**:
    its declassification policy denies every pair and it configures no audit
    monitor. -/
theorem rpi5_shippedLabeling_denies :
    (∀ src dst, (PlatformBinding.labeling (platform := RPi5Platform)).declassificationPolicy.canDeclassify
        src dst = false) ∧
    (PlatformBinding.labeling (platform := RPi5Platform)).auditMonitorClearance = none ∧
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := RPi5Platform)) = none :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

/-- The exerciser's monitor clearance validates on the Pi 5. -/
theorem rpi5Exerciser_validatedAuditMonitorClearance :
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := RPi5ExerciserPlatform)) =
      some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) :=
  Exerciser.validatedAuditMonitorClearance_eq

/-- The exerciser's labeling declares the shipped witnesses, so its boot starts
    the shipped initial threads. -/
theorem rpi5Exerciser_initialThreads :
    PlatformBinding.initialThreads (platform := RPi5ExerciserPlatform) =
      PlatformBinding.initialThreads (platform := RPi5Platform) := rfl

/-- The exerciser's boot binds the variant the shipped boot binds for every
    account, so the device tree selects the board for both alike. -/
theorem rpi5Exerciser_bindMachineConfig :
    PlatformBinding.bindMachineConfig (platform := RPi5ExerciserPlatform) =
      rpi5BoundMachineConfig := rfl

/-- WS-RB RB3: the exerciser's bound configuration serves the GIC-400's lines,
    `gicSpiCount + 32`, which include the two the HAL raises on the Pi 5
    (INTIDs 318 and 319, past every line the BCM2712 wires). -/
theorem rpi5Exerciser_bound_interruptLineCount (board : SeLe4n.MachineConfig) :
    (PlatformBinding.bindMachineConfig (platform := RPi5ExerciserPlatform)
      board).interruptLineCount = gicSpiCount + 32 := rfl

/-- On the measured board the boot maps one extension, the first gigabyte's
    part from the kernel's extent's end to the top the firmware reports, so the
    root task's two untypeds tile all the RAM it maps below the region map
    (`Exerciser.rootUntypeds_tile`), and no further untyped is made. -/
theorem rpi5ExerciserMeasured_extensions :
    rpi5BootRamExtensions rpi5ExerciserMeasuredVariant =
      [(rpi5KernelReservedEnd, 0x3FC0_0000 - rpi5KernelReservedEnd)] := by
  decide

theorem rpi5ExerciserMeasured_rootUntypeds_tile :
    let ext := rpi5BootRamExtensions rpi5ExerciserMeasuredVariant
    (Exerciser.rootTaskUntyped ext).regionBase.toNat = rpi5KernelReservedEnd ∧
    (Exerciser.rootTaskUntyped ext).regionBase.toNat + (Exerciser.rootTaskUntyped ext).regionSize =
      (Exerciser.rootIpcBufferUntyped ext).regionBase.toNat ∧
    (Exerciser.rootIpcBufferUntyped ext).regionBase.toNat +
        (Exerciser.rootIpcBufferUntyped ext).regionSize =
      regionMapBaseOf (rpi5KernelReservedEnd, 0x3FC0_0000 - rpi5KernelReservedEnd) := by
  rw [rpi5ExerciserMeasured_extensions]
  exact Exerciser.rootUntypeds_tile _ (by decide)

-- ============================================================================
-- Every gate of the exerciser's checked boot, decided on the measured board
-- ============================================================================

set_option maxRecDepth 8192 in
theorem rpi5ExerciserMeasured_wellFormed :
    (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant).wellFormed = true := by
  unfold PlatformConfig.wellFormed
  rw [objectIdsUnique_eq_transparent]
  decide

set_option maxRecDepth 8192 in
theorem rpi5ExerciserMeasured_bootSafe :
    (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant).initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  decide

theorem rpi5ExerciserMeasured_asidsDistinct :
    bootVSpaceAsidsDistinct (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant) =
      true := by
  decide

theorem rpi5ExerciserMeasured_rootDistinct :
    bootVSpaceRootObjIdDistinct (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant) =
      true := by
  decide

theorem rpi5ExerciserMeasured_rootNonSentinel :
    bootVSpaceRootObjIdNonSentinel
      (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant) = true := by
  decide

theorem rpi5ExerciserMeasured_rootSafe :
    bootVSpaceRootSafe (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant) = true := by
  unfold bootVSpaceRootSafe
  decide

/-- The exerciser's checked boot on the measured board takes its success arm —
    none of its refusals is reachable. -/
theorem rpi5ExerciserMeasured_checked :
    bootFromPlatformChecked (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant) =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot
          (bootFromPlatform (rpi5ExerciserBoundPlatformConfigAt rpi5ExerciserMeasuredVariant))
          rpi5BootVSpaceRootEntry.id rpi5BootVSpaceRootEntry.root
          rpi5BootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ rpi5ExerciserMeasured_wellFormed
    rpi5ExerciserMeasured_bootSafe rpi5ExerciserMeasured_asidsDistinct
    (rpi5MachineConfigForVariant_wellFormed _ rpi5ExerciserMeasuredVariant_admissible)
    (by decide)
    rpi5ExerciserMeasured_rootDistinct rpi5ExerciserMeasured_rootNonSentinel
    rpi5ExerciserMeasured_rootSafe rpi5BootVSpaceRootEntry rfl

end SeLe4n.Platform.RPi5
