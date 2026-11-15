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
# QEMU `virt` — the allocation exerciser's boot (WS-ZA ZA5.13)

The exerciser's deployment (`SeLe4n/Platform/Exerciser/Deployment.lean`) on
`virt`'s memory: its boot table pool and the one extension its boot maps
(`qemuVirtBootRamExtensions`), at the `virt` binding with the exerciser's
labeling.  Since WS-RB RB3 the exerciser boots the Raspberry Pi 5 image on
rpi5_machine's `raspi5b` first (`SeLe4n/Platform/RPi5/Exerciser.lean`); this
is the second lane.

The shipped `virt` entry (`QemuVirt.kernelMain`, `lean_kernel_main_qemu_virt`)
is untouched: it boots `QemuVirtPlatform`, whose labeling is the confined
production context (`qemuVirt_deploymentLabeling`), and
`SeLe4n/Testing/BootEntryContract.lean` holds it to that call and refuses this
image's call under it.  The HAL calls this entry only on an image built with
both `board_qemu_virt` and `smp_exercisers` (`rust/sele4n-hal/src/lean_entry.rs`).
-/

namespace SeLe4n.Platform.QemuVirt

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI

/-- The allocation exerciser's `virt` deployment. -/
structure QemuVirtExerciserPlatform where

/-- The exerciser's binding: the `virt` binding with the exerciser's labeling. -/
instance qemuVirtExerciserPlatformBinding : PlatformBinding QemuVirtExerciserPlatform :=
  { (qemuVirtPlatformBinding : PlatformBinding QemuVirtPlatform) with
    name := "QEMU virt allocation exerciser (GICv2 / Cortex-A76 / ARM64)"
    deploymentLabeling := Exerciser.deploymentLabeling
    witnessesOffBootVSpaceRoot := by decide }

/-- The exerciser's labeling partitions at the shipped boundary with the
    shipped lower witness, so its objects sit in the domains the shipped
    deployment's do. -/
theorem qemuVirtExerciser_boundary :
    Exerciser.upperDomainBase = qemuVirtUpperDomainBase ∧
    Exerciser.lowerWitnessIndex = qemuVirtLowerWitnessIndex := ⟨rfl, rfl⟩

/-- The exerciser's initial objects on `virt`'s memory. -/
def qemuVirtExerciserInitialObjects : List ObjectEntry :=
  Exerciser.initialObjects qemuVirtBootTablePage qemuVirtBootRamExtensions

/-- The configuration the exerciser's boot checks, whatever the account. -/
def qemuVirtExerciserBoundPlatformConfig : PlatformConfig :=
  { initialObjects := qemuVirtExerciserInitialObjects
    machineConfig := qemuVirtMachineConfig
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := QemuVirtExerciserPlatform)
    initialThreads := PlatformBinding.initialThreads (platform := QemuVirtExerciserPlatform)
    initialInterfaces := PlatformBinding.serviceInterfaces (platform := QemuVirtExerciserPlatform) }

-- ============================================================================
-- The boot, and the entry
-- ============================================================================

/-- **The exerciser image's only correct boot call** — the `virt` device-tree
    boot (`qemuVirtPlatformConfigFromDtb`, the shipped entry's own check of the
    board) at the exerciser's binding, its failure handled
    (`Exerciser.bootAndInitialiseOrHalt`).  What
    `lean_kernel_main_qemu_virt_exerciser` is, and what
    `SeLe4n/Testing/BootEntryContract.lean` holds that entry to. -/
def bootAndInitialiseQemuVirtExerciserFromDtbOrHalt (blob : ByteArray)
    (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) : BaseIO Unit :=
  match qemuVirtPlatformConfigFromDtb blob initialObjects bootVSpaceRoot with
  | .error _ => ffiFatalHaltAll
  | .ok config => do
      extendBootRamMap qemuVirtBootRamExtensions
      Exerciser.bootAndInitialiseOrHalt QemuVirtExerciserPlatform config

/-- The exerciser image's boot entry: `lean_kernel_main_qemu_virt_exerciser`,
    which `rust/sele4n-hal/src/lean_entry.rs` calls in place of
    `lean_kernel_main_qemu_virt` on an image built with `smp_exercisers`. -/
@[export lean_kernel_main_qemu_virt_exerciser]
def exerciserKernelMain (dtb : ByteArray) : BaseIO Unit :=
  bootAndInitialiseQemuVirtExerciserFromDtbOrHalt dtb qemuVirtExerciserInitialObjects none

-- ============================================================================
-- What differs, and what does not
-- ============================================================================

/-- **The shipped `virt` labeling refuses all four calls**: its declassification
    policy denies every pair and it configures no audit monitor, so the shipped
    image's `.declassify` and `.declassifySignal` are `.declassificationDenied`
    and its `.auditRead` and `.auditDrain` `.illegalAuthority`
    (`auditRead_unconfigured_denied`, `auditDrain_unconfigured_denied`). -/
theorem qemuVirt_shippedLabeling_denies :
    (∀ src dst, (PlatformBinding.labeling (platform := QemuVirtPlatform)).declassificationPolicy.canDeclassify
        src dst = false) ∧
    (PlatformBinding.labeling (platform := QemuVirtPlatform)).auditMonitorClearance = none ∧
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := QemuVirtPlatform)) = none :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

/-- The exerciser's monitor clearance validates on `virt`. -/
theorem qemuVirtExerciser_validatedAuditMonitorClearance :
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := QemuVirtExerciserPlatform)) =
      some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) :=
  Exerciser.validatedAuditMonitorClearance_eq

/-- The exerciser's labeling declares the shipped witnesses, so its boot starts
    the shipped initial threads. -/
theorem qemuVirtExerciser_initialThreads :
    PlatformBinding.initialThreads (platform := QemuVirtExerciserPlatform) =
      PlatformBinding.initialThreads (platform := QemuVirtPlatform) := rfl

/-- The exerciser's boot binds the shipped machine and boot root. -/
theorem qemuVirtExerciser_bindMachineConfig (board : SeLe4n.MachineConfig) :
    PlatformBinding.bindMachineConfig (platform := QemuVirtExerciserPlatform) board =
      qemuVirtMachineConfig := rfl

/-- WS-ZA ZA6.32: the exerciser's bound configuration serves `virt`'s lines,
    `qemuVirtGicSpiCount + 32`, the count the interrupt entry and the
    acknowledge refuse a line outside of. -/
theorem qemuVirtExerciser_bound_interruptLineCount (board : SeLe4n.MachineConfig) :
    (PlatformBinding.bindMachineConfig (platform := QemuVirtExerciserPlatform)
      board).interruptLineCount = qemuVirtGicSpiCount + 32 := rfl

/-- The root task's two untypeds tile the one extension's untyped part, which
    ends at the region map's base (`qemuVirtRegionMap_layout`). -/
theorem qemuVirtExerciserRootUntypeds_tile :
    Exerciser.firstExtension qemuVirtBootRamExtensions =
      (qemuVirtRootTaskUntyped.regionBase.toNat,
        qemuVirtRamTop - qemuVirtKernelReservedEnd) ∧
    (Exerciser.rootIpcBufferUntyped qemuVirtBootRamExtensions).regionBase.toNat +
        (Exerciser.rootIpcBufferUntyped qemuVirtBootRamExtensions).regionSize =
      qemuVirtRootTaskUntyped.regionBase.toNat + qemuVirtRootTaskUntyped.regionSize :=
  ⟨rfl, ((Exerciser.rootUntypeds_tile _ (by decide)).2.2).trans (by decide)⟩

-- ============================================================================
-- Every gate of the exerciser's checked boot, decided
-- ============================================================================

set_option maxRecDepth 8192 in
theorem qemuVirtExerciserBoundPlatformConfig_wellFormed :
    qemuVirtExerciserBoundPlatformConfig.wellFormed = true := by
  unfold PlatformConfig.wellFormed
  rw [objectIdsUnique_eq_transparent]
  decide

-- WS-ZA ZA6.4: the root CNode's cells, in a 64-slot geometry.
set_option maxRecDepth 8192 in
theorem qemuVirtExerciserBoundPlatformConfig_bootSafe :
    qemuVirtExerciserBoundPlatformConfig.initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_asidsDistinct :
    bootVSpaceAsidsDistinct qemuVirtExerciserBoundPlatformConfig = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_rootDistinct :
    bootVSpaceRootObjIdDistinct qemuVirtExerciserBoundPlatformConfig = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_rootNonSentinel :
    bootVSpaceRootObjIdNonSentinel qemuVirtExerciserBoundPlatformConfig = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_rootSafe :
    bootVSpaceRootSafe qemuVirtExerciserBoundPlatformConfig = true := by
  unfold bootVSpaceRootSafe
  decide

/-- The exerciser's checked boot takes its success arm — none of its refusals
    is reachable. -/
theorem qemuVirtExerciserBoundPlatformConfig_checked :
    bootFromPlatformChecked qemuVirtExerciserBoundPlatformConfig =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform qemuVirtExerciserBoundPlatformConfig)
          qemuVirtBootVSpaceRootEntry.id qemuVirtBootVSpaceRootEntry.root
          qemuVirtBootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ qemuVirtExerciserBoundPlatformConfig_wellFormed
    qemuVirtExerciserBoundPlatformConfig_bootSafe
    qemuVirtExerciserBoundPlatformConfig_asidsDistinct
    qemuVirtMachineConfig_wellFormed
    (by decide)
    qemuVirtExerciserBoundPlatformConfig_rootDistinct
    qemuVirtExerciserBoundPlatformConfig_rootNonSentinel
    qemuVirtExerciserBoundPlatformConfig_rootSafe qemuVirtBootVSpaceRootEntry rfl

end SeLe4n.Platform.QemuVirt
