-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.QemuVirt.KernelMain

/-!
# QEMU `virt` — the allocation exerciser's boot (WS-ZA ZA5.13)

The QEMU test image that carries the in-image drivers (`smp_exercisers`)
measures the heap allocations of every syscall round trip
(`rust/sele4n-hal/src/smp_exercisers.rs`).  Four of them — the declassification,
the declassified signal, the audit read and the audit drain — are refused by
the shipped labeling before they do anything: its declassification policy
denies every downgrade and it configures no audit monitor
(`qemuVirt_shippedLabeling_denies`).  A refusal measures nothing, so the test
image boots this deployment instead: the shipped one with three differences,
each the least the four calls need, and nothing else.

* **The labeling** (`qemuVirtExerciserDeploymentLabeling`): the same partition
  at the same boundary with the same witnesses, its lower half labeled
  `kernelTrusted` rather than `lowTrusted`.  The audit monitor's clearance
  must be a top of the lattice (`validatedAuditMonitorClearance`), and a monitor
  must dominate it, so the boot domain's threads must be at the top; the upper
  half stays `highUntrusted`, so the two halves still carry different labels
  (the boot guard's `verifiesDeclaredSeparation`).  Information may now flow up
  into the boot domain, which the shipped confinement forbids — this image is a
  test image, and the shipped image keeps the confinement.
* **One downgrade** (`qemuVirtExerciserDeclassificationPolicy`): from the boot
  domain to the upper one, the one pair the base lattice refuses that a boot
  thread can reach.
* **The audit monitor**: the clearance is the top, so the boot domain's threads
  qualify, and the root task holds the boot audit capability in slot 15
  (`qemuVirtExerciserAuditSlot`), which the exerciser deletes before the
  invocation scenarios carve into it.

The shipped `virt` entry (`QemuVirt.kernelMain`, `lean_kernel_main_qemu_virt`)
is untouched: it boots `QemuVirtPlatform`, whose labeling is the confined
production context (`qemuVirt_deploymentLabeling`), and
`SeLe4n/Testing/BootEntryContract.lean` holds it to that call and refuses this
image's call under it.  The HAL calls this entry only on an image built with
both `board_qemu_virt` and `smp_exercisers` (`rust/sele4n-hal/src/lean_entry.rs`),
and the Raspberry Pi 5 image never carries `smp_exercisers`.
-/

namespace SeLe4n.Platform.QemuVirt

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI
open SeLe4n.Platform.RPi5 (rpi5InitialCNode)

/-- The allocation exerciser's `virt` deployment. -/
structure QemuVirtExerciserPlatform where

/-- The exerciser's one authorized downgrade: from the boot domain
    (`kernelTrusted`, domain 3) to the upper one (`highUntrusted`, domain 2). -/
def qemuVirtExerciserDeclassificationPolicy : SeLe4n.Kernel.DeclassificationPolicy :=
  { canDeclassify := fun src dst =>
      src.id == (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted).id &&
        dst.id == (SeLe4n.Kernel.embedLegacyLabel .highUntrusted).id }

/-- The exerciser's labeling: the shipped partition at the shipped boundary and
    witnesses, its lower half at the top of the lattice, with one downgrade and
    the top as the audit monitor's clearance. -/
def qemuVirtExerciserDeploymentLabeling : SeLe4n.Kernel.DeploymentLabeling :=
  { SeLe4n.Kernel.indexPartitionedDeploymentLabeling qemuVirtUpperDomainBase
      qemuVirtLowerWitnessIndex .kernelTrusted .highUntrusted (by decide)
      qemuVirtLowerWitnessIndex_admissible qemuVirtLowerWitnessIndex_below_boundary with
    declassificationPolicy := qemuVirtExerciserDeclassificationPolicy
    auditMonitorClearance := some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) }

/-- The exerciser's binding: the `virt` binding with the exerciser's labeling. -/
instance qemuVirtExerciserPlatformBinding : PlatformBinding QemuVirtExerciserPlatform :=
  { (qemuVirtPlatformBinding : PlatformBinding QemuVirtPlatform) with
    name := "QEMU virt allocation exerciser (GICv2 / Cortex-A76 / ARM64)"
    deploymentLabeling := qemuVirtExerciserDeploymentLabeling
    witnessesOffBootVSpaceRoot := by decide }

/-- The root task's CNode slot holding the exerciser's boot audit capability:
    the last slot, which no scenario fills before the audit scenarios end. -/
def qemuVirtExerciserAuditSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 15

/-- The exerciser's root CNode: the shipped root CNode's capabilities and the
    audit trail's, with read and write (`Capability.auditTrailManage`), in
    `qemuVirtExerciserAuditSlot`. -/
def qemuVirtExerciserRootTaskCNode : CNode :=
  { rpi5InitialCNode
      (qemuVirtRootTaskCNodeSlots ++ [(qemuVirtExerciserAuditSlot, Capability.auditTrailManage)])
    with guardValue := qemuVirtRootTaskCNodeGuard }

/-- The exerciser's initial objects: the shipped deployment's, its root CNode
    (the second entry) replaced by the exerciser's. -/
def qemuVirtExerciserInitialObjects : List ObjectEntry :=
  qemuVirtInitialObjects.set 1
    { id := qemuVirtRootTaskCNodeId, obj := .cnode qemuVirtExerciserRootTaskCNode
      hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
      hMappings := fun _ h => nomatch h }

/-- The configuration the exerciser's boot checks, whatever the account. -/
def qemuVirtExerciserBoundPlatformConfig : PlatformConfig :=
  { irqTable := qemuVirtIrqTable
    initialObjects := qemuVirtExerciserInitialObjects
    machineConfig := qemuVirtMachineConfig
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := QemuVirtExerciserPlatform)
    initialThreads := PlatformBinding.initialThreads (platform := QemuVirtExerciserPlatform)
    initialInterfaces := PlatformBinding.serviceInterfaces (platform := QemuVirtExerciserPlatform) }

-- ============================================================================
-- The boot, and the entry
-- ============================================================================

/-- The checked platform boot at the exerciser's binding. -/
def bootAndInitialiseQemuVirtExerciser (config : PlatformConfig) :
    BaseIO (Except String SeLe4n.Model.SystemState) :=
  bootAndInitialisePlatform QemuVirtExerciserPlatform config

/-- The exerciser's boot with its failure handled: a refused boot halts every
    PE. -/
def bootAndInitialiseQemuVirtExerciserOrHalt (config : PlatformConfig) : BaseIO Unit := do
  match ← bootAndInitialiseQemuVirtExerciser config with
  | .ok _ => pure ()
  | .error _ => ffiFatalHaltAll

/-- **The exerciser image's only correct boot call** — the `virt` device-tree
    boot (`qemuVirtPlatformConfigFromDtb`, the shipped entry's own check of the
    board) at the exerciser's binding, its failure handled.  What
    `lean_kernel_main_qemu_virt_exerciser` is, and what
    `SeLe4n/Testing/BootEntryContract.lean` holds that entry to. -/
def bootAndInitialiseQemuVirtExerciserFromDtbOrHalt (blob : ByteArray)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) : BaseIO Unit :=
  match qemuVirtPlatformConfigFromDtb blob irqTable initialObjects bootVSpaceRoot with
  | .error _ => ffiFatalHaltAll
  | .ok config => do
      extendBootRamMap qemuVirtBootRamExtensions
      bootAndInitialiseQemuVirtExerciserOrHalt config

/-- The exerciser image's boot entry: `lean_kernel_main_qemu_virt_exerciser`,
    which `rust/sele4n-hal/src/lean_entry.rs` calls in place of
    `lean_kernel_main_qemu_virt` on an image built with `smp_exercisers`. -/
@[export lean_kernel_main_qemu_virt_exerciser]
def exerciserKernelMain (dtb : ByteArray) : BaseIO Unit :=
  bootAndInitialiseQemuVirtExerciserFromDtbOrHalt dtb qemuVirtIrqTable
    qemuVirtExerciserInitialObjects none

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

/-- The exerciser's policy authorizes exactly one pair: the boot domain to the
    upper one. -/
theorem qemuVirtExerciserDeclassificationPolicy_canDeclassify_iff
    (src dst : SeLe4n.Kernel.SecurityDomain) :
    qemuVirtExerciserDeclassificationPolicy.canDeclassify src dst = true ↔
      src = SeLe4n.Kernel.embedLegacyLabel .kernelTrusted ∧
        dst = SeLe4n.Kernel.embedLegacyLabel .highUntrusted := by
  obtain ⟨s⟩ := src
  obtain ⟨d⟩ := dst
  simp [qemuVirtExerciserDeclassificationPolicy, SeLe4n.Kernel.embedLegacyLabel,
    SeLe4n.Kernel.SecurityLabel.kernelTrusted, SeLe4n.Kernel.SecurityLabel.highUntrusted]

/-- The exerciser's monitor clearance validates — it is the top — so its audit
    calls are not refused for want of a monitor. -/
theorem qemuVirtExerciser_validatedAuditMonitorClearance :
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := QemuVirtExerciserPlatform)) =
      some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) := by
  decide

/-- The exerciser's labeling declares the shipped witnesses, so its boot starts
    the shipped initial threads. -/
theorem qemuVirtExerciser_initialThreads :
    PlatformBinding.initialThreads (platform := QemuVirtExerciserPlatform) =
      PlatformBinding.initialThreads (platform := QemuVirtPlatform) := rfl

/-- The exerciser's boot binds the shipped machine and boot root. -/
theorem qemuVirtExerciser_bindMachineConfig (board : SeLe4n.MachineConfig) :
    PlatformBinding.bindMachineConfig (platform := QemuVirtExerciserPlatform) board =
      qemuVirtMachineConfig := rfl

-- ============================================================================
-- Every gate of the exerciser's checked boot, decided
-- ============================================================================

set_option maxRecDepth 8192 in
theorem qemuVirtExerciserBoundPlatformConfig_wellFormed :
    qemuVirtExerciserBoundPlatformConfig.wellFormed = true := by
  unfold PlatformConfig.wellFormed
  rw [irqsUnique_eq_transparent, objectIdsUnique_eq_transparent]
  decide

theorem qemuVirtExerciserBoundPlatformConfig_bootSafe :
    qemuVirtExerciserBoundPlatformConfig.initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_asidsDistinct :
    bootVSpaceAsidsDistinct qemuVirtExerciserBoundPlatformConfig = true := by
  decide

set_option maxRecDepth 8192 in
theorem qemuVirtExerciserBoundPlatformConfig_irqHandlers :
    irqHandlersAndNotificationsReciprocal qemuVirtExerciserBoundPlatformConfig = true := by
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
    qemuVirtExerciserBoundPlatformConfig_irqHandlers qemuVirtMachineConfig_wellFormed
    (by decide)
    qemuVirtExerciserBoundPlatformConfig_rootDistinct
    qemuVirtExerciserBoundPlatformConfig_rootNonSentinel
    qemuVirtExerciserBoundPlatformConfig_rootSafe qemuVirtBootVSpaceRootEntry rfl

end SeLe4n.Platform.QemuVirt
