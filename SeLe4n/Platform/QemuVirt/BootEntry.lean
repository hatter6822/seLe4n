-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.FFI
import SeLe4n.Platform.QemuVirt.Contract

/-!
# QEMU `virt` — the device-tree boot (WS-BP BP8.1)

The `virt` image's counterpart of `Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt`:
parse the firmware's device tree with the verified parser, check the board
against this binding, map its RAM outside the kernel's extent, and boot — or
halt every PE.

The *checks* are the RPi5 bridge's own predicates, not copies of them:
`Boot.deviceTreeCoversMachineConfig` for the RAM and
`Boot.deviceTreeCoversMmioRegions` for the devices, so "does this board match
the binding" has one answer for both boards and differs only in the binding it
is asked about.  What differs is the binding's shape: `virt` is one fixed
configuration, so the initial objects are a list rather than a function of a
RAM variant, and the RAM the boot maps is `qemuVirtBootRamExtensions` whatever
the account.

The refusal type is the RPi5 bridge's (`Platform.FFI.DeviceTreeBootRefusal`):
an unparseable blob and a board that is not this image's are the same two
refusals on either board.
-/

namespace SeLe4n.Platform.QemuVirt

open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI

/-- The pure half: parse the blob, check the board — the RAM the binding
    declares and the three MMIO windows, each as the device it must be — and
    produce the configuration the checked boot runs on.  The device tree does
    not describe the hardware the kernel programs: `bindPlatformConfig` binds
    the binding's own machine configuration. -/
def qemuVirtPlatformConfigFromDtb (blob : ByteArray) (irqTable : List IrqEntry)
    (initialObjects : List ObjectEntry) (bootVSpaceRoot : Option BootVSpaceRootEntry) :
    Except DeviceTreeBootRefusal PlatformConfig :=
  match SeLe4n.Platform.DeviceTree.fromDtbFull blob qemuVirtMachineConfig.physicalAddressWidth with
  | .error e => .error (.unparseableBlob e)
  | .ok dt =>
      if deviceTreeCoversMachineConfig dt qemuVirtMachineConfig
          && deviceTreeCoversMmioRegions dt qemuVirtRequiredMmioWindows then
        .ok (PlatformConfig.fromDeviceTree dt irqTable initialObjects bootVSpaceRoot)
      else
        .error .boardDoesNotMatchBinding

/-- The checked platform boot at the `virt` binding — the platform a
    definition, not an argument the exported entry could vary. -/
def bootAndInitialiseQemuVirt (config : PlatformConfig) : BaseIO (Except String SeLe4n.Model.SystemState) :=
  bootAndInitialisePlatform QemuVirtPlatform config

/-- The `virt` boot is the generic one at this binding. -/
theorem bootAndInitialiseQemuVirt_eq (config : PlatformConfig) :
    bootAndInitialiseQemuVirt config = bootAndInitialisePlatform QemuVirtPlatform config := rfl

/-- The `virt` boot with its failure handled: a refused boot halts every PE. -/
def bootAndInitialiseQemuVirtOrHalt (config : PlatformConfig) : BaseIO Unit := do
  match ← bootAndInitialiseQemuVirt config with
  | .ok _ => pure ()
  | .error _ => ffiFatalHaltAll

/-- **The `virt` hardware boot's only correct call** — what
    `lean_kernel_main_qemu_virt` (`QemuVirt.kernelMain`) is, and what
    `SeLe4n/Testing/BootEntryContract.lean` holds that entry to.  An accepted
    board's RAM outside the kernel's extent is mapped first, while every
    secondary is still parked, then the deployment is installed; a refused
    blob halts every PE. -/
def bootAndInitialiseQemuVirtFromDtbOrHalt (blob : ByteArray) (irqTable : List IrqEntry)
    (initialObjects : List ObjectEntry) (bootVSpaceRoot : Option BootVSpaceRootEntry) :
    BaseIO Unit :=
  match qemuVirtPlatformConfigFromDtb blob irqTable initialObjects bootVSpaceRoot with
  | .error _ => ffiFatalHaltAll
  | .ok config => do
      extendBootRamMap qemuVirtBootRamExtensions
      bootAndInitialiseQemuVirtOrHalt config

/-- A refused blob boots nothing — every PE halts. -/
theorem bootAndInitialiseQemuVirtFromDtbOrHalt_refused (blob : ByteArray)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) (e : DeviceTreeBootRefusal)
    (h : qemuVirtPlatformConfigFromDtb blob irqTable initialObjects bootVSpaceRoot = .error e) :
    bootAndInitialiseQemuVirtFromDtbOrHalt blob irqTable initialObjects bootVSpaceRoot =
      ffiFatalHaltAll := by
  unfold bootAndInitialiseQemuVirtFromDtbOrHalt
  rw [h]

/-- An accepted board maps its RAM and boots through the checked entry, and
    nothing else. -/
theorem bootAndInitialiseQemuVirtFromDtbOrHalt_accepted (blob : ByteArray)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) (config : PlatformConfig)
    (h : qemuVirtPlatformConfigFromDtb blob irqTable initialObjects bootVSpaceRoot = .ok config) :
    bootAndInitialiseQemuVirtFromDtbOrHalt blob irqTable initialObjects bootVSpaceRoot =
      (do
        extendBootRamMap qemuVirtBootRamExtensions
        bootAndInitialiseQemuVirtOrHalt config) := by
  unfold bootAndInitialiseQemuVirtFromDtbOrHalt
  rw [h]

/-- An accepted configuration is the device tree's account around the caller's
    half — and the account covered this binding's RAM and devices. -/
theorem qemuVirtPlatformConfigFromDtb_ok_eq_fromDeviceTree (blob : ByteArray)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) (config : PlatformConfig)
    (h : qemuVirtPlatformConfigFromDtb blob irqTable initialObjects bootVSpaceRoot = .ok config) :
    ∃ dt, (deviceTreeCoversMachineConfig dt qemuVirtMachineConfig
        && deviceTreeCoversMmioRegions dt qemuVirtRequiredMmioWindows) = true ∧
      config = PlatformConfig.fromDeviceTree dt irqTable initialObjects bootVSpaceRoot := by
  unfold qemuVirtPlatformConfigFromDtb at h
  split at h
  · cases h
  · rename_i dt _
    split at h
    · rename_i hCov
      cases h
      exact ⟨dt, hCov, rfl⟩
    · cases h

/-- A board whose device tree does not cover the binding's RAM and devices is
    refused, whatever else the blob says. -/
theorem qemuVirtPlatformConfigFromDtb_refuses_foreign_board (blob : ByteArray)
    (irqTable : List IrqEntry) (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) (dt : SeLe4n.Platform.DeviceTree)
    (hParse : SeLe4n.Platform.DeviceTree.fromDtbFull blob
      qemuVirtMachineConfig.physicalAddressWidth = .ok dt)
    (hCov : (deviceTreeCoversMachineConfig dt qemuVirtMachineConfig
        && deviceTreeCoversMmioRegions dt qemuVirtRequiredMmioWindows) = false) :
    qemuVirtPlatformConfigFromDtb blob irqTable initialObjects bootVSpaceRoot =
      .error .boardDoesNotMatchBinding := by
  unfold qemuVirtPlatformConfigFromDtb
  rw [hParse]
  simp only [hCov, Bool.false_eq_true, ↓reduceIte]

end SeLe4n.Platform.QemuVirt
