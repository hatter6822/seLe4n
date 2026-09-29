-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.QemuVirt.Deployment

/-!
# QEMU `virt` — the hardware boot entry (WS-BP BP8.1)

`rust_boot_main` on an image built with `board_qemu_virt` calls
`lean_kernel_main_qemu_virt(dtb)` once, on the boot core, after the library
initializer — where the RPi5 image calls `lean_kernel_main`
(`rust/sele4n-hal/src/lean_entry.rs` selects the one its board names, by
`cfg`).  Both entries are in every archive, because both modules are in the
library root; the HAL's `cfg` decides which one a given image calls.

The entry is the `virt` device-tree boot with its failure handled, on the
firmware's blob and this deployment, and nothing else —
`SeLe4n/Testing/BootEntryContract.lean` holds it to exactly that program, as it
holds `lean_kernel_main` to the RPi5's.
-/

namespace SeLe4n.Platform.QemuVirt

/-- The `virt` hardware boot entry: `lean_kernel_main_qemu_virt`. -/
@[export lean_kernel_main_qemu_virt]
def kernelMain (dtb : ByteArray) : BaseIO Unit :=
  bootAndInitialiseQemuVirtFromDtbOrHalt dtb qemuVirtIrqTable qemuVirtInitialObjects none

/-- A device tree the bridge refuses boots nothing: every PE halts. -/
theorem kernelMain_refuses (dtb : ByteArray) (e : Platform.FFI.DeviceTreeBootRefusal)
    (h : qemuVirtPlatformConfigFromDtb dtb qemuVirtIrqTable qemuVirtInitialObjects none =
      .error e) :
    kernelMain dtb = Platform.FFI.ffiFatalHaltAll :=
  bootAndInitialiseQemuVirtFromDtbOrHalt_refused _ _ _ _ e h

/-- A device tree the bridge accepts maps the board's RAM outside the kernel's
    extent, then installs the deployment's boot state and the binding's
    labeling, and nothing else — the halt arm is never taken on it. -/
theorem kernelMain_installs (dtb : ByteArray) (config : Platform.Boot.PlatformConfig)
    (h : qemuVirtPlatformConfigFromDtb dtb qemuVirtIrqTable qemuVirtInitialObjects none =
      .ok config) :
    kernelMain dtb =
      (do
        Platform.FFI.extendBootRamMap qemuVirtBootRamExtensions
        Platform.FFI.initialiseKernelState qemuVirtDeploymentBootState.state
        Platform.FFI.initialiseKernelLabelingContext
          (PlatformBinding.labeling (platform := QemuVirtPlatform))) := by
  unfold kernelMain
  rw [bootAndInitialiseQemuVirtFromDtbOrHalt_accepted _ _ _ _ config h,
    qemuVirtPlatformConfigFromDtb_deployment_ok dtb config h,
    bootAndInitialiseQemuVirtOrHalt_qemuVirtPlatformConfigFor]

/-- ...and the state it installs satisfies the proof-layer invariant bundle. -/
theorem kernelMain_installs_invariantBundle :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle qemuVirtDeploymentBootState.state :=
  qemuVirtDeploymentBootState_invariantBridge.1

end SeLe4n.Platform.QemuVirt
