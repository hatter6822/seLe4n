-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.Deployment

/-!
# Raspberry Pi 5 — the hardware boot entry (WS-BP BP4.1, BP4.4)

`rust_boot_main` calls `lean_kernel_main(dtb)` once, on the boot core, after the
library initializer (`rust/sele4n-hal/src/lean_entry.rs`).  This module is that
symbol.

The argument is the firmware's flattened device tree, copied by the HAL into a
Lean `ByteArray` (WS-BP BP4.3; an unreadable pointer is handed over as the empty
array, which the parser refuses).  The entry is the device-tree boot with its
failure handled, `Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt`, applied to
that blob and to BP3's deployment — and nothing else.  That is not a style
choice: `SeLe4n/Testing/BootEntryContract.lean` requires exactly this program,
decided by the elaborator, so an entry that sequenced another action around the
boot, installed state beside it, or booted a blob it did not receive would fail
to build.

What the device tree decides is whether this is a Raspberry Pi 5 and which RAM
variant it is.  A blob the verified parser refuses, or a board that does not
cover the binding's RAM and MMIO, halts every PE (`kernelMain_refuses`).  An
accepted board boots the deployment on the variant its account selects, and
nothing on that path can halt (`kernelMain_installs`): the deployment is proved
to boot on every member of the family (`bootAndInitialiseRPi5_rpi5PlatformConfigFor`),
and the variant validated and the variant installed are one value
(`rpi5PlatformConfigFromDtb_ok_binds_detected_variant`).
-/

namespace SeLe4n.Platform.RPi5

/-- The hardware boot entry: `lean_kernel_main`.

`dtb` is the firmware's device tree, at the type
`BootEntryContract.expectedBootEntryType` pins (`ByteArray → BaseIO Unit`); the
HAL owns the copy and hands its one reference over. -/
@[export lean_kernel_main]
def kernelMain (dtb : ByteArray) : BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt dtb rpi5IrqTable rpi5InitialObjects none

/-- **WS-BP BP4.4**: a device tree the bridge refuses — unparseable, or a board
that is not the one this image was built for — boots nothing: every PE halts. -/
theorem kernelMain_refuses (dtb : ByteArray) (e : Platform.FFI.DeviceTreeBootRefusal)
    (h : Platform.FFI.rpi5PlatformConfigFromDtb dtb rpi5IrqTable rpi5InitialObjects none =
      .error e) :
    kernelMain dtb = Platform.FFI.ffiFatalHaltAll :=
  Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt_unparseable _ _ _ _ e h

/-- **WS-BP BP4.4**: a device tree the bridge accepts installs the deployment's
boot state on the variant the board's account selects, and the binding's
labeling context, and nothing else — the halting boot's halt arm is never taken
on it (`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`, over every
account). -/
theorem kernelMain_installs (dtb : ByteArray) (config : Platform.Boot.PlatformConfig)
    (h : Platform.FFI.rpi5PlatformConfigFromDtb dtb rpi5IrqTable rpi5InitialObjects none =
      .ok config) :
    kernelMain dtb =
      (do
        Platform.FFI.initialiseKernelState
          (rpi5DeploymentBootStateAt (rpi5VariantFor config.machineConfig)).state
        Platform.FFI.initialiseKernelLabelingContext
          (PlatformBinding.labeling (platform := RPi5Platform))) := by
  unfold kernelMain
  rw [Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt_accepted _ _ _ _ config h,
    rpi5PlatformConfigFromDtb_deployment_ok dtb config h,
    bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor]
  rfl

/-- **WS-BP BP4.4**: ...and the state it installs satisfies the proof-layer
invariant bundle, whichever variant the device tree selected. -/
theorem kernelMain_installs_invariantBundle (config : Platform.Boot.PlatformConfig) :
    SeLe4n.Kernel.Architecture.proofLayerInvariantBundle
      (rpi5DeploymentBootStateAt (rpi5VariantFor config.machineConfig)).state :=
  (rpi5DeploymentBootStateAt_invariantBridge _ (rpi5VariantFor_mem _)).1

end SeLe4n.Platform.RPi5
