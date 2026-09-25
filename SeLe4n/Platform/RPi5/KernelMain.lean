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
# Raspberry Pi 5 — the hardware boot entry (WS-BP BP4.1)

`rust_boot_main` calls `lean_kernel_main(dtb_ptr)` once, on the boot core, after
the library initializer (`rust/sele4n-hal/src/lean_entry.rs`).  This module is
that symbol.

The entry is the checked RPi5 boot, with its failure handled, applied to BP3's
deployment — and nothing else.  That is not a style choice:
`SeLe4n/Testing/BootEntryContract.lean` requires exactly this program, decided by
the elaborator, so an entry that sequenced another action around the boot, or
installed state beside it, would fail to build.  Why nothing precedes or follows
the boot is recorded there.

What the entry does not yet read is the device-tree pointer.  The
configuration is `rpi5PlatformConfig`, which fixes the smallest board as the
board account; `bindPlatformConfig` then binds the machine configuration the
RPi5 binding declares for it.  Reading the firmware's blob into a `ByteArray`
is a Lean-runtime allocation, and moving the entry onto the DTB-driven wrapper
(`bootAndInitialiseRPi5FromDtbOrHalt`) is WS-BP BP4.3–BP4.4.  Until then the
pointer is accepted at the type the `extern "C"` declaration is called at and
not consulted.

What the boot this entry runs establishes is proved of the state it installs:
`rpi5PlatformConfig_boots` (it succeeds and installs both separation witnesses),
`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig` (the halting entry never halts
on it) and `rpi5DeploymentBootState_invariantBridge` (the proof-layer bundle of
the installed state, and the frozen API bundle across the freeze).
-/

namespace SeLe4n.Platform.RPi5

/-- The hardware boot entry: `lean_kernel_main`.

The `UInt64` is the DTB pointer `rust_boot_main` passes, at the type
`BootEntryContract.expectedBootEntryType` pins; it is not read until the entry
moves onto the DTB-driven wrapper (WS-BP BP4.4). -/
@[export lean_kernel_main]
def kernelMain (_dtbPointer : UInt64) : BaseIO Unit :=
  Platform.FFI.bootAndInitialiseRPi5OrHalt rpi5PlatformConfig

/-- What the entry does, as a program: it installs the deployment's boot state
and the binding's labeling context, and nothing else — the halting boot's halt
arm is never taken on this configuration
(`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig`). -/
theorem kernelMain_installs (dtbPointer : UInt64) :
    kernelMain dtbPointer =
      (do
        Platform.FFI.initialiseKernelState rpi5DeploymentBootState.state
        Platform.FFI.initialiseKernelLabelingContext
          (PlatformBinding.labeling (platform := RPi5Platform))) :=
  bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig

end SeLe4n.Platform.RPi5
