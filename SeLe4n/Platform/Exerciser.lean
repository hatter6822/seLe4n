-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.Exerciser
import SeLe4n.Platform.QemuVirt.Exerciser

/-!
# The allocation exerciser's library root (WS-ZA ZA5.13, WS-RB RB3)

The root of the `SeLe4nExerciser` library: the exerciser's deployment
(`SeLe4n/Platform/Exerciser/Deployment.lean`) and its two boards' entries,
`lean_kernel_main_rpi5_exerciser` (`SeLe4n/Platform/RPi5/Exerciser.lean`) and
`lean_kernel_main_qemu_virt_exerciser`
(`SeLe4n/Platform/QemuVirt/Exerciser.lean`).  An exerciser image runs this
module's initializer in place of the kernel's root's
(`rust/sele4n-hal/src/lean_entry.rs`), which initializes the kernel and then
both entries' modules, and calls its own board's entry.
-/
