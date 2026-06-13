-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Machine
import SeLe4n.Model.Object
import SeLe4n.Model.State
-- WS-SM SM3.A audit-pass-6: pull the SM3.A theorem inventory into the
-- production import closure so `lake build` (default target) catches
-- regressions in the 34-entry aggregator at the production-build step,
-- not just at the Tier-3 invariant-surface or test-suite levels.  The
-- inventory has no run-time semantics (it is a documentation/audit
-- artifact); production reachability ensures CI cannot drop it
-- silently.
import SeLe4n.Model.Object.PerObjectLockInventory
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.VSpaceBackend
import SeLe4n.Kernel.Architecture.TlbModel
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Platform.Contract
import SeLe4n.Platform.Boot
import SeLe4n.Platform.FFI
import SeLe4n.Platform.Sim.Contract
import SeLe4n.Platform.RPi5.Contract
-- WS-SM SM6.A (live cross-core `.call` completion): the cross-core syscall
-- dispatch entry `syscallDispatchCrossCoreEntry`
-- (`@[export lean_syscall_dispatch_cross_core]`) — the live seam the Rust SVC
-- handler resolves against, which fires the diff-recovered cross-core
-- `.reschedule` SGIs.  Pulls its closure (`Concurrency.Runtime`,
-- `Scheduler.PriorityInheritance.PerCore`) into the production library so the
-- `@[export]` symbol is emitted into the kernel image.
import SeLe4n.Kernel.SyscallDispatchEntry
