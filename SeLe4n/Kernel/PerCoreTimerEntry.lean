-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
import SeLe4n.Platform.FFI

/-!
# WS-SM SM5.D.1 / SM5.I — Per-core timer-tick kernel entry

This module provides the Lean-side entry point that the Rust HAL's per-core CNTP
timer ISR (`timer::per_core_timer_tick_isr`, see `rust/sele4n-hal/src/timer.rs`)
calls into on each per-core timer interrupt, after recording the per-core tick and
re-arming the per-core comparator.

## SM5.I — the live per-core scheduler-tick driver

At SM5.D this entry was a `pure ()` placeholder; **SM5.I replaces it with the real
driver**.  On each per-core timer interrupt the entry now:

1. reads the live kernel `SystemState` and, **atomically** (one
   `modifyGetKernelState`), runs the verified `Kernel.perCoreTimerTickStep` —
   which decodes the `coreId`, drives the verified `Kernel.timerTickOnCore`
   transition (SM5.D.4 CBS replenishment, SM5.D.5 budget-tick preemption, SM5.D.6
   domain re-dispatch), commits the new state, and recovers the cross-core SGIs;
2. **fires** the recovered cross-core `.reschedule` SGIs via
   `Concurrency.fireCrossCoreSgis` — the SM5.F dispatch that actually pokes the
   remote cores' GIC (after the state write is visible, per the SM1.F.8 ordering).

The pure decision core is fully verified in
`SeLe4n/Kernel/Scheduler/Operations/PerCoreRunLoop.lean`
(`perCoreTimerTickStep_preserves_objects_invExt`,
`perCoreTimerTickStep_ok_currentThreadValidOnCore`, fail-closed reductions); this
entry is the thin `BaseIO` shell over it (the SM5.F pattern: verified pure core +
side-effecting shell that is inert on the no-SGI path —
`Concurrency.fireCrossCoreSgis [] = pure ()`).

The read-tick-commit is atomic under a single `IO.Ref.modifyGet`, and on hardware
runs under the big kernel lock the trap handler holds.  The finer-grained
`timerTickOnCoreLockSet` cross-domain footprint (SM5.D.3) certifies the 2PL
acquisition order a future per-object-locked migration consumes; the
`SchedLockId`-level `withLockSet` bracket itself is the SM3.C combinator's
cross-domain extension (tracked SM5.I closure target).

## Lean → Rust ABI contract

`@[export lean_per_core_timer_tick]` instructs the Lean compiler to emit a
C-callable wrapper named `lean_per_core_timer_tick` against which the Rust side
resolves `extern "C" { fn lean_per_core_timer_tick(core_id: u64); }` (gated on the
HAL's `hw_target` feature).  The attribute is required so the symbol is linkable.

## Build reachability and FFI-link isolation

Staged via `SeLe4n/Platform/Staged.lean` (added to the staged-module allowlist per
the WS-RC R12.B partition gate).

This driver references the `ffiSendSgi` extern transitively (via
`Concurrency.fireCrossCoreSgis`), and `@[export]` keeps the symbol live — so an
executable that *linked* this module would demand `ffi_send_sgi` at link time.
The guarantee that no test executable hits that is **link-isolation by
non-import**: no `lake exe` root imports this module.  `Main.lean` reaches only
`SeLe4n` + `MainTraceHarness`; the test suites that exercise the per-core tick
(`SmpTimerSuite`) deliberately import the FFI-free `PerCoreRunLoop` (the verified
`perCoreTimerTickStep`) and **not** this entry.  The only importers are
`Platform/Staged.lean` (a library build anchor, not an exe root, so no link step)
and `PerCoreTimerInventory.lean` (likewise).  The entry's signature +
`perCoreTimerTickEntry_def` body-shape marker are surfaced as tier-3 elaboration
anchors (no exe link).  The real kernel image (a future `[[bin]]` target) *will*
link the HAL, so `ffi_send_sgi` resolves there.
-/

namespace SeLe4n.Kernel

/-- **WS-SM SM5.I**: the per-core timer-tick kernel entry — the live driver.  The
C-callable seam (`@[export lean_per_core_timer_tick]`) the Rust per-core CNTP ISR
(`timer::per_core_timer_tick_isr`) invokes on each per-core timer interrupt.

Atomically runs the verified `perCoreTimerTickStep` against the live kernel state
(committing `timerTickOnCore`'s result), then fires the recovered cross-core
`.reschedule` SGIs.  See the module docstring. -/
@[export lean_per_core_timer_tick]
def perCoreTimerTickEntry (coreId : UInt64) : BaseIO Unit := do
  let sgis ← Platform.FFI.modifyGetKernelState (fun st =>
    let result := perCoreTimerTickStep st coreId
    (result.2, result.1))
  Concurrency.fireCrossCoreSgis sgis

/-- **WS-SM SM5.I** structural marker: `perCoreTimerTickEntry` unfolds to the
verified-step-then-fire-SGIs driver.  Pins the entry's body shape (atomic
`modifyGetKernelState` over `perCoreTimerTickStep`, then `fireCrossCoreSgis`) so a
refactor that drops the SGI firing or the state commit breaks this marker at
elaboration; combined with the `@[export]` attribute (which the Rust
`lean_per_core_timer_tick` extern resolves against) and the `build.rs` Check-5
scanner, the seam cannot regress silently. -/
theorem perCoreTimerTickEntry_def (coreId : UInt64) :
    perCoreTimerTickEntry coreId =
      (Platform.FFI.modifyGetKernelState (fun st =>
        let result := perCoreTimerTickStep st coreId
        (result.2, result.1)) >>= Concurrency.fireCrossCoreSgis) := rfl

end SeLe4n.Kernel
