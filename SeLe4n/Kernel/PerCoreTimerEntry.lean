-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Platform.FFI

/-!
# WS-SM SM5.D.1 — Per-core timer-tick kernel entry

This module provides the Lean-side entry point that the Rust HAL's per-core CNTV
timer ISR (`timer::per_core_timer_tick_isr`, see `rust/sele4n-hal/src/timer.rs`)
calls into on each per-core timer interrupt, after recording the per-core tick and
re-arming the per-core comparator.

## SM5.D.1 placeholder semantics

At SM5.D the function is intentionally a pass-through that returns `pure ()`.  The
*pure* per-core timer transition — `Kernel.timerTickOnCore` (plan §3.4), with its
SM5.D.4 CBS replenishment, SM5.D.6 domain rotation, and SM5.D.5 budget-tick
preemption — is fully specified and verified in
`SeLe4n/Kernel/Scheduler/Operations/Core.lean` +
`SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean`.  What this entry does
*not* yet do is drive that transition against live per-core kernel state: reading
core `coreId`'s `SchedulerState` slots from the kernel-state `IO.Ref`, committing
`timerTickOnCore`'s result under the `timerTickOnCoreLockSet` `withLockSet`
bracket, and emitting the returned cross-core `.reschedule` SGIs via
`Concurrency.emitWakeSgi`.  That runtime wiring needs the per-core kernel-state
seam SM5.I introduces (the single-`SystemState` `IO.Ref` is system-wide; per-core
dispatch needs the SM5.I per-core invariant suite + the per-core scheduler-state
partition).  Returning immediately at SM5.D is **deliberate** — the Rust ISR has
already recorded the per-core tick and re-armed the comparator, so a core that
reaches this entry is fully serviced for the tick; SM5.I replaces this body with
the per-core scheduler-tick driver.

## Lean → Rust ABI contract

`@[export lean_per_core_timer_tick]` instructs the Lean compiler to emit a
C-callable wrapper named `lean_per_core_timer_tick` against which the Rust side
resolves `extern "C" { fn lean_per_core_timer_tick(core_id: u64); }` (gated on the
HAL's `hw_target` feature).  The attribute is required so the symbol is linkable.

## Build reachability

Staged via `SeLe4n/Platform/Staged.lean` (added to the staged-module allowlist per
the WS-RC R12.B partition gate); SM5.I moves it production-reached when the
per-core scheduler-tick driver lands.
-/

namespace SeLe4n.Kernel

/-- **WS-SM SM5.D.1**: the per-core timer-tick kernel entry.  The C-callable seam
(`@[export lean_per_core_timer_tick]`) the Rust per-core CNTV ISR
(`timer::per_core_timer_tick_isr`) invokes on each per-core timer interrupt.

At SM5.D a deliberate `pure ()` placeholder (see the module docstring) — the pure
`timerTickOnCore` transition is verified; SM5.I wires this entry to drive it
against live per-core kernel state under the `timerTickOnCoreLockSet` bracket. -/
@[export lean_per_core_timer_tick]
def perCoreTimerTickEntry (_coreId : UInt64) : BaseIO Unit :=
  pure ()

/-- **WS-SM SM5.D.1** structural marker: `perCoreTimerTickEntry` returns unit.

A trivial witness used as a tier-3 surface anchor — the entry takes a `UInt64`
core id and returns `BaseIO Unit`.  A rename / signature change of the export
(which the Rust `lean_per_core_timer_tick` extern resolves against) breaks this
marker at elaboration before reaching the link step. -/
theorem perCoreTimerTickEntry_returns_unit_marker (coreId : UInt64) :
    perCoreTimerTickEntry coreId = pure () := rfl

end SeLe4n.Kernel
