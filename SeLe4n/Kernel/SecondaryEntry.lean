-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR5.15: PRODUCTION.  This module was staged-only, which meant
-- `@[export lean_secondary_kernel_main]` emitted no symbol into the library a
-- kernel image links — while `smp.rs` declared it as a hard `extern "C"`.  It is
-- now in `SeLe4n.lean`'s import closure; `scripts/check_kernel_entry_exports.py`
-- verifies the symbol against the built archive on every Tier-1 run.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.PerCoreRescheduleEntry
import SeLe4n.Platform.FFI

/-!
# WS-SM SM1.C.6 / SM5.C.5 — Secondary-core kernel entry

This module provides the Lean-side entry point that the Rust HAL's
`rust_secondary_main` (see `rust/sele4n-hal/src/smp.rs`) calls into
after completing the per-core hardware-init sequence (MMU, VBAR, GIC
CPU interface, timer) and **before** unmasking IRQs on the core.

## Bring-up semantics: the core's first reschedule

At SM1.C this function was a deliberate `pure ()` pass-through — the
per-core scheduler state it would enter did not exist yet.  SM5 built that
state (per-core run queues, idle TCBs, the verified selection / switch /
reschedule transitions), and this entry now runs it: the body is
definitionally the per-core reschedule entry
(`perCoreRescheduleEntry`, the `.reschedule` SGI receiver), because bring-up
**is** the core's first reschedule.

A freshly-onlined core has `currentOnCore c = none`
(`bootFromPlatform_smp_currentAllNone`), so the reschedule's
`candidateOutranksCurrentOnCore` gate admits any budget-eligible candidate
and the verified `handleRescheduleSgiOnCore` transition dispatches the
highest-priority runnable thread assigned to this core — the core's idle
thread when nothing else is enqueued (the idle-installing boot path parks
`idleThreadId c` in core `c`'s run queue at priority 0), or the identity
when the run queue is empty (the state then keeps the legacy
`current = none` idle representation until the first wake or tick).  One
verified step serves the bring-up and SGI-receiver seams; the bring-up
correctness witness is `perCoreRescheduleStep_switches_current`, and there
is no bespoke bring-up transition to prove or to drift.

## Runtime lock discipline (why the Rust caller brackets and orders this)

The entry commits kernel state through an `IO.Ref.modify` — a read then a
write, not a cross-core atomic — while sibling cores are already executing
bracketed kernel entries (their timer ticks and SGIs).  The Rust caller
therefore wraps this call in `kernel_entry::with_kernel_entry`, and invokes
it **before** `enable_irq` on this core: with IRQs still masked, a per-core
timer tick cannot interrupt the bracketed bring-up entry and re-enter the
non-reentrant kernel-entry lock on the same core (the same
IRQs-masked-while-held discipline every other kernel entry observes).  A
core that has not yet published `CORE_IRQ_READY` is excluded from every
shootdown round, so the bracket's self-service spin has no obligation to
discharge and the acquisition terminates.

## Lean → Rust ABI contract

`@[export lean_secondary_kernel_main]` instructs the Lean compiler to
emit a C-callable wrapper named `lean_secondary_kernel_main` against
which the Rust side resolves
`extern "C" { fn lean_secondary_kernel_main(core_id: u64); }`.  The
attribute is required so the symbol is linkable; without it the Rust
extern would fail at link time.

## Build reachability

This module is in the CI import closure via
`SeLe4n/Platform/Staged.lean` (staged-module allowlist per the WS-RC
R12.B partition gate).  Like `PerCoreRescheduleEntry` — and unlike the
timer-tick entry — the body references no `@[extern]` symbol, so linking
it demands nothing from the Rust HAL.

## Anti-cycle note

`Concurrency.Types` is foundational (no `Platform.*` deps).
`Platform.FFI` imports `Platform.Boot`, which transitively imports
`Platform.Contract` → `Concurrency.Types`.  This file imports both
(plus `Kernel.PerCoreRescheduleEntry`, which sits above `Platform.FFI`):

```
Concurrency.Types  ← Platform.Contract  ← Platform.Boot
                                        ← Platform.FFI
                                        ← PerCoreRescheduleEntry
                                        ← SecondaryEntry (this file)
```

A future refactor that moved this file's logic into `Concurrency.*`
would break layering — `Concurrency.*` must not depend on
`Platform.*`.
-/

namespace SeLe4n.Kernel

/-- **WS-SM SM1.C.6 / SM5.C.5** (closes SMP-C2 Lean side): Secondary-core
kernel entry.

Called from Rust `smp.rs::rust_secondary_main` once per secondary core,
inside `kernel_entry::with_kernel_entry` and before `enable_irq`, after the
per-core hardware-init sequence (MMU, VBAR, GIC, timer) completes.

The `coreId` argument is the PSCI `context_id` (1..=`MAX_SECONDARY_CORES`
on RPi5); the verified step decodes it fail-closed
(`perCoreRescheduleStep_invalid_core`), so an out-of-range id commits
nothing.

The body is definitionally the per-core reschedule entry — bring-up is the
core's first reschedule (see the module docstring). -/
@[export lean_secondary_kernel_main]
def secondaryKernelMain (coreId : UInt64) : BaseIO Unit :=
  perCoreRescheduleEntry coreId

/-- **WS-SM SM5.C.5** structural marker: the secondary bring-up entry IS the
reschedule entry — `rfl`, because that is the literal definition.  This is
the substantive scheduler-entry correctness witness the SM1.C.6 placeholder
marker (`secondaryKernelMain_returns_unit_marker`, retired with the
placeholder) promised: through `perCoreRescheduleEntry_def`, the bring-up
entry atomically commits the verified `perCoreRescheduleStep`, whose
dispatch witness is `perCoreRescheduleStep_switches_current`.  Pinning the
equality here means the two seams cannot drift apart: any future change to
bring-up semantics must go through the shared verified step. -/
theorem secondaryKernelMain_eq_perCoreRescheduleEntry (coreId : UInt64) :
    secondaryKernelMain coreId = perCoreRescheduleEntry coreId := rfl

/-- **WS-SM SM5.C.5**: the bring-up entry unfolds to the atomic commit of the
verified reschedule step (the composition of
`secondaryKernelMain_eq_perCoreRescheduleEntry` with
`perCoreRescheduleEntry_def`, stated directly so tier-3 surface scans can
pin the full body shape at one name). -/
theorem secondaryKernelMain_def (coreId : UInt64) :
    secondaryKernelMain coreId =
      Platform.FFI.updateKernelState (fun st => perCoreRescheduleStep st coreId) := rfl

end SeLe4n.Kernel
