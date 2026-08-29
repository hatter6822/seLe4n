-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM5.C.5 reschedule-SGI kernel entry; the
-- receiver seam of the cross-core wake protocol, and the shared body of
-- the secondary-core bring-up entry)
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
import SeLe4n.Platform.FFI

/-!
# WS-SM SM5.C.5 — Per-core reschedule kernel entry

This module provides the Lean-side entry point that the Rust HAL's
`.reschedule` SGI handler (`trap.rs::reschedule_sgi_handler`, registered at
boot for SGI INTID 0 per the SM0.H reservation) calls into when a core takes
a `.reschedule` inter-processor interrupt.

## The receiver seam of the cross-core wake protocol

SM5.C's cross-core wake is a two-sided protocol.  The **sender** side has
been live since SM5.I: `wakeThread` enqueues the woken thread on its target
core's run queue and surfaces a `(targetCore, .reschedule)` SGI, which the
timer-tick / syscall entries fire via `Concurrency.fireCrossCoreSgis` after
their state commit.  The **receiver** side is this entry: the target core
takes the SGI, and the verified `handleRescheduleSgiOnCore` transition
re-chooses the highest-priority budget-eligible runnable thread and switches
to it only when it outranks the current thread in the selector's own
strict-preference order — higher resolved effective priority, or an earlier
resolved deadline at equal effective priority (`isBetterCandidate` over
`resolveEffectivePrioDeadline`; PR #880 round 7)
(`candidateOutranksCurrentOnCore` — a lower-priority wake never preempts).

Until this entry landed, the SGI's arrival merely woke the target core from
`wfe`; the dispatch of the woken thread waited for the target's next timer
tick (≤ 1 tick of added latency).  With the receiver live, the wake→dispatch
latency is the SGI delivery itself (`wakeThread_emits_at_most_one_sgi` +
the SM5.C.11 delivery bound), and the multi-step liveness witness
(`wakeThread_then_handle_dispatches_current`) describes the runtime path
exactly.

## Bring-up is the first reschedule

`Kernel.secondaryKernelMain` (the `lean_secondary_kernel_main` bring-up seam
in `SecondaryEntry.lean`) is definitionally this entry
(`secondaryKernelMain_eq_perCoreRescheduleEntry`): a freshly-onlined core has
`currentOnCore c = none`, so the outranks gate admits any budget-eligible
candidate and the handler dispatches the highest-priority runnable — the
core's idle thread when nothing else is assigned.  One verified step serves
both seams; there is no bespoke bring-up transition to prove or to drift.

## Runtime lock discipline

The entry commits through `Platform.FFI.updateKernelState` (an
`IO.Ref.modify` — a read then a write, not a cross-core atomic), so it MUST
run inside the kernel-entry lock: the Rust callers
(`trap.rs::reschedule_sgi_handler` and `smp.rs::rust_secondary_main`) both
wrap the call in `kernel_entry::with_kernel_entry`.  The bring-up caller
additionally runs **before** `enable_irq` on its core, so a timer tick can
never interrupt the bracketed bring-up entry and re-enter the non-reentrant
lock on the same core.

## Lean → Rust ABI contract

`@[export lean_per_core_reschedule]` instructs the Lean compiler to emit a
C-callable wrapper named `lean_per_core_reschedule` against which the Rust
side resolves `extern "C" { fn lean_per_core_reschedule(core_id: u64); }`
(gated on the HAL's `hw_target` feature).  The attribute is required so the
symbol is linkable.

## Build reachability and FFI-link isolation

Staged via `SeLe4n/Platform/Staged.lean` (added to the staged-module
allowlist per the WS-RC R12.B partition gate).  Unlike the timer-tick entry,
this entry references no `@[extern]` symbol (its commit is a pure
`IO.Ref.modify` and it fires no SGIs), so linking it demands nothing from the
Rust HAL; the FFI-link-isolation note on `PerCoreTimerEntry` does not apply
here.  The test suites that exercise the reschedule semantics import the
FFI-free `PerCoreRunLoop` (the verified `perCoreRescheduleStep`), not this
entry.
-/

namespace SeLe4n.Kernel

/-- **WS-SM SM5.C.5**: the per-core reschedule kernel entry — the receiver
seam of the cross-core wake protocol.  The C-callable seam
(`@[export lean_per_core_reschedule]`) the Rust `.reschedule` SGI handler
(`trap.rs::reschedule_sgi_handler`) invokes when a core takes SGI INTID 0,
and the definitional body of the secondary-core bring-up entry
(`secondaryKernelMain`).

Atomically runs the verified `perCoreRescheduleStep` against the live kernel
state (committing `handleRescheduleSgiOnCore`'s result).  See the module
docstring. -/
@[export lean_per_core_reschedule]
def perCoreRescheduleEntry (coreId : UInt64) : BaseIO Unit :=
  Platform.FFI.updateKernelState (fun st => perCoreRescheduleStep st coreId)

/-- **WS-SM SM5.C.5** structural marker: `perCoreRescheduleEntry` unfolds to
the atomic commit of the verified reschedule step.  Pins the entry's body
shape (an `updateKernelState` over `perCoreRescheduleStep`) so a refactor
that drops the state commit — or inserts side effects the verified step does
not describe — breaks this marker at elaboration; combined with the
`@[export]` attribute (which the Rust `lean_per_core_reschedule` extern
resolves against) and the `build.rs` trap-path scanner, the seam cannot
regress silently. -/
theorem perCoreRescheduleEntry_def (coreId : UInt64) :
    perCoreRescheduleEntry coreId =
      Platform.FFI.updateKernelState (fun st => perCoreRescheduleStep st coreId) := rfl

end SeLe4n.Kernel
