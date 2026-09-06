-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR5.15: PRODUCTION.  This module was staged-only, which meant
-- `@[export lean_per_core_reschedule]` emitted no symbol into the library a
-- kernel image links — while `trap.rs` declared it as a hard `extern "C"` for
-- the `.reschedule` SGI handler.  It is now in `SeLe4n.lean`'s import closure;
-- `scripts/check_kernel_entry_exports.py` verifies the symbol against the built
-- archive on every Tier-1 run.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
import SeLe4n.Platform.FFI
import SeLe4n.Kernel.SchedLockBracket

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

## Recording the choice on the HAL (WS-RR RR7.26)

The verified step decides which thread this core runs; the HAL keeps a
per-core mirror of that decision (`ffi::PER_CPU_CURRENT_THREAD`) which a
dispatch path reads to know whose context to resume.  Until RR7.26 the two
were never connected — `Concurrency.switchToThreadHw` had *zero* production
callers while both sides' docstrings described it as the seam.  The entry now
reads the committed post-state's `currentOnCore` inside the same atomic step
and records it through `Concurrency.recordCommittedCurrentThreadHw`.

A transition that *vacates* the core clears the mirror rather than leaving it
naming a descheduled thread; a raw core id the model has no core for records
nothing, matching the verified step, which commits nothing for such an id.

## Build reachability and FFI linkage

Production since WS-RR RR5.15 (see the header note).  RR7.26 gave this entry
its first `@[extern]` reference — `ffiSwitchToThread`, through the typed
`Concurrency` wrappers — so the FFI-link-isolation note that stood here is no
longer true of it: linking this module now demands the same HAL symbols
`PerCoreTimerEntry` does.

That has a consequence for the host, and RR7.16 is where it surfaced.  The
suites that exercise the reschedule *semantics* import the FFI-free
`PerCoreRunLoop` (the verified `perCoreRescheduleStep`), not this entry — but
`tests/SmpFoundationsSuite.lean` §2.17 used to **execute** this entry, and a
Lean test executable links no Rust.  It linked before RR7.26 only because
`--gc-sections` dropped the unreachable `@[extern]` calls; with the record
wired, `ffi_switch_to_thread` became reachable from that suite's `main` and
the link failed.

**A Lean host executable cannot run a kernel entry that reaches the HAL**, and
the link says so, fail-closed, with no gate to write.  Stubbing the seam from
Lean is not the way out: an `@[export]` of a HAL symbol name is a second
definition of it in whatever archive carries that module — a duplicate at the
SM10.1 image link at best, and at worst one the linker silently prefers over
the HAL, discarding every scheduling decision the kernel makes.  That hazard
is refused by `scripts/check_kernel_entry_exports.py`, which fails when the
static archive defines any symbol the Lean tree declares `@[extern]`.  §2.17
therefore asserts the two *pure* halves this body composes — the empty-queue
step dispatches nobody, and an out-of-range id names no core — which are
stronger claims than the invocation's "it did not fault", and this entry's
`_def` marker pins the composition itself.
-/

namespace SeLe4n.Kernel

/-- **WS-SM SM5.C.5**: the per-core reschedule kernel entry — the receiver
seam of the cross-core wake protocol.  The C-callable seam
(`@[export lean_per_core_reschedule]`) the Rust `.reschedule` SGI handler
(`trap.rs::reschedule_sgi_handler`) invokes when a core takes SGI INTID 0,
and the definitional body of the secondary-core bring-up entry
(`secondaryKernelMain`).

Atomically runs the verified `perCoreRescheduleStep` against the live kernel
state (committing `handleRescheduleSgiOnCore`'s result) **inside the footprint
this core declares** (**WS-RR RR7.39** — `rescheduleUnderDeclaredLockSet`, the
object-store table write lock and this core's run-queue write lock), then records
the thread that step left running on this core in the HAL's per-core mirror
(**WS-RR RR7.26**).  Both reads of the post-state happen inside the one atomic
step, so the value recorded is the value committed.

The bracket's three outcomes all carry a state, and `LockBracketOutcome.state` is
the one definition that projects it — so a refused bracket records the *unwound*
state, which is the pre-state with nothing committed but the lock withdrawal.
`perCoreRescheduleStep_coversWrites` proves the step's writes lie inside the
declared footprint, so the footprint is not a false one.  See the module
docstring. -/
@[export lean_per_core_reschedule]
def perCoreRescheduleEntry (coreId : UInt64) : BaseIO Unit := do
  let record ← Platform.FFI.modifyGetKernelState (fun st =>
    let st' := (rescheduleUnderDeclaredLockSet coreId st).state
    ((Concurrency.coreIdOfUInt64? coreId).map
      (fun c => (c, st'.scheduler.currentOnCore c)), st'))
  Concurrency.recordCommittedCurrentThreadHw record

/-- **WS-SM SM5.C.5** structural marker: `perCoreRescheduleEntry` unfolds to
the atomic commit of the bracketed reschedule step followed by the HAL
current-thread record.  Pins the entry's body shape (a `modifyGetKernelState`
over `rescheduleUnderDeclaredLockSet` returning the decoded core with its
committed `currentOnCore`, then `recordCommittedCurrentThreadHw`) so a refactor
that drops the state commit, drops the record, drops the declared-footprint
bracket (**WS-RR RR7.39**), or inserts side effects the verified step does not
describe breaks this marker at elaboration; combined with the `@[export]`
attribute (which the Rust `lean_per_core_reschedule` extern resolves against)
and the `build.rs` trap-path scanner, the seam cannot regress silently. -/
theorem perCoreRescheduleEntry_def (coreId : UInt64) :
    perCoreRescheduleEntry coreId =
      (do
        let record ← Platform.FFI.modifyGetKernelState (fun st =>
          let st' := (rescheduleUnderDeclaredLockSet coreId st).state
          ((Concurrency.coreIdOfUInt64? coreId).map
            (fun c => (c, st'.scheduler.currentOnCore c)), st'))
        Concurrency.recordCommittedCurrentThreadHw record) := rfl

end SeLe4n.Kernel
