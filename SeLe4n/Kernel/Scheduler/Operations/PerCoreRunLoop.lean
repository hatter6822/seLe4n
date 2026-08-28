-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick

/-!
# WS-SM SM5.I — Per-core run-loop steps (the verified driver cores)

The pure, verified decision cores the per-core kernel entries run against live
kernel state.  Two steps live here:

* **`perCoreTimerTickStep`** — the timer-tick driver core
  (`Kernel.perCoreTimerTickEntry`, the `@[export lean_per_core_timer_tick]` seam
  the Rust CNTP ISR resolves).  At SM5.D the entry was a `pure ()` placeholder;
  SM5.I replaces it with a real driver that reads core `coreId`'s scheduler slots
  from the kernel-state `IO.Ref`, runs the **verified** `Kernel.timerTickOnCore`
  transition, commits its result, and fires the returned cross-core `.reschedule`
  SGIs.
* **`perCoreRescheduleStep`** — the `.reschedule`-SGI-receiver driver core
  (`Kernel.perCoreRescheduleEntry`, the `@[export lean_per_core_reschedule]` seam
  the Rust reschedule SGI handler resolves; also the body of the secondary-core
  bring-up entry `Kernel.secondaryKernelMain` — bring-up **is** the core's first
  reschedule).  It runs the **verified** `Kernel.handleRescheduleSgiOnCore`
  transition (SM5.C.5: budget-aware re-choose, preempt only when the candidate
  strictly outranks the current thread) and commits its result.  It emits no
  SGIs: a local dispatch wakes nothing remote.

This module holds the pure steps + their correctness theorems so each `BaseIO`
entry is a thin, side-effecting shell over a verified core (the SM5.F dispatch
pattern: pure decision core proven sound, `BaseIO` shell inert on the no-SGI
path).

## Fail-closed contract

Both steps decode the `UInt64` core id fail-closed: an out-of-range id
(`≥ numCores`) or a transition error (for the tick, a non-TCB current thread or a
bound-budget thread whose SchedContext is missing — R5.E; for the reschedule, a
corrupted run-queue selection) leaves the kernel state **unchanged** — and, for
the tick, emits **no** SGIs.  This is safe: the Rust ISR has already recorded the
per-core tick and re-armed the per-core comparator (or EOI'd the SGI) before
calling in, so a core reaching a no-op outcome is still fully serviced for the
interrupt.

## Runtime lock discipline

Each step runs under a kernel-entry lock, making its read-transition-commit
atomic against other cores.  **That lock is live as of SM5.I (v0.32.142)**:
`rust/sele4n-hal/src/kernel_entry.rs` holds it across every kernel entry that
commits state, which is what `IO.Ref.modifyGet` cannot supply on its own — it is
a read then a write, not a cross-core atomic, so without the bracket a tick
racing a syscall commit loses one transition whole (see
`Platform.FFI.modifyGetKernelState`).

It is held by the entry wrapper rather than by the trap handler itself, which is
the same exclusion at a slightly different seam: the per-core IRQ handler
(`trap.rs::handle_irq_per_core`) routes the timer PPI to
`timer::per_core_timer_tick_isr` and the `.reschedule` SGI to
`trap.rs::reschedule_sgi_handler`, and each ISR's bracket is immediately inside
it around its Lean call.  Until v0.32.142 this paragraph described the lock as
owed, and SMP was off by default for that reason; with the lock live the default
returns to decision #7's `smp_enabled: true`.  The finer-grained
`timerTickOnCoreLockSet` (SM5.D.3) cross-domain footprint over `SchedLockId`
(object-store ⊕ run-queue ⊕ replenish-queue write locks, ascending per plan §4.4 —
`timerTickOnCoreLockSet_pairwise_le`) certifies the 2PL acquisition order a future
per-object-locked migration consumes; the `SchedLockId`-level `withLockSet` bracket
itself is the SM3.C combinator's cross-domain extension (tracked).

## Build reachability

Staged via `SeLe4n/Platform/Staged.lean`; `Kernel.perCoreTimerTickEntry`,
`Kernel.perCoreRescheduleEntry` and `Kernel.secondaryKernelMain` consume it and
are themselves staged (the `@[export]` seams).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind)

/-- **WS-SM SM5.I** (the per-core run-loop step): drive the verified per-core timer
tick on core `coreId` against state `st`, returning the post-tick state paired with
the cross-core SGIs to fire.  Fail-closed (see the module docstring): an
out-of-range core id or a tick error yields `(st, [])`. -/
def perCoreTimerTickStep (st : SystemState) (coreId : UInt64) :
    SystemState × List (CoreId × SgiKind) :=
  if h : coreId.toNat < numCores then
    match timerTickOnCore st ⟨coreId.toNat, h⟩ with
    | .ok result => result
    | .error _ => (st, [])
  else (st, [])

/-- **WS-SM SM5.I**: an out-of-range core id is a no-op (state unchanged, no SGIs). -/
theorem perCoreTimerTickStep_invalid_core (st : SystemState) (coreId : UInt64)
    (h : ¬ coreId.toNat < numCores) :
    perCoreTimerTickStep st coreId = (st, []) := by
  unfold perCoreTimerTickStep; rw [dif_neg h]

/-- **WS-SM SM5.I**: on a valid core, a successful tick is committed verbatim. -/
theorem perCoreTimerTickStep_ok (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (result : SystemState × List (CoreId × SgiKind))
    (hok : timerTickOnCore st ⟨coreId.toNat, h⟩ = .ok result) :
    perCoreTimerTickStep st coreId = result := by
  unfold perCoreTimerTickStep; rw [dif_pos h, hok]

/-- **WS-SM SM5.I**: on a valid core, a tick error is a no-op (the Rust ISR has
already serviced the tick; the error short-circuits before any state write). -/
theorem perCoreTimerTickStep_error (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (e : KernelError)
    (herr : timerTickOnCore st ⟨coreId.toNat, h⟩ = .error e) :
    perCoreTimerTickStep st coreId = (st, []) := by
  unfold perCoreTimerTickStep; rw [dif_pos h, herr]

/-- **WS-SM SM5.I**: the step never *fabricates* SGIs — every emitted SGI comes from
the verified `timerTickOnCore` (the failure / out-of-range paths emit none).  So a
configuration in which `timerTickOnCore` emits no cross-core wake (every refilled
SchedContext homed on `c`) drives no cross-core IPI. -/
theorem perCoreTimerTickStep_sgis_eq_tick (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (result : SystemState × List (CoreId × SgiKind))
    (hok : timerTickOnCore st ⟨coreId.toNat, h⟩ = .ok result) :
    (perCoreTimerTickStep st coreId).2 = result.2 := by
  rw [perCoreTimerTickStep_ok st coreId h result hok]

/-- **WS-SM SM5.I** (soundness): the run-loop step preserves the object-store
invariant `invExt` — unconditionally, on every path.  The success path lifts
`timerTickOnCore_preserves_objects_invExt`; the failure / out-of-range paths return
`st` unchanged. -/
theorem perCoreTimerTickStep_preserves_objects_invExt (st : SystemState)
    (coreId : UInt64) (hInv : st.objects.invExt) :
    (perCoreTimerTickStep st coreId).1.objects.invExt := by
  by_cases h : coreId.toNat < numCores
  · cases hT : timerTickOnCore st ⟨coreId.toNat, h⟩ with
    | error e => rw [perCoreTimerTickStep_error st coreId h e hT]; exact hInv
    | ok result =>
        obtain ⟨st', sgis⟩ := result
        rw [perCoreTimerTickStep_ok st coreId h (st', sgis) hT]
        exact timerTickOnCore_preserves_objects_invExt st _ st' sgis hInv hT
  · rw [perCoreTimerTickStep_invalid_core st coreId h]; exact hInv

/-- **WS-SM SM5.I** (soundness): on a valid core, a successful step establishes the
SM4.C per-core current-thread validity on the ticked core — lifting SM5.D's
`timerTickOnCore_preserves_currentThreadValidOnCore`.  (The no-op paths are not
covered: they leave `st` whose pre-tick validity is the caller's to assume — the
substantive content is the success path, where the tick *re-establishes* validity
even when it preempts.) -/
theorem perCoreTimerTickStep_ok_currentThreadValidOnCore (st : SystemState)
    (coreId : UInt64) (h : coreId.toNat < numCores) (hInv : st.objects.invExt)
    (result : SystemState × List (CoreId × SgiKind))
    (hok : timerTickOnCore st ⟨coreId.toNat, h⟩ = .ok result) :
    currentThreadValidOnCore (perCoreTimerTickStep st coreId).1 ⟨coreId.toNat, h⟩ := by
  obtain ⟨st', sgis⟩ := result
  rw [perCoreTimerTickStep_ok st coreId h (st', sgis) hok]
  exact timerTickOnCore_preserves_currentThreadValidOnCore st _ st' sgis hInv hok

/-- **WS-SM SM5.C.5** (the reschedule run-loop step): drive the verified
`.reschedule` SGI handler on core `coreId` against state `st`, returning the
post-handler state.  Fail-closed (see the module docstring): an out-of-range core
id or a `handleRescheduleSgiOnCore` error yields `st` unchanged.

The same step is the secondary-core bring-up semantics
(`Kernel.secondaryKernelMain`): a freshly-onlined core has
`currentOnCore c = none`, so `candidateOutranksCurrentOnCore` admits any
budget-eligible candidate and the handler dispatches the highest-priority
runnable thread — the core's idle thread when nothing else is enqueued
(`idleThreadId c` sits in core `c`'s run queue at priority 0 on the
idle-installing boot path) — or is the identity when the run queue is empty.
Bring-up is therefore literally the core's first reschedule, and its correctness
is the SM5.C.5 theorem set, not a bespoke bring-up proof. -/
def perCoreRescheduleStep (st : SystemState) (coreId : UInt64) : SystemState :=
  if h : coreId.toNat < numCores then
    match handleRescheduleSgiOnCore st ⟨coreId.toNat, h⟩ with
    | .ok st' => st'
    | .error _ => st
  else st

/-- **WS-SM SM5.C.5**: an out-of-range core id is a no-op (state unchanged). -/
theorem perCoreRescheduleStep_invalid_core (st : SystemState) (coreId : UInt64)
    (h : ¬ coreId.toNat < numCores) :
    perCoreRescheduleStep st coreId = st := by
  unfold perCoreRescheduleStep; rw [dif_neg h]

/-- **WS-SM SM5.C.5**: on a valid core, a successful reschedule is committed
verbatim. -/
theorem perCoreRescheduleStep_ok (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (st' : SystemState)
    (hok : handleRescheduleSgiOnCore st ⟨coreId.toNat, h⟩ = .ok st') :
    perCoreRescheduleStep st coreId = st' := by
  unfold perCoreRescheduleStep; rw [dif_pos h, hok]

/-- **WS-SM SM5.C.5**: on a valid core, a reschedule error is a no-op (the Rust
handler has already EOI'd the SGI; the error short-circuits before any state
write). -/
theorem perCoreRescheduleStep_error (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (e : KernelError)
    (herr : handleRescheduleSgiOnCore st ⟨coreId.toNat, h⟩ = .error e) :
    perCoreRescheduleStep st coreId = st := by
  unfold perCoreRescheduleStep; rw [dif_pos h, herr]

/-- **WS-SM SM5.C.5** (soundness): the reschedule step preserves the object-store
invariant `invExt` — unconditionally, on every path.  The success path lifts
`handleRescheduleSgiOnCore_preserves_objects_invExt`; the failure / out-of-range
paths return `st` unchanged. -/
theorem perCoreRescheduleStep_preserves_objects_invExt (st : SystemState)
    (coreId : UInt64) (hInv : st.objects.invExt) :
    (perCoreRescheduleStep st coreId).objects.invExt := by
  by_cases h : coreId.toNat < numCores
  · cases hR : handleRescheduleSgiOnCore st ⟨coreId.toNat, h⟩ with
    | error e => rw [perCoreRescheduleStep_error st coreId h e hR]; exact hInv
    | ok st' =>
        rw [perCoreRescheduleStep_ok st coreId h st' hR]
        exact handleRescheduleSgiOnCore_preserves_objects_invExt st _ st' hInv hR
  · rw [perCoreRescheduleStep_invalid_core st coreId h]; exact hInv

/-- **WS-SM SM5.C.5** (soundness): the reschedule step preserves **every** core's
run-queue well-formedness.  The rescheduled core lifts
`handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed`; every other core
lifts the cross-core-independence frame
(`handleRescheduleSgiOnCore_independent_of_other_core`); the failure /
out-of-range paths return `st` unchanged. -/
theorem perCoreRescheduleStep_preserves_runQueue_wellFormed (st : SystemState)
    (coreId : UInt64)
    (hwf : ∀ c : CoreId, (st.scheduler.runQueueOnCore c).wellFormed) :
    ∀ c : CoreId,
      ((perCoreRescheduleStep st coreId).scheduler.runQueueOnCore c).wellFormed := by
  intro c
  by_cases h : coreId.toNat < numCores
  · cases hR : handleRescheduleSgiOnCore st ⟨coreId.toNat, h⟩ with
    | error e => rw [perCoreRescheduleStep_error st coreId h e hR]; exact hwf c
    | ok st' =>
        rw [perCoreRescheduleStep_ok st coreId h st' hR]
        by_cases hc : (⟨coreId.toNat, h⟩ : CoreId) = c
        · subst hc
          exact handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed
            st _ st' (hwf _) hR
        · rw [(handleRescheduleSgiOnCore_independent_of_other_core
            st _ c st' hc hR).2]
          exact hwf c
  · rw [perCoreRescheduleStep_invalid_core st coreId h]; exact hwf c

/-- **WS-SM SM5.C.5** (the substantive bring-up / dispatch witness): on a valid
core, when the budget-aware re-choose selects `tid` and `tid` outranks the
current thread (vacuously true at secondary bring-up, where
`currentOnCore c = none`), the committed state runs `tid` on that core.  This is
the scheduler-entry correctness witness the SM1.C.6 placeholder marker promised:
the entry does not merely return — it establishes `currentOnCore`. -/
theorem perCoreRescheduleStep_switches_current (st : SystemState)
    (coreId : UInt64) (h : coreId.toNat < numCores) (tid : SeLe4n.ThreadId)
    (st' : SystemState)
    (hc : chooseThreadEffectiveOnCore st ⟨coreId.toNat, h⟩ = .ok (some tid))
    (hout : candidateOutranksCurrentOnCore st ⟨coreId.toNat, h⟩ tid = true)
    (hok : handleRescheduleSgiOnCore st ⟨coreId.toNat, h⟩ = .ok st') :
    (perCoreRescheduleStep st coreId).scheduler.currentOnCore ⟨coreId.toNat, h⟩
      = some tid := by
  rw [perCoreRescheduleStep_ok st coreId h st' hok]
  exact handleRescheduleSgiOnCore_switches_current st _ tid st' hc hout hok

end SeLe4n.Kernel
