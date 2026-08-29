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
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind bootCoreId)

/-- **WS-SM SM5.I** (single-authority clock): the boot-core-conditional machine
clock advance the run-loop step applies before the tick transition reads
`machine.timer`.  Exactly one core — the boot core — advances the shared clock,
once per tick; every other core's step reads the clock the boot core last
committed.  Factored as a named state function so the step's theorems can
frame it (`tickClockedState_objects`) and so the SGI/commit statements name
the state the tick actually ran against. -/
def tickClockedState (st : SystemState) (c : CoreId) : SystemState :=
  if c = bootCoreId then { st with machine := tick st.machine } else st

/-- **WS-SM SM5.I**: the clock advance never touches the object store. -/
@[simp] theorem tickClockedState_objects (st : SystemState) (c : CoreId) :
    (tickClockedState st c).objects = st.objects := by
  unfold tickClockedState; split <;> rfl

/-- **WS-SM SM5.I**: the clock advance never touches the scheduler state. -/
@[simp] theorem tickClockedState_scheduler (st : SystemState) (c : CoreId) :
    (tickClockedState st c).scheduler = st.scheduler := by
  unfold tickClockedState; split <;> rfl

/-- **WS-SM SM5.I**: on the boot core the clock advances by exactly one. -/
theorem tickClockedState_bootCore_timer (st : SystemState) :
    (tickClockedState st bootCoreId).machine.timer = st.machine.timer + 1 := by
  unfold tickClockedState; rw [if_pos rfl]; exact tick_timer_succ st.machine

/-- **WS-SM SM5.I**: on a non-boot core the clock is untouched (the
single-authority rule: only the boot core advances the shared clock). -/
theorem tickClockedState_nonBoot (st : SystemState) (c : CoreId)
    (hc : c ≠ bootCoreId) : tickClockedState st c = st := by
  unfold tickClockedState; rw [if_neg hc]

/-- **WS-SM SM5.I** (the per-core run-loop step): drive the verified per-core
timer tick on core `coreId` against state `st`, returning the post-tick state
paired with the cross-core SGIs to fire.  Three verified pieces compose, in
order:

1. **Boot-core clock advance.**  On the boot core — and only there, the
   single-authority rule — the shared machine clock advances by one
   (`machine := tick st.machine`) *before* the tick transition reads it, so
   CBS replenishments and IPC timeouts that fall due this tick actually fire.
   The single-core `timerTick` / `timerTickWithBudget` advanced the clock on
   every committed path; the per-core `timerTickOnCore` deliberately reads
   without advancing (each core's CNTP is local), so the advance is re-homed
   here at the composition point, once per global tick, never per core.
2. **`timerTickOnCore`** — SM5.D budget accounting, CBS replenishment,
   budget-exhaustion preemption; recovers the cross-core `.reschedule` SGIs.
3. **`scheduleDomainOnCore`** — SM5.D.6 domain accounting: the in-domain
   decrement, or the boundary re-dispatch — the rotating arm's
   `switchDomainOnCore` preparation + rotation, or the empty-schedule arm's
   `singleDomainBoundaryPrep` (the same save → re-enqueue → clear-current
   preparation, so the outgoing current competes in the re-dispatch and is
   never dropped) — each followed by the budget-aware
   `scheduleEffectiveOnCore`.  The tick does budget accounting **only** (its
   own docstring: rotation folded into the tick breaks
   `currentThreadInActiveDomain`), so the run loop must invoke both —
   exactly as the single-core run loop invokes `timerTickWithBudget` then
   `scheduleDomain`.  The domain arm emits no SGIs; the step's SGI list is
   the tick's.

Fail-closed, all-or-nothing (see the module docstring): an out-of-range core
id, a tick error, or a domain-transition error yields `(st, [])` — an errored
entry commits nothing, the clock advance included. -/
def perCoreTimerTickStep (st : SystemState) (coreId : UInt64) :
    SystemState × List (CoreId × SgiKind) :=
  if h : coreId.toNat < numCores then
    match timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ with
    | .error _ => (st, [])
    | .ok result =>
        match scheduleDomainOnCore result.1 ⟨coreId.toNat, h⟩ with
        | .error _ => (st, [])
        | .ok st2 => (st2, result.2)
  else (st, [])

/-- **WS-SM SM5.I**: an out-of-range core id is a no-op (state unchanged, no SGIs). -/
theorem perCoreTimerTickStep_invalid_core (st : SystemState) (coreId : UInt64)
    (h : ¬ coreId.toNat < numCores) :
    perCoreTimerTickStep st coreId = (st, []) := by
  unfold perCoreTimerTickStep; rw [dif_neg h]

/-- **WS-SM SM5.I**: on a valid core, a successful tick (against the clocked
state) followed by a successful domain transition is committed verbatim — the
domain arm's state paired with the tick's SGIs. -/
theorem perCoreTimerTickStep_ok (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (result : SystemState × List (CoreId × SgiKind))
    (st2 : SystemState)
    (hok : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩
      = .ok result)
    (hdom : scheduleDomainOnCore result.1 ⟨coreId.toNat, h⟩ = .ok st2) :
    perCoreTimerTickStep st coreId = (st2, result.2) := by
  unfold perCoreTimerTickStep; rw [dif_pos h, hok]; simp only [hdom]

/-- **WS-SM SM5.I**: on a valid core, a tick error is a no-op — the whole step
(the boot-core clock advance included) commits nothing (the Rust ISR has
already serviced the tick; the error short-circuits before any state write). -/
theorem perCoreTimerTickStep_error (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (e : KernelError)
    (herr : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩
      = .error e) :
    perCoreTimerTickStep st coreId = (st, []) := by
  unfold perCoreTimerTickStep; rw [dif_pos h, herr]

/-- **WS-SM SM5.I**: on a valid core, a domain-transition error is equally a
no-op — all-or-nothing: the tick's commit is withheld rather than shipping a
state whose domain accounting failed (unreachable under the maintained
invariants; AK2-I out-of-bounds index). -/
theorem perCoreTimerTickStep_domain_error (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (result : SystemState × List (CoreId × SgiKind))
    (e : KernelError)
    (hok : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩
      = .ok result)
    (herr : scheduleDomainOnCore result.1 ⟨coreId.toNat, h⟩ = .error e) :
    perCoreTimerTickStep st coreId = (st, []) := by
  unfold perCoreTimerTickStep; rw [dif_pos h, hok]; simp only [herr]

/-- **WS-SM SM5.I**: the step never *fabricates* SGIs — every emitted SGI comes
from the verified `timerTickOnCore` (the domain arm emits none, and the failure /
out-of-range paths emit none).  So a configuration in which `timerTickOnCore`
emits no cross-core wake (every refilled SchedContext homed on `c`) drives no
cross-core IPI. -/
theorem perCoreTimerTickStep_sgis_eq_tick (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) (result : SystemState × List (CoreId × SgiKind))
    (st2 : SystemState)
    (hok : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩
      = .ok result)
    (hdom : scheduleDomainOnCore result.1 ⟨coreId.toNat, h⟩ = .ok st2) :
    (perCoreTimerTickStep st coreId).2 = result.2 := by
  rw [perCoreTimerTickStep_ok st coreId h result st2 hok hdom]

/-- **WS-SM SM5.I** (soundness): the run-loop step preserves the object-store
invariant `invExt` — unconditionally, on every path.  The clock advance frames
the store (`tickClockedState_objects`); the success path composes
`timerTickOnCore_preserves_objects_invExt` with
`scheduleDomainOnCore_preserves_objects_invExt`; the failure / out-of-range
paths return `st` unchanged. -/
theorem perCoreTimerTickStep_preserves_objects_invExt (st : SystemState)
    (coreId : UInt64) (hInv : st.objects.invExt) :
    (perCoreTimerTickStep st coreId).1.objects.invExt := by
  by_cases h : coreId.toNat < numCores
  · have hInvC : (tickClockedState st ⟨coreId.toNat, h⟩).objects.invExt := by
      rw [tickClockedState_objects]; exact hInv
    cases hT : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ with
    | error e => rw [perCoreTimerTickStep_error st coreId h e hT]; exact hInv
    | ok result =>
        obtain ⟨st', sgis⟩ := result
        have hTickInv : st'.objects.invExt :=
          timerTickOnCore_preserves_objects_invExt _ _ st' sgis hInvC hT
        cases hD : scheduleDomainOnCore st' ⟨coreId.toNat, h⟩ with
        | error e =>
            rw [perCoreTimerTickStep_domain_error st coreId h (st', sgis) e hT hD]
            exact hInv
        | ok st2 =>
            rw [perCoreTimerTickStep_ok st coreId h (st', sgis) st2 hT hD]
            exact scheduleDomainOnCore_preserves_objects_invExt st' _ st2 hTickInv hD
  · rw [perCoreTimerTickStep_invalid_core st coreId h]; exact hInv

/-- **WS-SM SM5.I** (soundness): on a valid core, a successful step establishes
the SM4.C per-core current-thread validity on the ticked core — composing
SM5.D's `timerTickOnCore_preserves_currentThreadValidOnCore` with SM5.D.6's
`scheduleDomainOnCore_preserves_currentThreadValidOnCore` (whose boundary arm
*establishes* validity outright via the re-dispatch).  (The no-op paths are not
covered: they leave `st` whose pre-tick validity is the caller's to assume —
the substantive content is the success path, where the tick and the domain
transition *re-establish* validity even when they preempt or rotate.) -/
theorem perCoreTimerTickStep_ok_currentThreadValidOnCore (st : SystemState)
    (coreId : UInt64) (h : coreId.toNat < numCores) (hInv : st.objects.invExt)
    (result : SystemState × List (CoreId × SgiKind)) (st2 : SystemState)
    (hok : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩
      = .ok result)
    (hdom : scheduleDomainOnCore result.1 ⟨coreId.toNat, h⟩ = .ok st2) :
    currentThreadValidOnCore (perCoreTimerTickStep st coreId).1 ⟨coreId.toNat, h⟩ := by
  obtain ⟨st', sgis⟩ := result
  rw [perCoreTimerTickStep_ok st coreId h (st', sgis) st2 hok hdom]
  have hInvC : (tickClockedState st ⟨coreId.toNat, h⟩).objects.invExt := by
    rw [tickClockedState_objects]; exact hInv
  have hTickValid : currentThreadValidOnCore st' ⟨coreId.toNat, h⟩ :=
    timerTickOnCore_preserves_currentThreadValidOnCore _ _ st' sgis hInvC hok
  have hTickInv : st'.objects.invExt :=
    timerTickOnCore_preserves_objects_invExt _ _ st' sgis hInvC hok
  exact scheduleDomainOnCore_preserves_currentThreadValidOnCore st' _ st2
    hTickInv hTickValid hdom

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
