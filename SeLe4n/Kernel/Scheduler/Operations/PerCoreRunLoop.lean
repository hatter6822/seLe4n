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
# WS-SM SM5.I — Per-core run-loop step (the verified driver core)

The pure, verified decision core the per-core timer-tick kernel entry
(`Kernel.perCoreTimerTickEntry`, the `@[export lean_per_core_timer_tick]` seam the
Rust CNTP ISR resolves) runs against live kernel state.  At SM5.D the entry was a
`pure ()` placeholder; SM5.I replaces it with a real driver that reads core
`coreId`'s scheduler slots from the kernel-state `IO.Ref`, runs the **verified**
`Kernel.timerTickOnCore` transition, commits its result, and fires the returned
cross-core `.reschedule` SGIs.  This module holds the pure step + its correctness
theorems so the `BaseIO` entry is a thin, side-effecting shell over a verified core
(the SM5.F dispatch pattern: pure decision core proven sound, `BaseIO` shell inert
on the no-SGI path).

## Fail-closed contract

`perCoreTimerTickStep` decodes the `UInt64` core id fail-closed: an out-of-range id
(`≥ numCores`) or a `timerTickOnCore` error (a non-TCB current thread, or a
bound-budget thread whose SchedContext is missing — R5.E) leaves the kernel state
**unchanged** and emits **no** SGIs.  This is safe: the Rust ISR has already
recorded the per-core tick and re-armed the per-core comparator before calling in,
so a core reaching a no-op outcome is still fully serviced for the tick.

## Runtime lock discipline

On hardware the per-core tick runs under the big kernel lock the trap handler
holds, so the read-`timerTickOnCore`-commit is atomic.  The finer-grained
`timerTickOnCoreLockSet` (SM5.D.3) cross-domain footprint over `SchedLockId`
(object-store ⊕ run-queue ⊕ replenish-queue write locks, ascending per plan §4.4 —
`timerTickOnCoreLockSet_pairwise_le`) certifies the 2PL acquisition order a future
per-object-locked migration consumes; the `SchedLockId`-level `withLockSet` bracket
itself is the SM3.C combinator's cross-domain extension (tracked).

## Build reachability

Staged via `SeLe4n/Platform/Staged.lean`; `Kernel.perCoreTimerTickEntry` consumes
it and is itself staged (the `@[export]` seam).
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

end SeLe4n.Kernel
