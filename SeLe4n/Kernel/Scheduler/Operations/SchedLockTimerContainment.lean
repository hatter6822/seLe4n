-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.39: STAGED.  The per-core timer tick's write-set containment — the
-- proof that the footprint `SeLe4n/Kernel/SchedLockBracket.lean` acquires for the
-- timer entry covers every write the tick performs.
--
-- Staged rather than production because its frame chain runs through
-- `PerCoreCbs` and `PerCoreTickCbsPreservation`, both staged.  That is the normal
-- place for this kind of surface: a proof links into no image, and CI builds this
-- module on every PR through `Platform.Staged`.

import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation
import SeLe4n.Kernel.SchedLockBracket

/-!
# WS-RR RR7.39 — the timer tick writes only inside its declared footprint

`timerTickOnCoreCompleteLockSet c` names the object-store table write lock,
**every** core's run-queue write lock, and core `c`'s replenish-queue write lock.
So `schedFootprintCoversWrites` has content in exactly one clause: no core's
replenish queue other than `c`'s may move.

That single obligation is the whole of what the footprint claims beyond what it
over-approximates, and it is the claim the footprint's own docstring makes when it
says the replenish segment "is core `c`'s alone, and that is exact".  RR7.39 turns
that sentence into a theorem, because a footprint's soundness is exactly the sort
of claim a comment must not be trusted with — the *previous* such sentence, about
the run-queue segment being the boot core's, had been false since PR #880 made the
tick's wakes target-aware.

The chain, one link per composed transition:

* `tickClockedState` writes `machine` only;
* `setLastTimeoutErrorsOnCore` writes a diagnostic slot;
* `processReplenishmentsDueOnCore` pops core `c`'s queue and its wakes touch only
  run queues (`…_replenishQueueOnCore_ne`);
* `timerTickBudgetOnCore` inserts through `replenishOnCore … c`
  (`…_replenishQueueOnCore_ne`);
* `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore` and `scheduleDomainOnCore`
  frame every replenish queue.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind AccessMode bootCoreId)

/-- **WS-RR RR7.39 (frame)**: `timerTickOnCore` writes no replenish queue but its
own core's.

Every arm is a composition of transitions that either frame every replenish queue
or write core `c`'s slot; the `hne` hypothesis discharges the latter. -/
theorem timerTickOnCore_replenishQueueOnCore_ne (st : SystemState) (c : CoreId)
    (res : SystemState × List (CoreId × SgiKind)) (c' : CoreId) (hne : c ≠ c')
    (hTick : timerTickOnCore st c = .ok res) :
    res.1.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  rw [timerTickOnCore_eq_prepared] at hTick
  -- the prepared state — the diagnostic clear composed with the drain — frames `c'`
  have hPrep : (timerTickOnCorePrepared st c).1.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
    simp only [timerTickOnCorePrepared]
    rw [processReplenishmentsDueOnCore_replenishQueueOnCore_ne _ c _ c' hne]
    simp [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore]
  split at hTick
  · -- idle core: either the local-wake reschedule, or the prepared state verbatim
    split at hTick
    · split at hTick
      · simp at hTick
      · rename_i st2 hSgi
        simp only [Except.ok.injEq] at hTick
        subst hTick
        rw [show ((st2, (timerTickOnCorePrepared st c).2.1) :
          SystemState × List (CoreId × SgiKind)).1 = st2 from rfl,
          handleRescheduleSgiOnCore_replenishQueueOnCore _ c st2 c' hSgi, hPrep]
    · simp only [Except.ok.injEq] at hTick
      subst hTick
      exact hPrep
  · -- a current thread: the budget charge, then at most one re-dispatch
    split at hTick
    · rename_i tcb _
      split at hTick
      · simp at hTick
      · rename_i st3 preempted timeoutSgis hBudget
        have hSt3 : st3.scheduler.replenishQueueOnCore c'
            = st.scheduler.replenishQueueOnCore c' := by
          rw [timerTickBudgetOnCore_replenishQueueOnCore_ne _ c _ tcb st3 preempted c' hne
            hBudget, hPrep]
        split at hTick
        · split at hTick
          · simp at hTick
          · rename_i st4 hSched
            simp only [Except.ok.injEq] at hTick
            subst hTick
            rw [show ((st4, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis) :
              SystemState × List (CoreId × SgiKind)).1 = st4 from rfl,
              scheduleEffectiveOnCore_replenishQueueOnCore st3 c st4 c' hSched, hSt3]
        · split at hTick
          · split at hTick
            · simp at hTick
            · rename_i st4 hSgi
              simp only [Except.ok.injEq] at hTick
              subst hTick
              rw [show ((st4, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis) :
                SystemState × List (CoreId × SgiKind)).1 = st4 from rfl,
                handleRescheduleSgiOnCore_replenishQueueOnCore st3 c st4 c' hSgi, hSt3]
          · simp only [Except.ok.injEq] at hTick
            subst hTick
            exact hSt3
    · simp at hTick

/-- **WS-RR RR7.39 (frame)**: the run-loop step writes no replenish queue but its
own core's — the tick's frame carried through the fail-closed core decode and the
domain transition. -/
theorem perCoreTimerTickStep_replenishQueueOnCore_ne (st : SystemState) (coreId : UInt64)
    (c' : CoreId) (h : coreId.toNat < numCores)
    (hne : (⟨coreId.toNat, h⟩ : CoreId) ≠ c') :
    (perCoreTimerTickStep st coreId).1.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold perCoreTimerTickStep
  rw [dif_pos h]
  cases hTick : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ with
  | error e => rfl
  | ok res =>
    simp only
    cases hDom : scheduleDomainOnCore res.1 ⟨coreId.toNat, h⟩ with
    | error e => rfl
    | ok st2 =>
      simp only
      rw [scheduleDomainOnCore_replenishQueueOnCore res.1 _ st2 c' hDom,
        timerTickOnCore_replenishQueueOnCore_ne _ _ res c' hne hTick,
        tickClockedState_scheduler]

/-- **WS-RR RR7.39 (the payoff for the timer seam)**: the verified tick step's
writes are inside the footprint the entry declares.

Two of the three clauses are vacuous by the footprint's own width — it names the
object-store table lock and every core's run-queue lock — and the third is
`perCoreTimerTickStep_replenishQueueOnCore_ne`.  So the footprint the bracket
acquires is not a *false* footprint. -/
theorem perCoreTimerTickStep_coversWrites (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) :
    schedFootprintCoversWrites
      ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
        timerTickOnCoreCompleteLockSet_keys_nodup _⟩
      st (perCoreTimerTickStep st coreId).1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hNot
    exact absurd List.mem_cons_self hNot
  · intro d hNot
    exact absurd
      (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_allCoreRunQueueLockSegment d))) hNot
  · intro d hNot
    have hne : (⟨coreId.toNat, h⟩ : CoreId) ≠ d := by
      rintro rfl
      exact hNot (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    exact perCoreTimerTickStep_replenishQueueOnCore_ne st coreId d h hne

/-- **WS-RR RR7.39**: the clock-advance-flagged step commits the plain step's
state, so its containment is the plain step's. -/
theorem perCoreTimerTickStepWithClockAdvance_coversWrites (st : SystemState)
    (coreId : UInt64) (h : coreId.toNat < numCores) :
    schedFootprintCoversWrites
      ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
        timerTickOnCoreCompleteLockSet_keys_nodup _⟩
      st (perCoreTimerTickStepWithClockAdvance st coreId).2 :=
  perCoreTimerTickStep_coversWrites st coreId h

end SeLe4n.Kernel
