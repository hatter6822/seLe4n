-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation

/-!
# The timer tick's state forms

The per-core timer tick (`perCoreTimerTickStep`, `perCoreTimerTickStepWithClockAdvance`)
is total, as seL4's `timerTick` is (WS-ZA ZA6.2): its scheduling points — the
dispatch (`scheduleEffectiveOnCore_eq_state`), the local reschedule
(`handleRescheduleSgiOnCore_eq_state`) and the domain accounting
(`scheduleDomainOnCore_eq_state`) — never refuse, and a current thread or a
bound context the store does not hold is charged nothing.  So the compiled step
(`perCoreTimerTickStepWithClockAdvanceImpl`,
`perCoreTimerTickStepWithClockAdvance_eq_impl`) keeps no pre-state: it reads the
reschedule flags before the tick, writes the state in place, and reads the clock
flag off the core's identity (`c = bootCoreId`).  The tick's own compiled
forms — the charge (`timerTickBudgetOnCore_eq_impl`), the exhausting charge
(`budgetExhaustOnCore_eq_impl`) and the drain
(`processReplenishmentsDueOnCore_eq_impl`, `processOneReplenishmentOnCore_eq_impl`)
— are registered in `Core.lean` ahead of `timerTickOnCore`, since a `@[csimp]`
reaches only code compiled after it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind bootCoreId)

/-- The dispatch leaves the clock where it was. -/
theorem scheduleEffectiveOnCoreState_machine_timer (st : SystemState) (c : CoreId) :
    (scheduleEffectiveOnCoreState st c).machine.timer = st.machine.timer :=
  scheduleEffectiveOnCore_machine_timer st c _ (scheduleEffectiveOnCore_eq_state st c)

-- ============================================================================
-- §2  The domain accounting never refuses
-- ============================================================================

/-- The domain accounting leaves the clock where it was. -/
theorem scheduleDomainOnCoreState_machine_timer (st : SystemState) (c : CoreId) :
    (scheduleDomainOnCoreState st c).machine.timer = st.machine.timer := by
  unfold scheduleDomainOnCoreState
  split
  · rfl
  · split
    · rw [scheduleEffectiveOnCoreState_machine_timer,
        switchDomainOnCore_machine st c _ (switchDomainOnCore_eq_state st c)]
    · rfl

-- ============================================================================
-- §3  The step
-- ============================================================================

theorem tickClockedState_machine_timer (st : SystemState) (c : CoreId) :
    (tickClockedState st c).machine.timer =
      if c = bootCoreId then st.machine.timer + 1 else st.machine.timer := by
  unfold tickClockedState; split
  · exact tick_timer_succ st.machine
  · rfl

/-- The step's commit moves the clock exactly as the clock advance does. -/
theorem perCoreTimerTickPost_machine_timer (st : SystemState) (c : CoreId) :
    (perCoreTimerTickPost st c).machine.timer =
      if c = bootCoreId then st.machine.timer + 1 else st.machine.timer := by
  unfold perCoreTimerTickPost
  rw [scheduleDomainOnCoreState_machine_timer, timerTickOnCore_machine_timer_eq,
    tickClockedState_machine_timer]

/-- WS-ZA ZA6.1/ZA6.2: the compiled `perCoreTimerTickStepWithClockAdvance`.  The
tick never refuses, so no pre-state is kept for a refusal: the step snapshots the
flags (`reschedulePendingSnapshot`, a call the compiler does not sink), runs the
tick and the domain accounting over the state in place, and reads the clock flag
off the core's identity (`c = bootCoreId`) instead of comparing two states.
Proven equal (`perCoreTimerTickStepWithClockAdvance_eq_impl`). -/
@[inline] def perCoreTimerTickStepWithClockAdvanceImpl (st : SystemState) (coreId : UInt64) :
    (PerCoreFlags × Bool) × SystemState :=
  if hc : coreId.toNat < numCores then
    let c : CoreId := ⟨coreId.toNat, hc⟩
    let pending0 := reschedulePendingSnapshot st
    let st' := scheduleDomainOnCoreState (timerTickOnCore (tickClockedState st c) c) c
    ((pending0.raised st'.scheduler.reschedulePending, decide (c = bootCoreId)), st')
  else ((PerCoreFlags.none, false), st)

@[csimp] theorem perCoreTimerTickStepWithClockAdvance_eq_impl :
    @perCoreTimerTickStepWithClockAdvance = @perCoreTimerTickStepWithClockAdvanceImpl := by
  funext st coreId
  unfold perCoreTimerTickStepWithClockAdvance perCoreTimerTickStepWithClockAdvanceImpl
  by_cases hc : coreId.toNat < numCores
  · rw [dif_pos hc, perCoreTimerTickStep_valid_core st coreId hc]
    simp only [perCoreTimerTickPost_machine_timer, reschedulePendingSnapshot]
    by_cases hb : (⟨coreId.toNat, hc⟩ : CoreId) = bootCoreId
    · simp [hb]
    · simp [hb]
  · rw [dif_neg hc, perCoreTimerTickStep_invalid_core st coreId hc]
    simp

end SeLe4n.Kernel
