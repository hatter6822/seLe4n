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
is specified fail-closed: an errored tick commits nothing, so the step keeps the
state it was given until the tick and the domain accounting have both returned.
Compiled that way, every write the tick makes copies what it writes, since the
kept state still holds it.  seL4's `timerTick` never fails, and here neither do
its scheduling points: the dispatch (`scheduleEffectiveOnCore_eq_state`) and the
domain accounting (`scheduleDomainOnCore_eq_state`) always succeed, and the
tick's only refusals are a current thread the store does not hold as a thread or
a bound context the store does not hold, both read off the state before the
first write (`timerTickAdmittedOnCore`).

When those checks pass and no replenishment is due, the step is its state form
(`timerTickStateOnCore`, `perCoreTimerTickStep_of_admitted`): no pre-state is
kept, the charge writes the thread's time slice or the context's budget in its
slot, and the clock flag is the core's identity (`c = bootCoreId`), read without
comparing two states.  The compiled step (`perCoreTimerTickStepWithClockAdvanceImpl`,
`perCoreTimerTickStepWithClockAdvance_eq_impl`) takes the state form when admitted
and the specification otherwise (WS-ZA ZA6.1).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind bootCoreId)

-- ============================================================================
-- §1  The dispatch never refuses
-- ============================================================================

/-- The selection scan names only a thread the store holds and the eligibility
test admits: a found candidate is one, and every improvement is one. -/
theorem chooseBestRunnableEffectiveCode_succ (st : SystemState) (eligible : TCB → Bool) :
    ∀ (l : List SeLe4n.ThreadId) (found : Bool) (bt : SeLe4n.ThreadId) (bp : SeLe4n.Priority)
      (bd : SeLe4n.Deadline) (k : Nat),
      (found = true → ∃ tcb, st.getTcb? bt = some tcb ∧ eligible tcb = true) →
      chooseBestRunnableEffectiveCode st eligible l found bt bp bd = k + 1 →
      ∃ tcb, st.getTcb? ⟨k⟩ = some tcb ∧ eligible tcb = true := by
  intro l
  induction l with
  | nil =>
    intro found bt bp bd k hF h
    unfold chooseBestRunnableEffectiveCode at h
    cases found
    · simp at h
    · simp only [if_true, Nat.add_right_cancel_iff] at h
      obtain ⟨tcb, hT, hE⟩ := hF rfl
      subst h
      exact ⟨tcb, hT, hE⟩
  | cons tid rest ih =>
    intro found bt bp bd k hF h
    unfold chooseBestRunnableEffectiveCode at h
    cases hT : st.getTcb? tid with
    | none => rw [hT] at h; exact ih found bt bp bd k hF h
    | some tcb =>
      rw [hT] at h
      simp only at h
      by_cases hE : (eligible tcb && hasSufficientBudget st tcb) = true
      · rw [if_pos hE] at h
        have hEl : eligible tcb = true := (Bool.and_eq_true _ _ ▸ hE).1
        split at h
        · exact ih true tid _ _ k (fun _ => ⟨tcb, hT, hEl⟩) h
        · exact ih found bt bp bd k hF h
      · rw [if_neg hE] at h
        exact ih found bt bp bd k hF h

/-- Core `c`'s selection names a thread the store holds, in `c`'s active domain. -/
theorem chooseThreadEffectiveOnCoreCode_succ {st : SystemState} {c : CoreId} {k : Nat}
    (h : chooseThreadEffectiveOnCoreCode st c = k + 1) :
    ∃ tcb, st.getTcb? ⟨k⟩ = some tcb ∧ tcb.domain = st.scheduler.activeDomainOnCore c := by
  unfold chooseThreadEffectiveOnCoreCode at h
  have hNone : (false = true → ∃ tcb, st.getTcb? default = some tcb ∧
      (fun tcb : TCB => tcb.domain == st.scheduler.activeDomainOnCore c) tcb = true) :=
    fun h => absurd h Bool.false_ne_true
  dsimp only at h
  split at h
  · obtain ⟨tcb, hT, hE⟩ := chooseBestRunnableEffectiveCode_succ st _ _ false _ _ _ k hNone h
    exact ⟨tcb, hT, beq_iff_eq.mp hE⟩
  · obtain ⟨tcb, hT, hE⟩ := chooseBestRunnableEffectiveCode_succ st _ _ false _ _ _ k hNone h
    exact ⟨tcb, hT, beq_iff_eq.mp hE⟩

/-- `scheduleEffectiveOnCore`'s state, which it always reaches
(`scheduleEffectiveOnCore_eq_state`): the selection names a thread the store
holds in the core's active domain (`chooseThreadEffectiveOnCoreCode_succ`), so
the dispatch's lookup and domain test always pass and the dispatch writes
without a refusal to keep the state for, as seL4's `schedule` never fails. -/
@[inline] def scheduleEffectiveOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match chooseThreadEffectiveOnCoreCode st c with
  | 0 => (idleFallbackOnCore (saveOutgoingContextOnCore st c) c).clearReschedulePendingOnCore c
  | k + 1 =>
      let tid : SeLe4n.ThreadId := ⟨k⟩
      let stSaved := saveOutgoingContextOnCore st c
      let stDequeued := stSaved.runRemoveOnCore c tid
      let stRestored := restoreIncomingContextOnCore stDequeued c tid
      { stRestored with scheduler := (stRestored.scheduler.setCurrentOnCore c (some tid))
        |>.clearReschedulePendingOnCore c }

theorem scheduleEffectiveOnCore_eq_state (st : SystemState) (c : CoreId) :
    scheduleEffectiveOnCore st c = .ok (scheduleEffectiveOnCoreState st c) := by
  rw [scheduleEffectiveOnCore_eq_impl]
  unfold scheduleEffectiveOnCoreImpl scheduleEffectiveOnCoreState
  cases hk : chooseThreadEffectiveOnCoreCode st c with
  | zero => rfl
  | succ k =>
    obtain ⟨tcb, hT, hD⟩ := chooseThreadEffectiveOnCoreCode_succ hk
    simp only [hT, hD, ↓reduceIte]

/-- The dispatch leaves the clock where it was. -/
theorem scheduleEffectiveOnCoreState_machine_timer (st : SystemState) (c : CoreId) :
    (scheduleEffectiveOnCoreState st c).machine.timer = st.machine.timer :=
  scheduleEffectiveOnCore_machine_timer st c _ (scheduleEffectiveOnCore_eq_state st c)

-- ============================================================================
-- §2  The domain accounting never refuses
-- ============================================================================

/-- `switchDomainOnCore`'s state, which it always reaches
(`switchDomainOnCore_eq_state`): the next index is taken modulo the schedule's
length, so the entry it names exists. -/
@[inline] def switchDomainOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.domainSchedule with
  | [] => st
  | _ =>
      let nextIdx := ((st.scheduler.domainScheduleIndexOnCore c) + 1) % st.scheduler.domainSchedule.length
      match st.scheduler.domainSchedule[nextIdx]? with
      | none => st
      | some entry =>
          let stQueued := requeueOutgoingOnCore st c
          let sched' := (((stQueued.scheduler.setCurrentOnCore
              c none).setActiveDomainOnCore c (DomainScheduleEntry.domain entry)).setDomainTimeRemainingOnCore
              c (DomainScheduleEntry.length entry)).setDomainScheduleIndexOnCore c nextIdx
          { stQueued with scheduler := sched' }

theorem switchDomainOnCore_eq_state (st : SystemState) (c : CoreId) :
    switchDomainOnCore st c = .ok (switchDomainOnCoreState st c) := by
  unfold switchDomainOnCore switchDomainOnCoreState
  cases hS : st.scheduler.domainSchedule with
  | nil => rfl
  | cons e rest =>
    simp only
    have hLt : ((st.scheduler.domainScheduleIndexOnCore c) + 1) % (e :: rest).length
        < (e :: rest).length := Nat.mod_lt _ (by simp)
    rw [List.getElem?_eq_getElem hLt]

/-- `scheduleDomainOnCore`'s state, which it always reaches
(`scheduleDomainOnCore_eq_state`). -/
@[inline] def scheduleDomainOnCoreState (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.domainSchedule with
  | [] => st
  | _ :: _ =>
      if (st.scheduler.domainTimeRemainingOnCore c) ≤ 1 then
        scheduleEffectiveOnCoreState (switchDomainOnCoreState st c) c
      else decrementDomainTimeOnCore st c

theorem scheduleDomainOnCore_eq_state (st : SystemState) (c : CoreId) :
    scheduleDomainOnCore st c = .ok (scheduleDomainOnCoreState st c) := by
  unfold scheduleDomainOnCore scheduleDomainOnCoreState
  cases st.scheduler.domainSchedule with
  | nil => rfl
  | cons e rest =>
    simp only
    split
    · rw [switchDomainOnCore_eq_state]; exact scheduleEffectiveOnCore_eq_state _ _
    · rfl

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
-- §3  The tick's checks, and its state form
-- ============================================================================

/-- No replenishment is due: the drain pops nothing and hands the queue back. -/
theorem ReplenishQueue.popDue_of_not_hasDue (q : ReplenishQueue) (now : Nat)
    (h : q.hasDue now = false) : q.popDue now = (q, []) := by
  obtain ⟨entries, size⟩ := q
  cases entries with
  | nil => simp [ReplenishQueue.popDue, ReplenishQueue.splitDue]
  | cons e tail =>
    obtain ⟨scId, at_⟩ := e
    simp only [ReplenishQueue.hasDue, decide_eq_false_iff_not] at h
    simp [ReplenishQueue.popDue, ReplenishQueue.splitDue, h]

/-- Writing core `c`'s replenish queue back unchanged is no write. -/
theorem SchedulerState.setReplenishQueueOnCore_self (s : SchedulerState) (c : CoreId) :
    s.setReplenishQueueOnCore c (s.replenishQueueOnCore c) = s := by
  unfold SchedulerState.setReplenishQueueOnCore SchedulerState.replenishQueueOnCore
  cases s
  congr 1
  ext i hi
  simp only [Vector.getElem_set]
  split
  · rename_i h; subst h; rfl
  · rfl

/-- With no replenishment due, the tick's preparation is the timeout-error clear
alone: the drain writes the queue back unchanged and reports no SGI and no
local wake. -/
theorem timerTickOnCorePrepared_of_noDue (st : SystemState) (c : CoreId)
    (h : (st.scheduler.replenishQueueOnCore c).hasDue st.machine.timer = false) :
    timerTickOnCorePrepared st c =
      ({ st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }, [], false) := by
  unfold timerTickOnCorePrepared processReplenishmentsDueOnCore
  have hq : (st.scheduler.setLastTimeoutErrorsOnCore c []).replenishQueueOnCore c =
      st.scheduler.replenishQueueOnCore c := rfl
  simp only [hq, ReplenishQueue.popDue_of_not_hasDue _ _ h, List.foldl_nil]
  rw [← hq, SchedulerState.setReplenishQueueOnCore_self]

/-- The tick's checks, read off the state before the first write: no
replenishment is due at `now`, and core `c`'s current thread, if any, is a
thread the store holds whose bound context, if any, the store holds.  When they
pass the tick is its state form (`timerTickOnCore_of_admitted`); a due
replenishment takes the general path. -/
@[inline] def timerTickAdmittedOnCore (st : SystemState) (c : CoreId) (now : Nat) : Bool :=
  !(st.scheduler.replenishQueueOnCore c).hasDue now &&
  match st.scheduler.currentOnCore c with
  | none => true
  | some tid =>
    match st.getTcb? tid with
    | none => false
    | some tcb =>
      match tcb.schedContextBinding with
      | .unbound => true
      | .bound scId => (st.getSchedContext? scId).isSome
      | .donated scId _ => (st.getSchedContext? scId).isSome

/-- The charge of `tid`, current on core `c`, as a state and the timeout SGIs:
`timerTickBudgetOnCore` followed by the dispatch when it preempts, with the
slice or budget written in its slot (`timerTickBudgetOnCore_eq_chargeState`). -/
@[inline] def timerTickChargeStateOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) : SystemState × List (CoreId × SgiKind) :=
  match tcb.schedContextBinding with
  | .unbound =>
    if tcb.timeSlice ≤ 1 then
      (scheduleEffectiveOnCoreState (sliceExpireOnCore st c tid tcb hTcb) c, [])
    else
      (st.modifyObject tid.toObjId
        (SystemState.mapTcbObject fun t => { t with timeSlice := t.timeSlice - 1 }), [])
  | .bound scId | .donated scId _ =>
    match st.getSchedContextWitnessed? scId with
    | some ⟨sc, hSc⟩ =>
      if sc.budgetRemaining.val ≤ 1 then
        let r := budgetExhaustOnCore st c tid scId sc hSc 1
        (scheduleEffectiveOnCoreState r.1 c, r.2)
      else
        (st.modifyObject scId.toObjId
          (SystemState.mapSchedContextObject fun s => consumeBudget s 1), [])
    | none => (st, [])

/-- The tick as a state and its SGIs, when no replenishment is due
(`timerTickOnCore_of_admitted`): the timeout-error clear, then the charge of the
current thread, if any. -/
@[inline] def timerTickStateOnCore (st : SystemState) (c : CoreId) :
    SystemState × List (CoreId × SgiKind) :=
  let st0 := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
  match st0.scheduler.currentOnCore c with
  | none => (st0, [])
  | some tid =>
    match st0.getTcbWitnessed? tid with
    | some ⟨tcb, hTcb⟩ => timerTickChargeStateOnCore st0 c tid tcb hTcb
    | none => (st0, [])

/-- The budget tick at a thread whose bound context, if any, the store holds,
followed by the dispatch when it preempts, is the charge's state form. -/
theorem timerTickBudgetOnCore_eq_chargeState (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hSc : match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId => (st.getSchedContext? scId).isSome
      | .donated scId _ => (st.getSchedContext? scId).isSome) :
    (match timerTickBudgetOnCore st c tid tcb hTcb with
     | .error e => .error e
     | .ok (st3, preempted, timeoutSgis) =>
         if preempted then
           match scheduleEffectiveOnCore st3 c with
           | .error e => .error e
           | .ok st4 => .ok (st4, ([] : List (CoreId × SgiKind)) ++ timeoutSgis)
         else if false = true then
           match handleRescheduleSgiOnCore st3 c with
           | .error e => .error e
           | .ok st4 => .ok (st4, [] ++ timeoutSgis)
         else .ok (st3, [] ++ timeoutSgis)) =
      (Except.ok (timerTickChargeStateOnCore st c tid tcb hTcb) :
        Except KernelError (SystemState × List (CoreId × SgiKind))) := by
  have hx := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold timerTickBudgetOnCore timerTickChargeStateOnCore
  cases hB : tcb.schedContextBinding with
  | unbound =>
    by_cases hS : tcb.timeSlice ≤ 1
    · simp only [hS, ↓reduceIte, scheduleEffectiveOnCore_eq_state, List.nil_append]
    · simp only [hS, ↓reduceIte, Bool.false_eq_true, List.nil_append,
        SystemState.modifyObject, SystemState.rewriteObject]
      rw [RobinHood.RHTable.modify_of_get? hx]
      rfl
  | bound scId =>
    rw [hB] at hSc
    simp only at hSc ⊢
    obtain ⟨sc, hS⟩ := Option.isSome_iff_exists.mp hSc
    have hy := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hS
    rw [SystemState.getSchedContextWitnessed?_eq_some hS]
    by_cases hBud : sc.budgetRemaining.val ≤ 1
    · simp only [hBud, ↓reduceIte, scheduleEffectiveOnCore_eq_state, List.nil_append]
    · simp only [hBud, ↓reduceIte, Bool.false_eq_true, List.nil_append,
        SystemState.modifyObject, SystemState.rewriteObject]
      rw [RobinHood.RHTable.modify_of_get? hy]
      rfl
  | donated scId o =>
    rw [hB] at hSc
    simp only at hSc ⊢
    obtain ⟨sc, hS⟩ := Option.isSome_iff_exists.mp hSc
    have hy := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hS
    rw [SystemState.getSchedContextWitnessed?_eq_some hS]
    by_cases hBud : sc.budgetRemaining.val ≤ 1
    · simp only [hBud, ↓reduceIte, scheduleEffectiveOnCore_eq_state, List.nil_append]
    · simp only [hBud, ↓reduceIte, Bool.false_eq_true, List.nil_append,
        SystemState.modifyObject, SystemState.rewriteObject]
      rw [RobinHood.RHTable.modify_of_get? hy]
      rfl

/-- When its checks pass, the tick is its state form. -/
theorem timerTickOnCore_of_admitted (st : SystemState) (c : CoreId)
    (h : timerTickAdmittedOnCore st c st.machine.timer = true) :
    timerTickOnCore st c = .ok (timerTickStateOnCore st c) := by
  unfold timerTickAdmittedOnCore at h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hDue, hChk⟩ := h
  rw [timerTickOnCore_eq_prepared, timerTickOnCorePrepared_of_noDue st c hDue]
  unfold timerTickStateOnCore
  have hCur : ({ st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } :
      SystemState).scheduler.currentOnCore c = st.scheduler.currentOnCore c := rfl
  simp only [hCur]
  cases hC : st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    rw [hC] at hChk
    simp only at hChk
    cases hT : st.getTcb? tid with
    | none => rw [hT] at hChk; exact absurd hChk Bool.false_ne_true
    | some tcb =>
      rw [hT] at hChk
      have hT0 : ({ st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } :
          SystemState).getTcb? tid = some tcb := hT
      simp only
      rw [timerTickChargeCurrentOnCore_eq hT0, SystemState.getTcbWitnessed?_eq_some hT0]
      simp only
      refine timerTickBudgetOnCore_eq_chargeState _ c tid tcb hT0 ?_
      simp only at hChk
      revert hChk
      cases tcb.schedContextBinding <;> simp <;> exact id

/-- The tick's state form leaves the clock where it was. -/
theorem timerTickStateOnCore_machine_timer (st : SystemState) (c : CoreId)
    (h : timerTickAdmittedOnCore st c st.machine.timer = true) :
    (timerTickStateOnCore st c).1.machine.timer = st.machine.timer :=
  timerTickOnCore_machine_timer_eq st c _ _ (timerTickOnCore_of_admitted st c h)

-- ============================================================================
-- §4  The step
-- ============================================================================

/-- The clock advance changes neither what the checks read nor, off the boot
core, the clock. -/
theorem timerTickAdmittedOnCore_tickClockedState (st : SystemState) (c : CoreId) (now : Nat) :
    timerTickAdmittedOnCore (tickClockedState st c) c now = timerTickAdmittedOnCore st c now := by
  unfold tickClockedState; split <;> rfl

theorem tickClockedState_machine_timer (st : SystemState) (c : CoreId) :
    (tickClockedState st c).machine.timer =
      if c = bootCoreId then st.machine.timer + 1 else st.machine.timer := by
  unfold tickClockedState; split
  · exact tick_timer_succ st.machine
  · rfl

/-- When the tick's checks pass on core `c`, the run-loop step is the tick's
state form on the clocked state followed by the domain accounting's. -/
theorem perCoreTimerTickStep_of_admitted (st : SystemState) (coreId : UInt64)
    (hc : coreId.toNat < numCores)
    (h : timerTickAdmittedOnCore st ⟨coreId.toNat, hc⟩
      (tickClockedState st ⟨coreId.toNat, hc⟩).machine.timer = true) :
    perCoreTimerTickStep st coreId =
      (scheduleDomainOnCoreState
        (timerTickStateOnCore (tickClockedState st ⟨coreId.toNat, hc⟩) ⟨coreId.toNat, hc⟩).1
        ⟨coreId.toNat, hc⟩,
       (timerTickStateOnCore (tickClockedState st ⟨coreId.toNat, hc⟩) ⟨coreId.toNat, hc⟩).2) := by
  rw [← timerTickAdmittedOnCore_tickClockedState] at h
  unfold perCoreTimerTickStep
  rw [dif_pos hc, timerTickOnCore_of_admitted _ _ h]
  simp only [scheduleDomainOnCore_eq_state]

/-- WS-ZA ZA6.1: the compiled `perCoreTimerTickStepWithClockAdvance`.  The
tick's checks are read off the state first (`timerTickAdmittedOnCore`, at the
time the clock advance will set); when they pass, the step is the tick's and
the domain accounting's state forms, the clock flag the core's identity, so no
pre-state is kept and each write is in place.  Otherwise it is the
specification's step.  Proven equal
(`perCoreTimerTickStepWithClockAdvance_eq_impl`). -/
@[inline] def perCoreTimerTickStepWithClockAdvanceImpl (st : SystemState) (coreId : UInt64) :
    (List (CoreId × SgiKind) × Bool) × SystemState :=
  if hc : coreId.toNat < numCores then
    let c : CoreId := ⟨coreId.toNat, hc⟩
    let now := if c = bootCoreId then st.machine.timer + 1 else st.machine.timer
    if timerTickAdmittedOnCore st c now then
      let r := timerTickStateOnCore (tickClockedState st c) c
      ((r.2, decide (c = bootCoreId)), scheduleDomainOnCoreState r.1 c)
    else
      let result := perCoreTimerTickStep st coreId
      ((result.2, result.1.machine.timer != st.machine.timer), result.1)
  else (([], false), st)

@[csimp] theorem perCoreTimerTickStepWithClockAdvance_eq_impl :
    @perCoreTimerTickStepWithClockAdvance = @perCoreTimerTickStepWithClockAdvanceImpl := by
  funext st coreId
  unfold perCoreTimerTickStepWithClockAdvance perCoreTimerTickStepWithClockAdvanceImpl
  by_cases hc : coreId.toNat < numCores
  · rw [dif_pos hc]
    simp only
    rw [← tickClockedState_machine_timer]
    split
    · rename_i hA
      rw [perCoreTimerTickStep_of_admitted st coreId hc hA]
      rw [← timerTickAdmittedOnCore_tickClockedState] at hA
      simp only [scheduleDomainOnCoreState_machine_timer,
        timerTickStateOnCore_machine_timer _ _ hA, tickClockedState_machine_timer]
      by_cases hb : (⟨coreId.toNat, hc⟩ : CoreId) = bootCoreId
      · simp [hb]
      · simp [hb]
    · rfl
  · rw [dif_neg hc, perCoreTimerTickStep_invalid_core st coreId hc]
    simp

end SeLe4n.Kernel
