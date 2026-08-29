-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop

/-!
# WS-SM SM5.I — the live per-core timer tick preserves the per-core CBS invariant

`Kernel.timerTickOnCore` (the per-core timer tick driven by `perCoreTimerTickEntry`)
preserves `perCoreCbsInvariant` — the conjunction of replenish-queue **validity**
(sorted + size-consistent), replenishment **pipeline-order** (every pending
replenishment is eligible strictly in the future), and replenish-queue
**affinity-consistency** (every queued SchedContext's bound thread is homed on the
core).  This is the "preservation by every transition" obligation SM5.I owes for
the live CBS engine: the SM5.H §13 A5 result already proves the affinity-change
composite preserves the invariant; this module closes the *tick* side.

The three conjuncts decompose by difficulty:
* **Validity** — machine-free.  `timerTickOnCorePrepared` (clear + the SM5.D.4
  `processReplenishmentsDueOnCore`) only *pops* core `c`'s queue (`popDue` preserves
  sorted + size-consistent; the wake fold never touches a replenish queue), the
  SM5.H §14 budget-tick A4 preserves it, and `scheduleEffectiveOnCore` frames it.
* **Pipeline-order** — `popDue now` *establishes* it on core `c` (every remaining
  entry is `> now`), the budget tick's insert is `now + period > now` (`period > 0`
  from SchedContext well-formedness), and `machine.timer` is unchanged through the
  tick (the timeout-path machine-frame chain).
* **Affinity-consistency** — `popDue` removes entries (monotone), and the budget
  insert is for the running thread's bound SchedContext, which is homed on `c` under
  the affinity-placement precondition (current thread on `c` ⇒ homed on `c`) and
  `schedContextBindingConsistent`.

## Build reachability

Staged via `SeLe4n/Platform/Staged.lean`.  The SM5.I per-core run loop is the
runtime exerciser; the theorems here are the formal preservation guarantee.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind bootCoreId)

-- ============================================================================
-- §1  Replenish-queue frames for the SM5.D.4 replenishment machinery
-- ============================================================================

/-- WS-SM SM5.I: `enqueueRunnableOnCore` leaves every core's replenish-queue slot
unchanged — it writes only objects (`ipcState := .ready`) and a run queue. -/
theorem enqueueRunnableOnCore_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold enqueueRunnableOnCore; split
  · split
    · rfl
    · simp only [SchedulerState.setRunQueueOnCore_replenishQueueOnCore]
  · rfl

/-- WS-SM SM5.I: `processOneReplenishmentOnCore` leaves every core's replenish-queue
slot unchanged — it refills a SchedContext (whole scheduler framed) and optionally
wakes a thread (a run-queue write), never touching a replenish queue. -/
theorem processOneReplenishmentOnCore_replenishQueueOnCore_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) :
    (processOneReplenishmentOnCore st ec scId now).1.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp only [processOneReplenishmentOnCore]
  split
  · split
    · rw [refillSchedContext_scheduler_eq]
    · rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_replenishQueueOnCore,
        refillSchedContext_scheduler_eq]
  · rw [refillSchedContext_scheduler_eq]

/-- WS-SM SM5.I: the wake fold inside `processReplenishmentsDueOnCore` preserves every
core's replenish-queue slot (each step is a `processOneReplenishmentOnCore`). -/
theorem foldl_processOneReplenishment_replenishQueueOnCore (c : CoreId) (now : Nat) (c' : CoreId)
    (dueIds : List SeLe4n.SchedContextId)
    (acc : SystemState × List (CoreId × SgiKind) × Bool) :
    (dueIds.foldl (fun acc scId =>
        let r := processOneReplenishmentOnCore acc.1 c scId now
        (r.1, acc.2.1 ++ r.2.1.toList, acc.2.2 || r.2.2)) acc).1.scheduler.replenishQueueOnCore c'
      = acc.1.scheduler.replenishQueueOnCore c' := by
  induction dueIds generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
      rw [List.foldl_cons, ih]
      exact processOneReplenishmentOnCore_replenishQueueOnCore_eq acc.1 c hd now c'

/-- WS-SM SM5.I: core `c`'s replenish queue after `processReplenishmentsDueOnCore` is
exactly the `popDue` remainder (the wake fold never re-inserts). -/
theorem processReplenishmentsDueOnCore_replenishQueueOnCore_self (st : SystemState)
    (c : CoreId) (now : Nat) :
    (processReplenishmentsDueOnCore st c now).1.scheduler.replenishQueueOnCore c
      = ((st.scheduler.replenishQueueOnCore c).popDue now).1 := by
  simp only [processReplenishmentsDueOnCore]
  rw [foldl_processOneReplenishment_replenishQueueOnCore]
  simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]

/-- WS-SM SM5.I: every *other* core's replenish queue is unchanged by
`processReplenishmentsDueOnCore` (`popDue` writes only core `c`'s slot). -/
theorem processReplenishmentsDueOnCore_replenishQueueOnCore_ne (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) (h : c ≠ c') :
    (processReplenishmentsDueOnCore st c now).1.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp only [processReplenishmentsDueOnCore]
  rw [foldl_processOneReplenishment_replenishQueueOnCore]
  simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ h]

/-- WS-SM SM5.I: `dispatchIdleOnCore` leaves every core's replenish-queue slot
unchanged (it writes only a run queue, the restored context, and the current slot). -/
theorem dispatchIdleOnCore_replenishQueueOnCore (st : SystemState) (c c' : CoreId) :
    (dispatchIdleOnCore st c).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp only [dispatchIdleOnCore, SchedulerState.setCurrentOnCore_replenishQueueOnCore,
    restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_replenishQueueOnCore]

/-- WS-SM SM5.I: `idleFallbackOnCore` leaves every core's replenish-queue slot
unchanged (both arms — idle dispatch and `current = none`). -/
theorem idleFallbackOnCore_replenishQueueOnCore (st : SystemState) (c c' : CoreId) :
    (idleFallbackOnCore st c).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold idleFallbackOnCore; split
  · exact dispatchIdleOnCore_replenishQueueOnCore st c c'
  · simp only [SchedulerState.setCurrentOnCore_replenishQueueOnCore]

/-- WS-SM SM5.I: a successful per-core reschedule (`scheduleEffectiveOnCore`) leaves
every core's replenish-queue slot unchanged — it writes only run queues, the current
slot, and the object store (mirrors `scheduleEffectiveOnCore_activeDomainOnCore`). -/
theorem scheduleEffectiveOnCore_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (c' : CoreId) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      rw [idleFallbackOnCore_replenishQueueOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.setCurrentOnCore_replenishQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_replenishQueueOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.I (validity, item 4): `processReplenishmentsDueOnCore` preserves
replenish-queue **validity** on every core — core `c`'s queue is the `popDue`
remainder (sorted + size-consistent are preserved by removal); every other core's is
unchanged. -/
theorem processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) (hValid : replenishQueueValidOnCore st c') :
    replenishQueueValidOnCore (processReplenishmentsDueOnCore st c now).1 c' := by
  unfold replenishQueueValidOnCore at hValid ⊢
  by_cases h : c = c'
  · subst h
    rw [processReplenishmentsDueOnCore_replenishQueueOnCore_self]
    exact ⟨popDue_preserves_sorted hValid.1, popDue_sizeConsistent hValid.2⟩
  · rw [processReplenishmentsDueOnCore_replenishQueueOnCore_ne _ _ _ _ h]
    exact hValid

/-- WS-SM SM5.I: the prepared (clear + `processReplenishmentsDueOnCore`) phase
preserves replenish-queue validity on every core. -/
theorem timerTickOnCorePrepared_preserves_replenishQueueValidOnCore (st : SystemState)
    (c c' : CoreId) (hValid : replenishQueueValidOnCore st c') :
    replenishQueueValidOnCore (timerTickOnCorePrepared st c).1 c' := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore
  unfold replenishQueueValidOnCore at hValid ⊢
  simpa only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] using hValid

/-- WS-SM SM5.I (item 4, headline): the **live per-core timer tick** preserves
replenish-queue validity on every core.  The prepared phase preserves it, the SM5.H
§14 budget-tick A4 preserves it, and a preempting `scheduleEffectiveOnCore` frames
it. -/
theorem timerTickOnCore_preserves_replenishQueueValidOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind)) (c' : CoreId)
    (hValid : ∀ c'', replenishQueueValidOnCore st c'')
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    replenishQueueValidOnCore st' c' := by
  have hPrep : ∀ c'', replenishQueueValidOnCore (timerTickOnCorePrepared st c).1 c'' :=
    fun c'' => timerTickOnCorePrepared_preserves_replenishQueueValidOnCore st c c'' (hValid c'')
  rw [timerTickOnCore_eq_prepared] at hStep
  split at hStep
  · -- idle arm: the prepared state, or the round-7 local-wake reschedule
    -- (whose handler never touches a replenish queue)
    split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st2 hH
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        have h2 := hPrep c'
        unfold replenishQueueValidOnCore at h2 ⊢
        rw [handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c' hH]
        exact h2
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst; exact hPrep c'
  · split at hStep
    · split at hStep
      · simp at hStep
      · -- budget tick `.ok (st3, b)`
        rename_i st3 b tsgis hbud
        have h3 : replenishQueueValidOnCore st3 c' :=
          timerTickBudgetOnCore_preserves_replenishQueueValidOnCore _ c _ _ _ _ c' hPrep hbud
        split at hStep
        · -- preempted: scheduleEffectiveOnCore
          split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            unfold replenishQueueValidOnCore at h3 ⊢
            rw [scheduleEffectiveOnCore_replenishQueueOnCore _ c _ c' hsched]
            exact h3
        · -- not preempted: the round-7 local-wake reschedule, or identity
          split at hStep
          · split at hStep
            · simp at hStep
            · rename_i st4 hH
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨hst, _⟩ := hStep; subst hst
              unfold replenishQueueValidOnCore at h3 ⊢
              rw [handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c' hH]
              exact h3
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst; exact h3
    · simp at hStep

-- ============================================================================
-- §2  Machine-timer frames (the per-core tick reads but never advances the
--     global timer — the substrate for pipeline-order preservation)
-- ============================================================================

/-- WS-SM SM5.I: `ensureRunnable` leaves the machine unchanged (it writes only a
run queue). -/
theorem ensureRunnable_machine (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).machine = st.machine := by
  unfold ensureRunnable; split
  · rfl
  · split <;> rfl

/-- WS-SM SM5.I: `saveOutgoingContextOnCore` leaves the machine unchanged (it saves
the register context *into* the outgoing TCB; it reads `machine.regs` but writes
only the object store). -/
theorem saveOutgoingContextOnCore_machine (st : SystemState) (c : CoreId) :
    (saveOutgoingContextOnCore st c).machine = st.machine := by
  unfold saveOutgoingContextOnCore; split
  · rfl
  · split <;> rfl

/-- WS-SM SM5.I: `restoreIncomingContext` leaves the machine **timer** unchanged — it
writes only `machine.regs` (the register file), never the global timer. -/
theorem restoreIncomingContext_machine_timer (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).machine.timer = st.machine.timer := by
  unfold restoreIncomingContext; split <;> rfl

/-- WS-SM SM5.I: `endpointQueueRemove` leaves the machine unchanged (it writes only
the object store — queue links + `ipcState`).  Mirrors
`endpointQueueRemove_scheduler_eq`. -/
theorem endpointQueueRemove_machine
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    st'.machine = st.machine := by
  unfold endpointQueueRemove at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hTcb : lookupTcb st tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        simp only [Except.ok.injEq] at hStep
        rw [← hStep]

/-- WS-SM SM5.I: `timeoutThread` leaves the machine unchanged — every step
(`endpointQueueRemove`, `storeObject`, `ensureRunnable`, optional
`revertPriorityInheritance`) writes only the object store / run queues.  Mirrors
`timeoutThread_replenishQueueOnCore`. -/
theorem timeoutThread_machine (epId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (execCore : CoreId) (st : SystemState)
    (r : SystemState × Option (CoreId × SgiKind))
    (h : timeoutThread epId isReceiveQ tid execCore st = .ok r) :
    r.1.machine = st.machine := by
  unfold timeoutThread at h
  split at h
  · simp at h
  · rename_i st1 hER
    have hMach1 : st1.machine = st.machine :=
      endpointQueueRemove_machine epId isReceiveQ tid st st1 hER
    split at h
    · simp at h
    · rename_i tcb hLk
      simp only [storeObject] at h
      split at h <;>
        · simp only [Except.ok.injEq] at h
          subst h
          first
            | rw [PriorityInheritance.revert_preserves_machine]
            | skip
          rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_machine_eq]
          show st1.machine = st.machine
          rw [hMach1]

/-- WS-SM SM5.I: timing out **all** of a SchedContext's IPC-blocked threads leaves the
machine unchanged (each step is a `timeoutThread`).  Mirrors
`timeoutBlockedThreads_replenishQueueOnCore`. -/
theorem timeoutBlockedThreads_machine (st : SystemState) (scId : SeLe4n.SchedContextId)
    (execCore : CoreId) :
    (timeoutBlockedThreads st scId execCore).1.machine = st.machine := by
  unfold timeoutBlockedThreads
  suffices hFold : ∀ (tids : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × SgiKind)),
      (tids.foldl (fun (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × SgiKind)) tid =>
        match acc.1.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match timeoutThread epId isReceiveQ tid execCore acc.1 with
            | .ok r => (r.1, acc.2.1, acc.2.2 ++ r.2.toList)
            | .error e => (acc.1, acc.2.1 ++ [(tid, e)], acc.2.2)
          | none => (acc.1, acc.2.1, acc.2.2)
        | none => (acc.1, acc.2.1, acc.2.2)) acc).1.machine = acc.1.machine by
    exact hFold _ (st, [], [])
  intro tids
  induction tids with
  | nil => intro acc; rfl
  | cons hd tail ih =>
    intro acc
    rw [List.foldl_cons, ih]
    split
    · split
      · split
        · next r heqTo => exact timeoutThread_machine _ _ hd execCore acc.1 r heqTo
        · rfl
      · rfl
    · rfl

/-- WS-SM SM5.I: the per-core budget tick leaves the machine unchanged — every
branch writes only the object store / scheduler slots (the bound-exhausted branch's
`timeoutBlockedThreads` is machine-framed). -/
theorem timerTickBudgetOnCore_machine (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (st' : SystemState) (b : Bool)
    {sgis : List (CoreId × SgiKind)}
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) :
    st'.machine = st.machine := by
  unfold timerTickBudgetOnCore at hStep
  split at hStep
  · -- unbound: both time-slice arms are object/scheduler writes
    split at hStep <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst; rfl
  all_goals
    -- bound and donated: identical structure (getSchedContext? then the budget `if`)
    split at hStep
    · split at hStep
      · -- budget exhausted (the `timeoutBlockedThreads` machine-frame closes it)
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        simp [timeoutBlockedThreads_machine, replenishOnCore]
      · -- budget > 1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst; rfl
    · simp at hStep

/-- WS-SM SM5.I: `dispatchIdleOnCore` leaves the machine **timer** unchanged (it
restores the idle thread's register context — `machine.regs` — but never the
global timer). -/
theorem dispatchIdleOnCore_machine_timer (st : SystemState) (c : CoreId) :
    (dispatchIdleOnCore st c).machine.timer = st.machine.timer := by
  simp [dispatchIdleOnCore, restoreIncomingContextOnCore_machine_timer]

/-- WS-SM SM5.I: `idleFallbackOnCore` leaves the machine timer unchanged. -/
theorem idleFallbackOnCore_machine_timer (st : SystemState) (c : CoreId) :
    (idleFallbackOnCore st c).machine.timer = st.machine.timer := by
  unfold idleFallbackOnCore; split
  · exact dispatchIdleOnCore_machine_timer st c
  · rfl

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` leaves the machine **timer**
unchanged — it saves/restores register context (`machine.regs`) but never advances
the global timer. -/
theorem scheduleEffectiveOnCore_machine_timer (st : SystemState) (c : CoreId)
    (st' : SystemState) (hStep : scheduleEffectiveOnCore st c = .ok st') :
    st'.machine.timer = st.machine.timer := by
  unfold scheduleEffectiveOnCore at hStep
  cases hCh : chooseThreadEffectiveOnCore st c with
  | error e => rw [hCh] at hStep; simp at hStep
  | ok res =>
    rw [hCh] at hStep
    cases res with
    | none =>
      simp only [Except.ok.injEq] at hStep; subst hStep
      simp [idleFallbackOnCore_machine_timer, saveOutgoingContextOnCore_machine]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          subst hStep
          simp [restoreIncomingContextOnCore_machine_timer, saveOutgoingContextOnCore_machine]
        · simp at hStep

/-- WS-SM SM5.I (machine substrate): the **live per-core timer tick** leaves the
machine **timer** unchanged — it reads `now := machine.timer` but never advances the
global timer (prepared + budget tick fully preserve the machine; a preempting
`scheduleEffectiveOnCore` changes only `machine.regs`). -/
theorem timerTickOnCore_machine_timer_eq (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    st'.machine.timer = st.machine.timer := by
  have hPrepM : (timerTickOnCorePrepared st c).1.machine = st.machine :=
    timerTickOnCorePrepared_machine_eq st c
  rw [timerTickOnCore_eq_prepared] at hStep
  split at hStep
  · -- idle arm: prepared, or the round-7 local-wake reschedule (timer-framed)
    split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st2 hH
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        rw [handleRescheduleSgiOnCore_machine_timer _ c _ hH, hPrepM]
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst; rw [hPrepM]
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st3 b tsgis hbud
        have h3 : st3.machine = (timerTickOnCorePrepared st c).1.machine :=
          timerTickBudgetOnCore_machine _ c _ _ _ _ hbud
        split at hStep
        · split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            rw [scheduleEffectiveOnCore_machine_timer _ c _ hsched, h3, hPrepM]
        · split at hStep
          · split at hStep
            · simp at hStep
            · rename_i st4 hH
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨hst, _⟩ := hStep; subst hst
              rw [handleRescheduleSgiOnCore_machine_timer _ c _ hH, h3, hPrepM]
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            rw [h3, hPrepM]
    · simp at hStep

-- ============================================================================
-- §3  Pipeline-order preservation (every pending replenishment stays in the
--     future).  `popDue` only *removes* entries, so a pre-tick future-ordered
--     queue stays future-ordered; the budget insert is `now + period > now`.
-- ============================================================================

/-- WS-SM SM5.I: `splitDue`'s remaining list is a subset of the input (it only
*drops* due entries).  The substrate for pipeline-order preservation. -/
theorem splitDue_snd_subset (entries : List (SeLe4n.SchedContextId × Nat)) (now : Nat)
    (e : SeLe4n.SchedContextId × Nat) :
    e ∈ (ReplenishQueue.splitDue entries now).2 → e ∈ entries := by
  induction entries with
  | nil => intro h; simp [ReplenishQueue.splitDue] at h
  | cons hd tl ih =>
    intro h
    obtain ⟨id, t⟩ := hd
    unfold ReplenishQueue.splitDue at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · exact h

/-- WS-SM SM5.I: `popDue`'s remaining queue is a subset of the input. -/
theorem popDue_remaining_subset (rq : ReplenishQueue) (now : Nat)
    (e : SeLe4n.SchedContextId × Nat) :
    e ∈ (rq.popDue now).1.entries → e ∈ rq.entries := by
  intro h
  exact splitDue_snd_subset rq.entries now e h

/-- WS-SM SM5.I: `processReplenishmentsDueOnCore` preserves pipeline-order on every
core — it only `popDue`-removes entries from core `c` (every other core unchanged)
and never advances the timer. -/
theorem processReplenishmentsDueOnCore_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c : CoreId) (now : Nat) (c' : CoreId)
    (hPipe : replenishmentPipelineOrderOnCore st c') :
    replenishmentPipelineOrderOnCore (processReplenishmentsDueOnCore st c now).1 c' := by
  intro pair hMem
  rw [processReplenishmentsDueOnCore_machine_eq]
  by_cases h : c = c'
  · subst h
    rw [processReplenishmentsDueOnCore_replenishQueueOnCore_self] at hMem
    exact hPipe pair (popDue_remaining_subset _ now pair hMem)
  · rw [processReplenishmentsDueOnCore_replenishQueueOnCore_ne _ _ _ _ h] at hMem
    exact hPipe pair hMem

/-- WS-SM SM5.I: a successful `scheduleEffectiveOnCore` preserves pipeline-order (it
frames every replenish queue and the timer). -/
theorem scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState) (c' : CoreId)
    (hPipe : replenishmentPipelineOrderOnCore st c')
    (hStep : scheduleEffectiveOnCore st c = .ok st') :
    replenishmentPipelineOrderOnCore st' c' := by
  intro pair hMem
  rw [scheduleEffectiveOnCore_replenishQueueOnCore st c st' c' hStep] at hMem
  rw [scheduleEffectiveOnCore_machine_timer st c st' hStep]
  exact hPipe pair hMem

/-- WS-SM SM5.I: the prepared (clear + replenishment) phase preserves pipeline-order. -/
theorem timerTickOnCorePrepared_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c c' : CoreId)
    (hPipe : replenishmentPipelineOrderOnCore st c') :
    replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c).1 c' := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_replenishmentPipelineOrderOnCore
  intro pair hMem
  simp only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] at hMem
  exact hPipe pair hMem

/-- WS-SM SM5.I (helper): pipeline-order transfers across a replenish-queue + timer
equality. -/
private theorem pipeline_frame_of_queue_timer_eq (st base : SystemState) (c' : CoreId)
    (hQ : base.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c')
    (hM : base.machine.timer = st.machine.timer)
    (hPipe : replenishmentPipelineOrderOnCore st c') :
    replenishmentPipelineOrderOnCore base c' := by
  intro pair hMem; rw [hQ] at hMem; rw [hM]; exact hPipe pair hMem

/-- WS-SM SM5.I: the per-core budget tick preserves pipeline-order — the unchanged
branches frame the queue, and the bound-exhausted branch's insert (`now + period`)
is future because the SchedContext's `period` is positive. -/
theorem timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st' : SystemState) (b : Bool) (c' : CoreId)
    {sgis : List (CoreId × SgiKind)}
    (hPipe : replenishmentPipelineOrderOnCore st c')
    (hPeriod : ∀ scId sc, st.getSchedContext? scId = some sc → 0 < sc.period.val)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b, sgis)) :
    replenishmentPipelineOrderOnCore st' c' := by
  have hM : st'.machine.timer = st.machine.timer := by
    rw [timerTickBudgetOnCore_machine st c tid tcb st' b hStep]
  match hB : tcb.schedContextBinding with
  | .unbound =>
      simp only [timerTickBudgetOnCore, hB] at hStep
      split at hStep <;>
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hst, _⟩ := hStep; subst hst
          exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe
  | .bound scId =>
      match hSc : st.getSchedContext? scId with
      | some sc =>
          by_cases hBud : sc.budgetRemaining.val ≤ 1
          · have hQ := timerTickBudgetOnCore_bound_exhausted_replenish_eq
              st c tid tcb scId sc st' b hB hSc hBud hStep c'
            refine pipeline_frame_of_queue_timer_eq
              (replenishOnCore st c scId (st.machine.timer + sc.period.val)) st' c' hQ
              (by rw [hM, replenishOnCore_machine]) ?_
            by_cases hcc : c = c'
            · subst hcc
              exact replenishOnCore_preserves_replenishmentPipelineOrderOnCore st c scId _ hPipe
                (by have := hPeriod scId sc hSc; omega)
            · exact replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne st c c' scId _ hcc hPipe
          · simp only [timerTickBudgetOnCore, hB, hSc, if_neg hBud, Except.ok.injEq,
              Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe
      | none =>
          simp only [timerTickBudgetOnCore, hB, hSc] at hStep
          exact absurd hStep (by simp)
  | .donated scId owner =>
      match hSc : st.getSchedContext? scId with
      | some sc =>
          by_cases hBud : sc.budgetRemaining.val ≤ 1
          · have hQ := timerTickBudgetOnCore_donated_exhausted_replenish_eq
              st c tid tcb scId owner sc st' b hB hSc hBud hStep c'
            refine pipeline_frame_of_queue_timer_eq
              (replenishOnCore st c scId (st.machine.timer + sc.period.val)) st' c' hQ
              (by rw [hM, replenishOnCore_machine]) ?_
            by_cases hcc : c = c'
            · subst hcc
              exact replenishOnCore_preserves_replenishmentPipelineOrderOnCore st c scId _ hPipe
                (by have := hPeriod scId sc hSc; omega)
            · exact replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne st c c' scId _ hcc hPipe
          · simp only [timerTickBudgetOnCore, hB, hSc, if_neg hBud, Except.ok.injEq,
              Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe
      | none =>
          simp only [timerTickBudgetOnCore, hB, hSc] at hStep
          exact absurd hStep (by simp)

/-- WS-SM SM5.I (pipeline-order, headline): the **live per-core timer tick**
preserves replenishment pipeline-order on every core, given the pre-tick
pipeline-order and that every SchedContext (on the prepared state, which the budget
tick runs against) has a positive `period` — so the budget insert `now + period` is
strictly future, and `popDue` only removes entries. -/
theorem timerTickOnCore_preserves_replenishmentPipelineOrderOnCore (st : SystemState)
    (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind)) (c' : CoreId)
    (hPipe : ∀ c'', replenishmentPipelineOrderOnCore st c'')
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).1.getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    replenishmentPipelineOrderOnCore st' c' := by
  have hPrep : ∀ c'', replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c).1 c'' :=
    fun c'' => timerTickOnCorePrepared_preserves_replenishmentPipelineOrderOnCore st c c'' (hPipe c'')
  rw [timerTickOnCore_eq_prepared] at hStep
  split at hStep
  · -- idle arm: prepared, or the round-7 local-wake reschedule (queue+timer framed)
    split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st2 hH
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        exact pipeline_frame_of_queue_timer_eq _ _ c'
          (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c' hH)
          (handleRescheduleSgiOnCore_machine_timer _ c _ hH) (hPrep c')
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst; exact hPrep c'
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st3 b tsgis hbud
        have h3 : replenishmentPipelineOrderOnCore st3 c' :=
          timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ _ _ _ c'
            (hPrep c') hPeriod hbud
        split at hStep
        · split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ c' h3 hsched
        · split at hStep
          · split at hStep
            · simp at hStep
            · rename_i st4 hH
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨hst, _⟩ := hStep; subst hst
              exact pipeline_frame_of_queue_timer_eq _ _ c'
                (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c' hH)
                (handleRescheduleSgiOnCore_machine_timer _ c _ hH) h3
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst; exact h3
    · simp at hStep

-- ============================================================================
-- §4  The aggregate: the live tick preserves `perCoreCbsInvariant`
-- ============================================================================

/-- WS-SM SM5.I (aggregate): the **live per-core timer tick** preserves the per-core
CBS invariant `perCoreCbsInvariant` (validity ∧ pipeline-order ∧ affinity-consistency).

The **validity** and **pipeline-order** conjuncts are discharged *unconditionally*
(given the pre-tick invariant + positive SchedContext periods on the prepared state):
the tick only `popDue`-removes replenish entries and re-inserts one strictly-future
entry, and never advances `machine.timer`.

The **affinity-consistency** conjunct (every queued SchedContext's bound thread is
homed on the core) is supplied here verbatim as `hAffinity` — covering the *entire*
post-state replenish queue, both the carried-over `popDue` entries and the single new
budget insert.  **This is a strictly weaker form than necessary** (it assumes the
conclusion): the tick provably never writes a TCB's `cpuAffinity` nor a SchedContext's
`boundThread`, so the carried entries' affinity is *derivable* from the pre-tick
affinity via per-phase `determineTargetCore` / `boundThread` frames, and only the new
budget insert genuinely needs the *affinity-placement invariant* (a thread current on
core `c` is homed on `c`).  The strengthened
`PerCoreTickCbsAffinity.timerTickOnCore_preserves_perCoreCbsInvariant_discharged`
**supersedes** this: it derives the carried-entries affinity (prepared + schedule
phases proven) and narrows the residual to the budget-phase frame
`hBudgetAffinity`.  This `hAffinity` form is retained for the existing call surface. -/
theorem timerTickOnCore_preserves_perCoreCbsInvariant (st : SystemState) (c : CoreId)
    (st' : SystemState) (sgis : List (CoreId × SgiKind)) (c' : CoreId)
    (hInv : ∀ c'', perCoreCbsInvariant st c'')
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).1.getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hAffinity : replenishQueueAffinityConsistentOnCore st' c')
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    perCoreCbsInvariant st' c' :=
  ⟨timerTickOnCore_preserves_replenishQueueValidOnCore st c st' sgis c'
      (fun c'' => (hInv c'').1) hStep,
   timerTickOnCore_preserves_replenishmentPipelineOrderOnCore st c st' sgis c'
      (fun c'' => (hInv c'').2.1) hPeriod hStep,
   hAffinity⟩

-- ============================================================================
-- §5  SMP clock-advance honesty (PR #880 round 4)
-- ============================================================================
--
-- `replenishmentPipelineOrderOnCore` states the *strict* form: every queued
-- deadline exceeds `machine.timer`.  Under the live per-core composition the
-- boot core's committed step advances the shared clock, and a *remote* core's
-- queue may then hold entries due at exactly the new clock until that core's
-- own next committed tick drains them — the bounded release window inherent
-- to per-core release queues (each core drains its own queue on its own PPI;
-- seL4 MCS is shaped the same way).  This section makes the true guarantee
-- formal instead of leaving the strict form to read as global-always:
--
--   * the boot clock advance makes nothing strictly overdue — every remote
--     entry satisfies the weak form `≥ timer` immediately after the advance
--     (`tickClockedState_bootCore_replenish_ge`);
--   * each core's own committed step *re-establishes* the strict form on its
--     own queue at the current clock
--     (`perCoreTimerTickStep_ok_establishes_replenishmentPipelineOrderOnCore_self`,
--     via `popDue`'s prefix-drain under sortedness).
--
-- Together: strict pipeline order is a per-core property holding from a
-- core's own committed tick until the next boot-core clock advance; between
-- a remote advance and the owner's next tick the queue is at worst due-now,
-- never silently overdue-and-growing.

/-- (local) Under `pairwiseSortedBy`, every tail entry's eligibility is at
least the head's. -/
private theorem pairwiseSortedBy_tail_ge_head (idt : SchedContextId × Nat)
    (rest : List (SchedContextId × Nat))
    (hSorted : pairwiseSortedBy (idt :: rest)) :
    ∀ p ∈ rest, idt.2 ≤ p.2 := by
  induction rest generalizing idt with
  | nil => intro p hp; simp at hp
  | cons hd tl ih =>
      intro p hp
      obtain ⟨id1, t1⟩ := idt
      obtain ⟨id2, t2⟩ := hd
      obtain ⟨hle, hrest⟩ := hSorted
      rcases List.mem_cons.mp hp with hEq | hTl
      · subst hEq; exact hle
      · exact Nat.le_trans hle (ih (id2, t2) hrest p hTl)

/-- WS-SM (PR #880 round 4): after `popDue now`, every remaining entry is
eligible strictly after `now`, under sortedness — the generic per-queue form
of the boot-core-pinned AN5-B lemma, consumed by the per-core establishment
below.  `splitDue` stops at the first not-due entry; sortedness carries the
strict bound to the whole suffix. -/
theorem popDue_remaining_gt (rq : ReplenishQueue) (now : Nat)
    (hSorted : replenishQueueSorted rq) :
    ∀ pair ∈ (rq.popDue now).1.entries, pair.2 > now := by
  intro pair hMem
  simp only [ReplenishQueue.popDue] at hMem
  unfold replenishQueueSorted at hSorted
  revert hMem hSorted
  induction rq.entries with
  | nil => intro _ hMem; simp [ReplenishQueue.splitDue] at hMem
  | cons hd tl ih =>
      intro hSort hMem
      simp only [ReplenishQueue.splitDue] at hMem
      split at hMem
      · exact ih (pairwiseSortedBy_tail hSort) hMem
      · rename_i hHdGt
        have hHd : hd.2 > now := Nat.lt_of_not_le hHdGt
        rcases List.mem_cons.mp hMem with hEq | hTl
        · rw [hEq]; exact hHd
        · exact Nat.lt_of_lt_of_le hHd (pairwiseSortedBy_tail_ge_head hd tl hSort pair hTl)

/-- WS-SM (PR #880 round 4): the boot core's shared-clock advance makes no
queued replenishment strictly overdue — every entry that satisfied the strict
form at the old clock satisfies the weak form (`≥ timer`, i.e. at worst
due-now) at the advanced clock, on every core.  The due-now window is drained
by the owning core's next committed tick (the establishment theorem below). -/
theorem tickClockedState_bootCore_replenish_ge (st : SystemState) (c' : CoreId)
    (hPipe : replenishmentPipelineOrderOnCore st c') :
    ∀ pair ∈ ((tickClockedState st bootCoreId).scheduler.replenishQueueOnCore c').entries,
      pair.2 ≥ (tickClockedState st bootCoreId).machine.timer := by
  intro pair hMem
  rw [tickClockedState_scheduler] at hMem
  rw [tickClockedState_bootCore_timer]
  exact hPipe pair hMem

/-- WS-SM (PR #880 round 4): `switchDomainOnCore` frames every core's replenish
queue — its writes are the context save (objects) and run-queue / current /
domain scheduler slots. -/
theorem switchDomainOnCore_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (c' : CoreId) (h : switchDomainOnCore st c = .ok st') :
    st'.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      simp only [SchedulerState.setDomainScheduleIndexOnCore_replenishQueueOnCore,
        SchedulerState.setDomainTimeRemainingOnCore_replenishQueueOnCore,
        SchedulerState.setActiveDomainOnCore_replenishQueueOnCore,
        SchedulerState.setCurrentOnCore_replenishQueueOnCore,
        SchedulerState.setRunQueueOnCore_replenishQueueOnCore]

/-- WS-SM (PR #880 round 4): `switchDomainOnCore` leaves the machine (and so
the shared clock) unchanged — its only object write is the context save. -/
theorem switchDomainOnCore_machine (st : SystemState) (c : CoreId)
    (st' : SystemState) (h : switchDomainOnCore st c = .ok st') :
    st'.machine = st.machine := by
  unfold switchDomainOnCore at h
  cases hcase : st.scheduler.domainSchedule with
  | nil => rw [hcase] at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons hd tl =>
    rw [hcase] at h; dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; subst h
      exact saveOutgoingContextOnCore_machine st c

/-- WS-SM (PR #880 round 4): the domain tick preserves pipeline order on every
core — the inert arm is the identity, the decrement writes one domain slot,
and the boundary composes the queue/timer-framing switch with the preserving
re-dispatch. -/
theorem scheduleDomainOnCore_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c : CoreId) (st' : SystemState) (c' : CoreId)
    (hPipe : replenishmentPipelineOrderOnCore st c')
    (hStep : scheduleDomainOnCore st c = .ok st') :
    replenishmentPipelineOrderOnCore st' c' := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · simp only [Except.ok.injEq] at hStep; subst hStep; exact hPipe
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i stMid hsw
        refine scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore
          stMid c st' c' ?_ hStep
        refine pipeline_frame_of_queue_timer_eq st stMid c' ?_ ?_ hPipe
        · exact switchDomainOnCore_replenishQueueOnCore st c stMid c' hsw
        · rw [switchDomainOnCore_machine st c stMid hsw]
    · simp only [Except.ok.injEq] at hStep; subst hStep
      refine pipeline_frame_of_queue_timer_eq st _ c' ?_ rfl hPipe
      simp [decrementDomainTimeOnCore,
        SchedulerState.setDomainTimeRemainingOnCore_replenishQueueOnCore]

/-- WS-SM (PR #880 round 4): a core's committed timer tick **re-establishes**
strict pipeline order on its own queue at the current clock — even when the
input state holds entries due at exactly `machine.timer` (the post-advance
window on the boot core, or a remote advance observed by this core's tick).
The prepared phase `popDue`-drains everything `≤ timer` (strict remainder
under sortedness); the budget phase's only insert is strictly future
(`hPeriod`); the dispatch phase frames queue and timer. -/
theorem timerTickOnCore_establishes_replenishmentPipelineOrderOnCore_self
    (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hSorted : replenishQueueSorted (st.scheduler.replenishQueueOnCore c))
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).1.getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    replenishmentPipelineOrderOnCore st' c := by
  have hPrepSelf : replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c).1 c := by
    intro pair hMem
    have hQ : (timerTickOnCorePrepared st c).1.scheduler.replenishQueueOnCore c
        = ((st.scheduler.replenishQueueOnCore c).popDue st.machine.timer).1 := by
      simp only [timerTickOnCorePrepared]
      rw [processReplenishmentsDueOnCore_replenishQueueOnCore_self]
      simp only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore]
    rw [hQ] at hMem
    rw [timerTickOnCorePrepared_machine_eq]
    exact popDue_remaining_gt _ _ hSorted pair hMem
  rw [timerTickOnCore_eq_prepared] at hStep
  split at hStep
  · -- idle arm: prepared, or the round-7 local-wake reschedule (queue+timer framed)
    split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st2 hH
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        exact pipeline_frame_of_queue_timer_eq _ _ c
          (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c hH)
          (handleRescheduleSgiOnCore_machine_timer _ c _ hH) hPrepSelf
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst; exact hPrepSelf
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st3 b tsgis hbud
        have h3 : replenishmentPipelineOrderOnCore st3 c :=
          timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ _ _ _ c
            hPrepSelf hPeriod hbud
        split at hStep
        · split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore
              _ c _ c h3 hsched
        · split at hStep
          · split at hStep
            · simp at hStep
            · rename_i st4 hH
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨hst, _⟩ := hStep; subst hst
              exact pipeline_frame_of_queue_timer_eq _ _ c
                (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c hH)
                (handleRescheduleSgiOnCore_machine_timer _ c _ hH) h3
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst; exact h3
    · simp at hStep

/-- WS-SM (PR #880 round 4, the drain guarantee): a core's **committed run-loop
step** re-establishes strict pipeline order on its own queue — the sortedness
travels across the clock advance (scheduler untouched), the tick drains the
due prefix at the advanced clock, and the domain tick preserves the result.
Instantiated at a remote core's own next PPI, this is exactly what closes the
due-now window `tickClockedState_bootCore_replenish_ge` bounds. -/
theorem perCoreTimerTickStep_ok_establishes_replenishmentPipelineOrderOnCore_self
    (st : SystemState) (coreId : UInt64) (h : coreId.toNat < numCores)
    (hSorted : replenishQueueSorted (st.scheduler.replenishQueueOnCore ⟨coreId.toNat, h⟩))
    (hPeriod : ∀ scId sc,
      (timerTickOnCorePrepared (tickClockedState st ⟨coreId.toNat, h⟩)
          ⟨coreId.toNat, h⟩).1.getSchedContext? scId = some sc → 0 < sc.period.val)
    (result : SystemState × List (CoreId × SgiKind)) (st2 : SystemState)
    (hok : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩
      = .ok result)
    (hdom : scheduleDomainOnCore result.1 ⟨coreId.toNat, h⟩ = .ok st2) :
    replenishmentPipelineOrderOnCore (perCoreTimerTickStep st coreId).1 ⟨coreId.toNat, h⟩ := by
  obtain ⟨st', sgis⟩ := result
  rw [perCoreTimerTickStep_ok st coreId h (st', sgis) st2 hok hdom]
  have hSorted' : replenishQueueSorted
      ((tickClockedState st ⟨coreId.toNat, h⟩).scheduler.replenishQueueOnCore
        ⟨coreId.toNat, h⟩) := by
    rw [tickClockedState_scheduler]; exact hSorted
  have hSelf := timerTickOnCore_establishes_replenishmentPipelineOrderOnCore_self
    (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ st' sgis hSorted' hPeriod hok
  exact scheduleDomainOnCore_preserves_replenishmentPipelineOrderOnCore st'
    ⟨coreId.toNat, h⟩ st2 ⟨coreId.toNat, h⟩ hSelf hdom

end SeLe4n.Kernel
