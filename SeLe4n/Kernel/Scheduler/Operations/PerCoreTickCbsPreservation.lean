-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs

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
    (acc : SystemState × List (CoreId × SgiKind)) :
    (dueIds.foldl (fun acc scId =>
        let (s, sgi?) := processOneReplenishmentOnCore acc.1 c scId now
        (s, acc.2 ++ sgi?.toList)) acc).1.scheduler.replenishQueueOnCore c'
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
    restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_replenishQueueOnCore]

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
            restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_replenishQueueOnCore]
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
  · -- idle: result is the prepared state
    rw [Except.ok.injEq] at hStep
    have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
    rw [← hst]; exact hPrep c'
  · split at hStep
    · split at hStep
      · simp at hStep
      · -- budget tick `.ok (st3, b)`
        rename_i st3 b hbud
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
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ =>
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
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (h : timeoutThread epId isReceiveQ tid st = .ok st') :
    st'.machine = st.machine := by
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
          rw [ensureRunnable_machine]
          show st1.machine = st.machine
          rw [hMach1]

/-- WS-SM SM5.I: timing out **all** of a SchedContext's IPC-blocked threads leaves the
machine unchanged (each step is a `timeoutThread`).  Mirrors
`timeoutBlockedThreads_replenishQueueOnCore`. -/
theorem timeoutBlockedThreads_machine (st : SystemState) (scId : SeLe4n.SchedContextId) :
    (timeoutBlockedThreads st scId).1.machine = st.machine := by
  unfold timeoutBlockedThreads
  suffices hFold : ∀ (tids : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError)),
      (tids.foldl (fun (acc : SystemState × List (SeLe4n.ThreadId × KernelError)) tid =>
        match acc.1.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match timeoutThread epId isReceiveQ tid acc.1 with
            | .ok st'' => (st'', acc.2)
            | .error e => (acc.1, acc.2 ++ [(tid, e)])
          | none => (acc.1, acc.2)
        | none => (acc.1, acc.2)) acc).1.machine = acc.1.machine by
    exact hFold _ (st, [])
  intro tids
  induction tids with
  | nil => intro acc; rfl
  | cons hd tail ih =>
    intro acc
    rw [List.foldl_cons, ih]
    split
    · split
      · split
        · next st'' heqTo => exact timeoutThread_machine _ _ hd acc.1 st'' heqTo
        · rfl
      · rfl
    · rfl

/-- WS-SM SM5.I: the per-core budget tick leaves the machine unchanged — every
branch writes only the object store / scheduler slots (the bound-exhausted branch's
`timeoutBlockedThreads` is machine-framed). -/
theorem timerTickBudgetOnCore_machine (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (st' : SystemState) (b : Bool)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) :
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
  simp [dispatchIdleOnCore, restoreIncomingContext_machine_timer]

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
          simp [restoreIncomingContext_machine_timer, saveOutgoingContextOnCore_machine]
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
  · rw [Except.ok.injEq] at hStep
    have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
    rw [← hst, hPrepM]
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st3 b hbud
        have h3 : st3.machine = (timerTickOnCorePrepared st c).1.machine :=
          timerTickBudgetOnCore_machine _ c _ _ _ _ hbud
        split at hStep
        · split at hStep
          · simp at hStep
          · rename_i st4 hsched
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            rw [scheduleEffectiveOnCore_machine_timer _ c _ hsched, h3, hPrepM]
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
    (hPipe : replenishmentPipelineOrderOnCore st c')
    (hPeriod : ∀ scId sc, st.getSchedContext? scId = some sc → 0 < sc.period.val)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) :
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
  · rw [Except.ok.injEq] at hStep
    have hst : (timerTickOnCorePrepared st c).1 = st' := by rw [hStep]
    rw [← hst]; exact hPrep c'
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i st3 b hbud
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

end SeLe4n.Kernel
