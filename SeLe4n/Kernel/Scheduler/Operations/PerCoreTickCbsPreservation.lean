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

Production since **WS-LS LS2.2**: `timerTickBracket`'s coverage field
(`SchedLockBracket.lean`) consumes `perCoreTimerTickStep_coversWrites`, whose
replenish clause chains through this module, so the module sits in the
production closure.  The SM5.I per-core run loop is the runtime exerciser; the
theorems here are the formal preservation guarantee.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId SgiKind bootCoreId)

-- ============================================================================
-- §1  Replenish-queue frames for the SM5.D.4 replenishment machinery
-- ============================================================================

-- `v0.35.167` (WS-RR RR8.12 Cut C3b-i): `enqueueRunnableOnCore_replenishQueueOnCore`
-- moved to `Scheduler/Operations/Selection.lean`, beside the definition it frames.
-- It was declared here, in a **staged** module, which production may not import —
-- so the live `.tcbResume` arm's own scheduler-domain footprint could not state
-- that the resume moves no replenish entry.  Same shape as `v0.35.166`'s five
-- relocations: a frame about a production definition, sitting downstream of every
-- asker that needs it.

/-- WS-SM SM5.I: `processOneReplenishmentOnCore` leaves every core's replenish-queue
slot unchanged — it refills a SchedContext (whole scheduler framed) and optionally
wakes a thread (a run-queue write), never touching a replenish queue. -/
theorem processOneReplenishmentOnCore_replenishQueueOnCore_eq (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (c' : CoreId) :
    (processOneReplenishmentOnCore st ec scId now).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  rw [processOneReplenishmentOnCore, markRefillKeyChange_replenishQueueOnCore]
  simp only [refillWakeOnCore]
  split
  · split
    · rw [refillSchedContext_scheduler_eq]
    · rw [SchedulerState.markReschedulePendingOnCoreIf_replenishQueueOnCore,
        wakeThread_state_eq_enqueue, enqueueRunnableOnCore_replenishQueueOnCore,
        refillSchedContext_scheduler_eq]
  · rw [refillSchedContext_scheduler_eq]

/-- WS-SM SM5.I: the wake fold inside `processReplenishmentsDueOnCore` preserves every
core's replenish-queue slot (each step is a `processOneReplenishmentOnCore`). -/
theorem foldl_processOneReplenishment_replenishQueueOnCore (c : CoreId) (now : Nat) (c' : CoreId)
    (dueIds : List SeLe4n.SchedContextId)
    (acc : SystemState) :
    (dueIds.foldl (fun acc scId => processOneReplenishmentOnCore acc c scId now) acc).scheduler.replenishQueueOnCore c'
      = acc.scheduler.replenishQueueOnCore c' := by
  induction dueIds generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
      rw [List.foldl_cons, ih]
      exact processOneReplenishmentOnCore_replenishQueueOnCore_eq acc c hd now c'

/-- WS-SM SM5.I: core `c`'s replenish queue after `processReplenishmentsDueOnCore` is
exactly the `popDue` remainder (the wake fold never re-inserts). -/
theorem processReplenishmentsDueOnCore_replenishQueueOnCore_self (st : SystemState)
    (c : CoreId) (now : Nat) :
    (processReplenishmentsDueOnCore st c now).scheduler.replenishQueueOnCore c
      = ((st.scheduler.replenishQueueOnCore c).popDue now).1 := by
  simp only [processReplenishmentsDueOnCore]
  rw [foldl_processOneReplenishment_replenishQueueOnCore]
  simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]

/-- WS-SM SM5.I: every *other* core's replenish queue is unchanged by
`processReplenishmentsDueOnCore` (`popDue` writes only core `c`'s slot). -/
theorem processReplenishmentsDueOnCore_replenishQueueOnCore_ne (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) (h : c ≠ c') :
    (processReplenishmentsDueOnCore st c now).scheduler.replenishQueueOnCore c'
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
    restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
    SystemState.runRemoveOnCore_scheduler, SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore]

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
      rw [SystemState.clearReschedulePendingOnCore_scheduler,
        SchedulerState.clearReschedulePendingOnCore_replenishQueueOnCore,
        idleFallbackOnCore_replenishQueueOnCore, saveOutgoingContextOnCore_scheduler_eq]
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        split at hStep
        · simp only [Except.ok.injEq] at hStep
          rw [← hStep]
          simp only [SchedulerState.clearReschedulePendingOnCore_replenishQueueOnCore,
            SchedulerState.setCurrentOnCore_replenishQueueOnCore,
            restoreIncomingContextOnCore_scheduler, SchedulerState.setRunQueueOnCore_replenishQueueOnCore,
    SystemState.runRemoveOnCore_scheduler, SchedulerState.setRunQueueEndsOnCore_replenishQueueOnCore]
          rw [saveOutgoingContextOnCore_scheduler_eq]
        · simp at hStep

/-- WS-SM SM5.I (validity, item 4): `processReplenishmentsDueOnCore` preserves
replenish-queue **validity** on every core — core `c`'s queue is the `popDue`
remainder (sorted + size-consistent are preserved by removal); every other core's is
unchanged. -/
theorem processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) (hValid : replenishQueueValidOnCore st c') :
    replenishQueueValidOnCore (processReplenishmentsDueOnCore st c now) c' := by
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
    replenishQueueValidOnCore (timerTickOnCorePrepared st c) c' := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore
  unfold replenishQueueValidOnCore at hValid ⊢
  simpa only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] using hValid

/-- WS-SM SM5.I (item 4, headline): the **live per-core timer tick** preserves
replenish-queue validity on every core.  The prepared phase preserves it, the SM5.H
§14 budget-tick A4 preserves it, and a preempting `scheduleEffectiveOnCore` frames
it. -/
theorem timerTickOnCore_preserves_replenishQueueValidOnCore (st : SystemState) (c : CoreId)
    (c' : CoreId) (hValid : ∀ c'', replenishQueueValidOnCore st c'') :
    replenishQueueValidOnCore (timerTickOnCore st c) c' := by
  have hPrep : ∀ c'', replenishQueueValidOnCore (timerTickOnCorePrepared st c) c'' :=
    fun c'' => timerTickOnCorePrepared_preserves_replenishQueueValidOnCore st c c'' (hValid c'')
  refine timerTickOnCore_of (P := fun s => ∀ c'', replenishQueueValidOnCore s c'') st c hPrep
    ?_ ?_ ?_ c'
  · intro s hs c''
    have h2 := hs c''
    unfold replenishQueueValidOnCore at h2 ⊢
    rw [handleRescheduleSgiOnCore_replenishQueueOnCore s c _ c''
      (handleRescheduleSgiOnCore_eq_state s c)]
    exact h2
  · intro s hs c''
    have h2 := hs c''
    unfold replenishQueueValidOnCore at h2 ⊢
    rw [scheduleEffectiveOnCore_replenishQueueOnCore s c _ c'' (scheduleEffectiveOnCore_eq_state s c)]
    exact h2
  · intro tid tcb hTcb st3 b hb c''
    exact timerTickBudgetOnCore_preserves_replenishQueueValidOnCore _ c _ _ _ _ c'' hPrep hb

-- ============================================================================
-- §2  Machine-timer frames (the per-core tick reads but never advances the
--     global timer — the substrate for pipeline-order preservation)
-- ============================================================================

/-- WS-SM SM5.I: `ensureRunnable` leaves the machine unchanged (it writes only a
run queue). -/
theorem ensureRunnable_machine (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).machine = st.machine := by
  have h := ensureRunnable_onlyObjectsSchedulerDiffer st tid
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- WS-SM SM5.I: `saveOutgoingContextOnCore` leaves the machine unchanged (it saves
the register context *into* the outgoing TCB; it reads `machine.regs` but writes
only the object store). -/
theorem saveOutgoingContextOnCore_machine (st : SystemState) (c : CoreId) :
    (saveOutgoingContextOnCore st c).machine = st.machine := by
  unfold saveOutgoingContextOnCore; split
  · rfl
  · exact SystemState.updateTcb_machine _ _ _

/-- WS-SM SM5.I: `restoreIncomingContext` leaves the machine **timer** unchanged — it
writes only `machine.regs` (the register file), never the global timer. -/
theorem restoreIncomingContext_machine_timer (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).machine.timer = st.machine.timer := by
  unfold restoreIncomingContext SystemState.getTcb?; split <;> rfl

-- WS-OD OD1.4: `endpointQueueRemove_machine` moved to
-- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` and `abortPendingIpcOnEndpoint_machine`
-- to `SeLe4n/Kernel/IPC/Operations/Timeout.lean`, each beside the operation it
-- is about and beside that operation's `_scheduler_eq` sibling.  The cancellation reclaim needs the abort's machine frame and does
-- not import this scheduler module; one home per question is the fix, not a
-- second proof.

/-- WS-SM SM5.I: `timeoutThread` leaves the machine unchanged — every step
(`endpointQueueRemove`, `storeObject`, `ensureRunnable`, optional
`revertPriorityInheritance`) writes only the object store / run queues.  Mirrors
`timeoutThread_replenishQueueOnCore`. -/
theorem timeoutThread_machine (epId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (execCore : CoreId) (st : SystemState)
    (r : SystemState × Option (CoreId × SgiKind))
    (h : timeoutThread epId isReceiveQ tid execCore st = .ok r) :
    r.1.machine = st.machine := by
  -- WS-OD OD1.2: the removal and the TCB store are the abort's; compose its
  -- own machine frame rather than re-deriving the case analysis.
  unfold timeoutThread at h
  split at h
  · simp at h
  · rename_i st2 hAbort
    have hMach2 : st2.machine = st.machine :=
      abortPendingIpcOnEndpoint_machine epId isReceiveQ tid st st2 hAbort
    simp only [] at h
    split at h <;>
      · simp only [Except.ok.injEq] at h
        subst h
        first
          | rw [PriorityInheritance.revert_preserves_machine]
          | skip
        try rw [SystemState.unlinkReplyWaiter_machine]
        rw [wakeThread_state_eq_enqueue, enqueueRunnableOnCore_machine_eq]
        show st2.machine = st.machine
        rw [hMach2]

/-- WS-SM SM5.I: timing out **all** of a SchedContext's IPC-blocked threads leaves the
machine unchanged (each step is a `timeoutThread`).  Mirrors
`timeoutBlockedThreads_replenishQueueOnCore`. -/
theorem timeoutBlockedThreads_machine (st : SystemState) (scId : SeLe4n.SchedContextId)
    (execCore : CoreId) :
    (timeoutBlockedThreads st scId execCore).1.machine = st.machine := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) :
    st'.machine = st.machine := by
  unfold timerTickBudgetOnCore budgetExhaustOnCore spendBudgetOnCore sliceExpireOnCore at hStep
  dsimp only [SystemState.rewriteObject] at hStep
  split at hStep
  · -- unbound: both time-slice arms are object/scheduler writes
    split at hStep <;>
      · simp only [Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst; simp
  all_goals
    -- bound and donated: identical structure (getSchedContext? then the budget `if`)
    split at hStep
    · split at hStep
      · -- budget exhausted (the `timeoutBlockedThreads` machine-frame closes it)
        simp only [Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst
        simp [timeoutBlockedThreads_machine, replenishOnCore]
      · -- budget > 1
        simp only [Prod.mk.injEq] at hStep
        obtain ⟨hst, _⟩ := hStep; subst hst; rfl
    · simp only [Prod.mk.injEq] at hStep
      obtain ⟨hst, _⟩ := hStep; subst hst; rfl

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
theorem timerTickOnCore_machine_timer_eq (st : SystemState) (c : CoreId) :
    (timerTickOnCore st c).machine.timer = st.machine.timer := by
  refine timerTickOnCore_of (P := fun s => s.machine.timer = st.machine.timer) st c
    (by show (timerTickOnCorePrepared st c).machine.timer = _; rw [timerTickOnCorePrepared_machine_eq]) ?_ ?_ ?_
  · intro s hs
    rw [handleRescheduleSgiOnCore_machine_timer s c _ (handleRescheduleSgiOnCore_eq_state s c)]
    exact hs
  · intro s hs
    rw [scheduleEffectiveOnCore_machine_timer s c _ (scheduleEffectiveOnCore_eq_state s c)]
    exact hs
  · intro tid tcb hTcb st3 b hb
    rw [timerTickBudgetOnCore_machine _ c _ _ _ _ hb, timerTickOnCorePrepared_machine_eq]

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
    replenishmentPipelineOrderOnCore (processReplenishmentsDueOnCore st c now) c' := by
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
    replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c) c' := by
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
    {hW : st.getTcb? tid = some tcb}
    (hStep : timerTickBudgetOnCore st c tid tcb hW = (st', b)) :
    replenishmentPipelineOrderOnCore st' c' := by
  have hM : st'.machine.timer = st.machine.timer := by
    rw [timerTickBudgetOnCore_machine st c tid tcb st' b hStep]
  match hB : tcb.schedContextBinding with
  | .unbound =>
      simp only [timerTickBudgetOnCore, sliceExpireOnCore, SystemState.rewriteObject, hB] at hStep
      split at hStep <;>
        · simp only [Prod.mk.injEq] at hStep
          obtain ⟨hst, _⟩ := hStep; subst hst
          exact pipeline_frame_of_queue_timer_eq st _ c' (by simp) hM hPipe
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
          · simp only [timerTickBudgetOnCore, budgetExhaustOnCore, spendBudgetOnCore, SystemState.rewriteObject, hB, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hBud,
              Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe
      | none =>
          simp only [timerTickBudgetOnCore, hB, SystemState.getSchedContextWitnessed?_eq_none hSc,
            Prod.mk.injEq] at hStep
          obtain ⟨hst, _⟩ := hStep; subst hst
          exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe
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
          · simp only [timerTickBudgetOnCore, budgetExhaustOnCore, spendBudgetOnCore, SystemState.rewriteObject, hB, SystemState.getSchedContextWitnessed?_eq_some hSc, if_neg hBud,
              Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe
      | none =>
          simp only [timerTickBudgetOnCore, hB, SystemState.getSchedContextWitnessed?_eq_none hSc,
            Prod.mk.injEq] at hStep
          obtain ⟨hst, _⟩ := hStep; subst hst
          exact pipeline_frame_of_queue_timer_eq st _ c' rfl hM hPipe

/-- WS-SM SM5.I (pipeline-order, headline): the **live per-core timer tick**
preserves replenishment pipeline-order on every core, given the pre-tick
pipeline-order and that every SchedContext (on the prepared state, which the budget
tick runs against) has a positive `period` — so the budget insert `now + period` is
strictly future, and `popDue` only removes entries. -/
theorem timerTickOnCore_preserves_replenishmentPipelineOrderOnCore (st : SystemState)
    (c : CoreId) (c' : CoreId)
    (hPipe : ∀ c'', replenishmentPipelineOrderOnCore st c'')
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val) :
    replenishmentPipelineOrderOnCore (timerTickOnCore st c) c' := by
  have hPrep : ∀ c'', replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c) c'' :=
    fun c'' => timerTickOnCorePrepared_preserves_replenishmentPipelineOrderOnCore st c c'' (hPipe c'')
  refine timerTickOnCore_of (P := fun s => ∀ c'', replenishmentPipelineOrderOnCore s c'') st c hPrep
    ?_ ?_ ?_ c'
  · intro s hs c''
    have hH := handleRescheduleSgiOnCore_eq_state s c
    exact pipeline_frame_of_queue_timer_eq _ _ c''
      (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c'' hH)
      (handleRescheduleSgiOnCore_machine_timer _ c _ hH) (hs c'')
  · intro s hs c''
    exact scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ c'' (hs c'')
      (scheduleEffectiveOnCore_eq_state s c)
  · intro tid tcb hTcb st3 b hb c''
    exact timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ _ _ _ c''
      (hPrep c'') hPeriod hb

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
    (c' : CoreId)
    (hInv : ∀ c'', perCoreCbsInvariant st c'')
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hAffinity : replenishQueueAffinityConsistentOnCore (timerTickOnCore st c) c') :
    perCoreCbsInvariant (timerTickOnCore st c) c' :=
  ⟨timerTickOnCore_preserves_replenishQueueValidOnCore st c c'
      (fun c'' => (hInv c'').1),
   timerTickOnCore_preserves_replenishmentPipelineOrderOnCore st c c'
      (fun c'' => (hInv c'').2.1) hPeriod,
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
--     (`perCoreTimerTickStep_establishes_replenishmentPipelineOrderOnCore_self`,
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
        SchedulerState.setCurrentOnCore_replenishQueueOnCore]
      obtain ⟨E, hE⟩ := requeueOutgoingOnCore_scheduler st c
      rw [hE]; simp

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
      exact (requeueOutgoingOnCore_machine st c).trans (saveOutgoingContextOnCore_machine st c)

/-- **WS-RR RR7.39 (frame)**: the domain tick never touches any core's replenish
queue.

Three arms, none of which reaches a replenishment: single-domain mode is the
identity, the boundary composes the queue-framing `switchDomainOnCore` with the
queue-framing `scheduleEffectiveOnCore`, and the non-boundary arm writes one
domain-time slot.

Consumed by `perCoreTimerTickStep_replenishQueueOnCore_ne` (RR7.39), which is the
last link in "the tick writes only its own core's replenish queue" — the fact the
tick's declared footprint asserts when it names `replenishQueue ⟨c⟩` alone. -/
theorem scheduleDomainOnCore_replenishQueueOnCore (st : SystemState) (c : CoreId)
    (st' : SystemState) (c' : CoreId) (hStep : scheduleDomainOnCore st c = .ok st') :
    st'.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  unfold scheduleDomainOnCore at hStep
  split at hStep
  · simp only [Except.ok.injEq] at hStep; subst hStep; rfl
  · split at hStep
    · split at hStep
      · simp at hStep
      · rename_i stMid hsw
        rw [scheduleEffectiveOnCore_replenishQueueOnCore stMid c st' c' hStep,
          switchDomainOnCore_replenishQueueOnCore st c stMid c' hsw]
    · simp only [Except.ok.injEq] at hStep; subst hStep
      simp [decrementDomainTimeOnCore,
        SchedulerState.setDomainTimeRemainingOnCore_replenishQueueOnCore]

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
    (st : SystemState) (c : CoreId)
    (hSorted : replenishQueueSorted (st.scheduler.replenishQueueOnCore c))
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val) :
    replenishmentPipelineOrderOnCore (timerTickOnCore st c) c := by
  have hPrepSelf : replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c) c := by
    intro pair hMem
    have hQ : (timerTickOnCorePrepared st c).scheduler.replenishQueueOnCore c
        = ((st.scheduler.replenishQueueOnCore c).popDue st.machine.timer).1 := by
      simp only [timerTickOnCorePrepared]
      rw [processReplenishmentsDueOnCore_replenishQueueOnCore_self]
      simp only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore]
    rw [hQ] at hMem
    rw [timerTickOnCorePrepared_machine_eq]
    exact popDue_remaining_gt _ _ hSorted pair hMem
  refine timerTickOnCore_of (P := fun s => replenishmentPipelineOrderOnCore s c) st c hPrepSelf
    ?_ ?_ ?_
  · intro s hs
    have hH := handleRescheduleSgiOnCore_eq_state s c
    exact pipeline_frame_of_queue_timer_eq _ _ c
      (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c hH)
      (handleRescheduleSgiOnCore_machine_timer _ c _ hH) hs
  · intro s hs
    exact scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ c hs
      (scheduleEffectiveOnCore_eq_state s c)
  · intro tid tcb hTcb st3 b hb
    exact timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ _ _ _ c
      hPrepSelf hPeriod hb

/-- WS-SM (PR #880 round 4, the drain guarantee): a core's **committed run-loop
step** re-establishes strict pipeline order on its own queue — the sortedness
travels across the clock advance (scheduler untouched), the tick drains the
due prefix at the advanced clock, and the domain tick preserves the result.
Instantiated at a remote core's own next PPI, this is exactly what closes the
due-now window `tickClockedState_bootCore_replenish_ge` bounds. -/
theorem perCoreTimerTickStep_establishes_replenishmentPipelineOrderOnCore_self
    (st : SystemState) (coreId : UInt64) (h : coreId.toNat < numCores)
    (hSorted : replenishQueueSorted (st.scheduler.replenishQueueOnCore ⟨coreId.toNat, h⟩))
    (hPeriod : ∀ scId sc,
      (timerTickOnCorePrepared (tickClockedState st ⟨coreId.toNat, h⟩)
          ⟨coreId.toNat, h⟩).getSchedContext? scId = some sc → 0 < sc.period.val) :
    replenishmentPipelineOrderOnCore (perCoreTimerTickStep st coreId).1 ⟨coreId.toNat, h⟩ := by
  rw [perCoreTimerTickStep_valid_core st coreId h]
  have hSorted' : replenishQueueSorted
      ((tickClockedState st ⟨coreId.toNat, h⟩).scheduler.replenishQueueOnCore
        ⟨coreId.toNat, h⟩) := by
    rw [tickClockedState_scheduler]; exact hSorted
  have hSelf := timerTickOnCore_establishes_replenishmentPipelineOrderOnCore_self
    (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ hSorted' hPeriod
  exact scheduleDomainOnCore_preserves_replenishmentPipelineOrderOnCore _
    ⟨coreId.toNat, h⟩ _ ⟨coreId.toNat, h⟩ hSelf (scheduleDomainOnCore_eq_state _ _)

end SeLe4n.Kernel
