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

/-- The wake's enqueue writes a thread alone: every scheduling context reads the
same. -/
theorem enqueueRunnableOnCore_getSchedContext? (st : SystemState) (c : CoreId)
    (tid0 : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (enqueueRunnableOnCore st c tid0).getSchedContext? scId = st.getSchedContext? scId := by
  cases hTcb : st.getTcb? tid0 with
  | none =>
    unfold enqueueRunnableOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hTcb]
  | some tcb =>
    cases hR : wakeDeclines st c tid0 with
    | true => rw [enqueueRunnableOnCore_eq_self_of_declines st c tid0 hR]
    | false =>
      have hRaw := (SystemState.getTcb?_eq_some_iff st tid0 tcb).mp hTcb
      rw [(enqueueRunnableOnCore_objectsAgree_marked st c tid0 tcb hTcb hR).getSchedContext? scId,
        getSchedContext?_insert_tcb_eq st _ tid0 tcb (tcb.setIpcState .ready)
          hInv hRaw rfl scId]

/-- WS-ZA ZA6.3: a replenishment's only context write is its refill — the wake
writes a thread and the key hook a reschedule flag. -/
theorem processOneReplenishmentOnCore_getSchedContext? (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt)
    (s : SeLe4n.SchedContextId) :
    (processOneReplenishmentOnCore st ec scId now).getSchedContext? s =
      (refillSchedContext st scId now).getSchedContext? s := by
  rw [processOneReplenishmentOnCore,
    markRefillKeyChange_extract_frame (fun x => x.getSchedContext? s) _ _ _ (fun _ _ => rfl)]
  simp only [refillWakeOnCore]
  split
  · split
    · rfl
    · show (wakeThread _ _ _).1.getSchedContext? s = _
      rw [wakeThread_state_eq_enqueue]
      exact enqueueRunnableOnCore_getSchedContext? _ _ _
        (refillSchedContext_preserves_objects_invExt st scId now hInv) s
  · rfl

/-- WS-ZA ZA6.3: a replenishment writes no release queue: the refill keeps the
context's release fields, the wake writes a thread and a run queue. -/
theorem processOneReplenishmentOnCore_releaseStateAgree (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) :
    SystemState.releaseStateAgree (processOneReplenishmentOnCore st ec scId now) st := by
  have hR : SystemState.releaseStateAgree (refillSchedContext st scId now) st :=
    SystemState.releaseStateAgree.updateSchedContext st scId _ hInv (fun sc => by
      have hD : ∀ x : SchedContext, (cbsUpdateDeadline x now true).releaseNextCode = x.releaseNextCode ∧
          (cbsUpdateDeadline x now true).releaseCoreCode = x.releaseCoreCode ∧
          (cbsUpdateDeadline x now true).releaseAt = x.releaseAt := by
        intro x; unfold cbsUpdateDeadline; split <;> exact ⟨rfl, rfl, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hD (processReplenishments sc now)
      rw [h1, h2, h3]
      unfold processReplenishments
      split
      simp only [SchedContext.withReplenishments_releaseNextCode,
        SchedContext.withReplenishments_releaseCoreCode, SchedContext.withReplenishments_releaseAt]
      exact ⟨rfl, rfl, rfl⟩)
  refine SystemState.releaseStateAgree.trans ⟨?_, ?_⟩ hR
  · exact SystemState.ReleaseLinksAgree.of_getSchedContext?
      (processOneReplenishmentOnCore_getSchedContext? st ec scId now hInv)
  · rw [processOneReplenishmentOnCore, markRefillKeyChange_extract_frame
      (fun x => x.scheduler.releaseSlots) _ _ _ (fun _ _ => rfl)]
    simp only [refillWakeOnCore]
    split
    · split
      · rfl
      · show (SchedulerState.markReschedulePendingOnCoreIf _ _ _).releaseSlots = _
        rw [wakeThread_state_eq_enqueue]
        rcases enqueueRunnableOnCore_scheduler_cases (refillSchedContext st scId now)
          (determineTargetCore (refillSchedContext st scId now) _) _ with h | ⟨E, p, h⟩ <;>
          · rw [h]; rfl
    · rfl

/-- WS-ZA ZA6.3: **a refilled context's place is in the future** — the refill
at `now` keeps only the refills released after `now`. -/
theorem processOneReplenishmentOnCore_releaseKeyOf_gt (st : SystemState) (ec : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) :
    ∀ t, (processOneReplenishmentOnCore st ec scId now).releaseKeyOf scId = some t → t > now := by
  intro t ht
  unfold SystemState.releaseKeyOf at ht
  rw [processOneReplenishmentOnCore_getSchedContext? st ec scId now hInv, refillSchedContext,
    SystemState.updateSchedContext_getSchedContext?_self _ _ _ hInv] at ht
  cases h : st.getSchedContext? scId with
  | none => rw [h] at ht; cases ht
  | some sc =>
    rw [h] at ht
    exact refilledSchedContext_releaseKey_gt sc now t ht

/-- WS-SM SM5.I / WS-ZA ZA6.3: every *other* core's replenish queue is unchanged by
`processReplenishmentsDueOnCore`: each refill writes no queue and each
re-placement writes core `c`'s alone. -/
theorem processReplenishmentsDueOnCore_replenishQueueOnCore_ne (st : SystemState)
    (c : CoreId) (now : Nat) (c' : CoreId) (h : c ≠ c') :
    (processReplenishmentsDueOnCore st c now).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' :=
  processReplenishmentsDueOnCore_frame (fun s => s.scheduler.replenishQueueOnCore c') st c now
    (fun s scId => processOneReplenishmentOnCore_replenishQueueOnCore_eq s c scId now c')
    (fun s scId => SystemState.releasePlace_replenishQueueOnCore_ne s c scId c' (Ne.symm h))

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
replenish-queue **validity** on every core — each refill writes no queue, and
each re-placement is a removal then a sorted insert on core `c` alone
(WS-ZA ZA6.3). -/
theorem processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore (st : SystemState)
    (c : CoreId) (now : Nat) (hValid : ∀ c', replenishQueueValidOnCore st c') :
    ∀ c', replenishQueueValidOnCore (processReplenishmentsDueOnCore st c now) c' :=
  processReplenishmentsDueOnCore_induction (fun s => ∀ c', replenishQueueValidOnCore s c')
    st c now
    (fun s scId h c' => by
      unfold replenishQueueValidOnCore at h ⊢
      rw [processOneReplenishmentOnCore_replenishQueueOnCore_eq]; exact h c')
    (fun s scId h => replenishOnCore_preserves_replenishQueueValid_smp s c scId h) hValid

/-- WS-SM SM5.I: the prepared (clear + `processReplenishmentsDueOnCore`) phase
preserves replenish-queue validity on every core. -/
theorem timerTickOnCorePrepared_preserves_replenishQueueValidOnCore (st : SystemState)
    (c : CoreId) (hValid : ∀ c', replenishQueueValidOnCore st c') :
    ∀ c', replenishQueueValidOnCore (timerTickOnCorePrepared st c) c' := by
  simp only [timerTickOnCorePrepared]
  apply processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore
  intro c'
  unfold replenishQueueValidOnCore at hValid ⊢
  simpa only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] using hValid c'

/-- WS-SM SM5.I (item 4, headline): the **live per-core timer tick** preserves
replenish-queue validity on every core.  The prepared phase preserves it, the SM5.H
§14 budget-tick A4 preserves it, and a preempting `scheduleEffectiveOnCore` frames
it. -/
theorem timerTickOnCore_preserves_replenishQueueValidOnCore (st : SystemState) (c : CoreId)
    (c' : CoreId) (hValid : ∀ c'', replenishQueueValidOnCore st c'') :
    replenishQueueValidOnCore (timerTickOnCore st c) c' := by
  have hPrep : ∀ c'', replenishQueueValidOnCore (timerTickOnCorePrepared st c) c'' :=
    timerTickOnCorePrepared_preserves_replenishQueueValidOnCore st c hValid
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

/-- WS-SM SM5.I (helper): pipeline-order transfers across a replenish-queue + timer
equality. -/
private theorem pipeline_frame_of_queue_timer_eq (st base : SystemState) (c' : CoreId)
    (hQ : base.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c')
    (hM : base.machine.timer = st.machine.timer)
    (hPipe : replenishmentPipelineOrderOnCore st c') :
    replenishmentPipelineOrderOnCore base c' := by
  intro pair hMem; rw [hQ] at hMem; rw [hM]; exact hPipe pair hMem

/-- WS-ZA ZA6.3: **a property every pass of the drain keeps holds after it** — a
pass takes the context at core `c`'s head, refills it and places that same
context again, so a proof may read the head and the refill's outcome at the
placement. -/
theorem drainDueOnCore_induction_pass (P : SystemState → Prop) (c : CoreId) (now : Nat)
    (hPass : ∀ s scId, P s → s.scheduler.releaseHeadOnCore c ≠ 0 →
      ReleaseChain.decode (s.scheduler.releaseHeadOnCore c) = scId →
      P ((processOneReplenishmentOnCore s c scId now).releasePlace c scId)) :
    ∀ f st, P st → P (drainDueOnCore c now f st)
  | 0, _, h => h
  | f + 1, st, h => by
    unfold drainDueOnCore
    dsimp only
    split
    · exact h
    · rename_i h0
      split
      · exact drainDueOnCore_induction_pass P c now hPass f _ (hPass _ _ h h0 rfl)
      · exact h

/-- On a refined queue, a nonzero head names a queued context. -/
theorem releaseHead_mem {s : SystemState} {c : CoreId} (hR : s.releaseQueueRefinedOnCore c)
    (h0 : s.scheduler.releaseHeadOnCore c ≠ 0) :
    ReleaseChain.decode (s.scheduler.releaseHeadOnCore c) ∈ s.releaseIds c := by
  have hch := hR.chain
  cases hl : s.releaseIds c with
  | nil => rw [hl] at hch; exact absurd hch h0
  | cons x r =>
    rw [hl] at hch
    rw [hch.1, ReleaseChain.decode_code]
    exact List.mem_cons_self ..

/-- WS-ZA ZA6.3: **the drain keeps every release queue refined** — a refill
writes no release field, and a placement keeps the agreement. -/
theorem processReplenishmentsDueOnCore_preserves_releaseQueueRefined (st : SystemState)
    (c : CoreId) (now : Nat) (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined) :
    (processReplenishmentsDueOnCore st c now).releaseQueueRefined :=
  (drainDueOnCore_induction_pass (fun s => s.objects.invExt ∧ s.releaseQueueRefined) c now
    (fun s scId ⟨hI, hR⟩ _ _ =>
      ⟨SystemState.releasePlace_objects_invExt _ c scId
          (processOneReplenishmentOnCore_preserves_objects_invExt s c scId now hI),
        SystemState.releasePlace_refined
          ((processOneReplenishmentOnCore_releaseStateAgree s c scId now hI).refined hR) c scId⟩)
    _ st ⟨hInv, hRef⟩).2

/-- WS-SM SM5.I / WS-ZA ZA6.3: `processReplenishmentsDueOnCore` preserves
pipeline-order on every core — a pass places the refilled context at its
earliest pending refill, which the refill at `now` left after `now`, writes no
other core's queue, and never advances the timer. -/
theorem processReplenishmentsDueOnCore_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c : CoreId) (now : Nat) (hInv : st.objects.invExt)
    (hNow : st.machine.timer ≤ now) (hPipe : ∀ c', replenishmentPipelineOrderOnCore st c') :
    ∀ c', replenishmentPipelineOrderOnCore (processReplenishmentsDueOnCore st c now) c' := by
  refine (drainDueOnCore_induction_pass (fun s => s.objects.invExt ∧ s.machine.timer ≤ now ∧
      ∀ c', replenishmentPipelineOrderOnCore s c') c now ?_ _ st ⟨hInv, hNow, hPipe⟩).2.2
  rintro s scId ⟨hI, hT, hP⟩ - -
  have hI1 := processOneReplenishmentOnCore_preserves_objects_invExt s c scId now hI
  have hM : (processOneReplenishmentOnCore s c scId now).machine = s.machine :=
    processOneReplenishmentOnCore_machine_eq s c scId now
  have hP1 : ∀ c', replenishmentPipelineOrderOnCore (processOneReplenishmentOnCore s c scId now) c' :=
    fun c' => pipeline_frame_of_queue_timer_eq s _ c'
      (processOneReplenishmentOnCore_replenishQueueOnCore_eq s c scId now c') (by rw [hM]) (hP c')
  refine ⟨SystemState.releasePlace_objects_invExt _ c scId hI1,
    by rw [SystemState.releasePlace_machine, hM]; exact hT, fun c' => ?_⟩
  by_cases hcc : c = c'
  · subst hcc
    refine replenishOnCore_preserves_replenishmentPipelineOrderOnCore _ c scId (hP1 c) ?_
    intro t ht
    rw [hM]
    exact Nat.lt_of_le_of_lt hT (processOneReplenishmentOnCore_releaseKeyOf_gt s c scId now hI t ht)
  · exact replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne _ c c' scId hcc (hP1 c')

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
    (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hPipe : ∀ c', replenishmentPipelineOrderOnCore st c') :
    ∀ c', replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c) c' := by
  simp only [timerTickOnCorePrepared]
  refine processReplenishmentsDueOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ hInv
    (Nat.le_refl _) ?_
  intro c' pair hMem
  simp only [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore] at hMem
  exact hPipe c' pair hMem

/-- WS-ZA ZA6.3: the context of the thread current on core `c` holds no refill
released by now — the budget tick's re-placement of it then lands after now.
The drain leaves this true of every context it releases. -/
def currentRefillsFutureOnCore (s : SystemState) (c : CoreId) : Prop :=
  ∀ tid tcb scId sc, s.scheduler.currentOnCore c = some tid → s.getTcb? tid = some tcb →
    tcb.schedContextBinding.scId? = some scId → s.getSchedContext? scId = some sc →
    ∀ t, sc.releaseKey? = some t → t > s.machine.timer

/-- `timerTickOnCore_of`, with the budget arm told that its thread is current. -/
theorem timerTickOnCore_of_current {P : SystemState → Prop} (st : SystemState) (c : CoreId)
    (hPrep : P (timerTickOnCorePrepared st c))
    (hR : ∀ s, P s → P (handleRescheduleOnCoreState s c))
    (hS : ∀ s, P s → P (scheduleEffectiveOnCoreState s c))
    (hB : ∀ tid tcb (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb) st3 b,
      (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
      timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) → P st3) :
    P (timerTickOnCore st c) := by
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hb, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hb, h⟩ <;> rw [h]
  · exact rescheduleIfPendingOnCore_of _ c hPrep (hR _ hPrep)
  · exact rescheduleIfPendingOnCore_of _ c hPrep (hR _ hPrep)
  · exact hS _ (hB tid tcb hTcb st3 true hCur hb)
  · have h3 := hB tid tcb hTcb st3 false hCur hb
    exact rescheduleIfPendingOnCore_of _ c h3 (hR _ h3)

/-- The exhausted arm's re-placement keeps pipeline order: the charged context's
place is its earliest pending refill, which is in the future when its refills
were (`spentSchedContext_releaseKey_gt`). -/
private theorem exhausted_pipeline (st : SystemState) (c c' : CoreId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (hInv : st.objects.invExt) (hPipe : replenishmentPipelineOrderOnCore st c')
    (hP : 0 < sc.period.val) (hOld : ∀ t, sc.releaseKey? = some t → t > st.machine.timer) :
    replenishmentPipelineOrderOnCore (replenishOnCore (st.rewriteObject scId.toObjId
      (.schedContext (spentSchedContext sc st.machine.timer))
      (SystemState.rewriteAdmissible_schedContext hSc _)) c scId) c' := by
  have hPR := pipeline_frame_of_queue_timer_eq st (st.rewriteObject scId.toObjId
      (.schedContext (spentSchedContext sc st.machine.timer))
      (SystemState.rewriteAdmissible_schedContext hSc _)) c' rfl rfl hPipe
  by_cases hcc : c = c'
  · subst hcc
    refine replenishOnCore_preserves_replenishmentPipelineOrderOnCore _ c scId hPR ?_
    intro t ht
    obtain ⟨sc', hsc', hk⟩ := SystemState.releaseKeyOf_eq_some.mp ht
    have e : (st.rewriteObject scId.toObjId (.schedContext (spentSchedContext sc st.machine.timer))
        (SystemState.rewriteAdmissible_schedContext hSc _)).getSchedContext? scId =
        some (spentSchedContext sc st.machine.timer) := by
      unfold SystemState.getSchedContext?; rw [SystemState.rewriteObject_objects_self _ _ _ _ hInv]
    rw [e] at hsc'; cases hsc'
    exact spentSchedContext_releaseKey_gt sc _ hP hOld t hk
  · exact replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne _ c c' scId hcc hPR

/-- WS-SM SM5.I: the per-core budget tick preserves pipeline-order — the unchanged
branches frame the queue, and the bound-exhausted branch's insert (`now + period`)
is future because the SchedContext's `period` is positive. -/
theorem timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st' : SystemState) (b : Bool) (c' : CoreId)
    (hPipe : replenishmentPipelineOrderOnCore st c')
    (hInv : st.objects.invExt)
    (hPeriod : ∀ scId sc, st.getSchedContext? scId = some sc → 0 < sc.period.val)
    (hFuture : ∀ scId sc, tcb.schedContextBinding.scId? = some scId →
      st.getSchedContext? scId = some sc → ∀ t, sc.releaseKey? = some t → t > st.machine.timer)
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
            refine pipeline_frame_of_queue_timer_eq _ st' c' hQ
              (by rw [hM, replenishOnCore_machine]; rfl) ?_
            exact exhausted_pipeline st c c' scId sc hSc hInv hPipe (hPeriod scId sc hSc)
              (hFuture scId sc (by rw [hB]; rfl) hSc)
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
            refine pipeline_frame_of_queue_timer_eq _ st' c' hQ
              (by rw [hM, replenishOnCore_machine]; rfl) ?_
            exact exhausted_pipeline st c c' scId sc hSc hInv hPipe (hPeriod scId sc hSc)
              (hFuture scId sc (by rw [hB]; rfl) hSc)
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
    (c : CoreId) (c' : CoreId) (hInv : st.objects.invExt)
    (hPipe : ∀ c'', replenishmentPipelineOrderOnCore st c'')
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hFuture : currentRefillsFutureOnCore (timerTickOnCorePrepared st c) c) :
    replenishmentPipelineOrderOnCore (timerTickOnCore st c) c' := by
  have hPrep := timerTickOnCorePrepared_preserves_replenishmentPipelineOrderOnCore st c hInv hPipe
  have hInvP : (timerTickOnCorePrepared st c).objects.invExt :=
    processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv
  refine timerTickOnCore_of_current (P := fun s => ∀ c'', replenishmentPipelineOrderOnCore s c'')
    st c hPrep ?_ ?_ ?_ c'
  · intro s hs c''
    have hH := handleRescheduleSgiOnCore_eq_state s c
    exact pipeline_frame_of_queue_timer_eq _ _ c''
      (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c'' hH)
      (handleRescheduleSgiOnCore_machine_timer _ c _ hH) (hs c'')
  · intro s hs c''
    exact scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ c'' (hs c'')
      (scheduleEffectiveOnCore_eq_state s c)
  · intro tid tcb hTcb st3 b hCur hb c''
    exact timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ _ _ _ c''
      (hPrep c'') hInvP hPeriod (fun scId sc hB hSc => hFuture tid tcb scId sc hCur hTcb hB hSc) hb

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
    (hInv : ∀ c'', perCoreCbsInvariant st c'') (hObj : st.objects.invExt)
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hFuture : currentRefillsFutureOnCore (timerTickOnCorePrepared st c) c)
    (hAffinity : replenishQueueAffinityConsistentOnCore (timerTickOnCore st c) c') :
    perCoreCbsInvariant (timerTickOnCore st c) c' :=
  ⟨timerTickOnCore_preserves_replenishQueueValidOnCore st c c'
      (fun c'' => (hInv c'').1),
   timerTickOnCore_preserves_replenishmentPipelineOrderOnCore st c c' hObj
      (fun c'' => (hInv c'').2.1) hPeriod hFuture,
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

/-- The entries of a queue released by `now`. -/
private abbrev dueEntries (es : List (SchedContextId × Nat)) (now : Nat) :
    List (SchedContextId × Nat) :=
  es.filter fun e => decide (e.2 ≤ now)

/-- Taking the head off a queue holding it once leaves the rest. -/
private theorem filter_drop_head (e0 : SchedContextId × Nat) (es : List (SchedContextId × Nat))
    (hx : e0.1 ∉ es.map Prod.fst) :
    ((e0 :: es).filter fun (p : SchedContextId × Nat) => !(p.1 == e0.1)) = es := by
  rw [List.filter_cons, if_neg (by simp)]
  refine List.filter_eq_self.mpr fun e he => ?_
  have : e.1 ≠ e0.1 := fun h => hx (h ▸ List.mem_map_of_mem he)
  simpa using this

/-- An entry put in after `now` adds no due entry. -/
private theorem dueEntries_insertSorted (es : List (SchedContextId × Nat)) (x : SchedContextId)
    (t now : Nat) (ht : t > now) :
    (dueEntries (ReplenishQueue.insertSorted es x t) now).length = (dueEntries es now).length := by
  rw [SystemState.insertSorted_eq_split]
  unfold dueEntries
  rw [List.filter_append, List.filter_cons, if_neg (by simp; omega), ← List.filter_append,
    List.takeWhile_append_dropWhile]

/-- WS-ZA ZA6.3: **the drain empties its core of due refills** — run on a
refined, sorted queue holding at most `f` entries released by `now`, every
entry it leaves is released after `now`.  Each pass takes the head, which is
due (it is the queue's first entry, at its release time), and puts it back
behind every due entry or off the queue; when the head is not due, sortedness
carries the bound to the whole queue. -/
theorem drainDueOnCore_establishes (c : CoreId) (now : Nat) :
    ∀ f (st : SystemState), st.releaseQueueRefined → st.objects.invExt →
      replenishQueueValidOnCore st c →
      (dueEntries (st.scheduler.replenishQueueOnCore c).entries now).length ≤ f →
      ∀ e ∈ ((drainDueOnCore c now f st).scheduler.replenishQueueOnCore c).entries, e.2 > now
  | 0, st, _, _, _, hD => by
    intro e he
    have := List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp (Nat.le_zero.mp hD)) e he
    simp only [decide_eq_true_eq] at this
    omega
  | f + 1, st, hR, hI, hV, hD => by
    have hc := hR c
    unfold drainDueOnCore
    dsimp only
    split
    · rename_i h0
      intro e he
      exfalso
      have hch := hc.chain
      rw [h0] at hch
      have hmem : e.1 ∈ st.releaseIds c := List.mem_map_of_mem he
      cases hl : st.releaseIds c with
      | nil => rw [hl] at hmem; cases hmem
      | cons x r => rw [hl] at hch; exact ReleaseChain.code_ne_zero x hch.1.symm
    · rename_i h0
      obtain ⟨e0, es, hE⟩ : ∃ e0 es, (st.scheduler.replenishQueueOnCore c).entries = e0 :: es := by
        cases hE : (st.scheduler.replenishQueueOnCore c).entries with
        | nil =>
          exfalso
          have hch := hc.chain
          have : st.releaseIds c = [] := by simp [SystemState.releaseIds, hE]
          rw [this] at hch; exact h0 hch
        | cons e0 es => exact ⟨e0, es, rfl⟩
      have hIds : st.releaseIds c = e0.1 :: es.map Prod.fst := by simp [SystemState.releaseIds, hE]
      have hHead : ReleaseChain.decode (st.scheduler.releaseHeadOnCore c) = e0.1 := by
        have hch := hc.chain; rw [hIds] at hch; rw [hch.1, ReleaseChain.decode_code]
      have hAt : st.releaseAtOn c e0.1 = e0.2 := hc.at_eq e0 (by rw [hE]; exact List.mem_cons_self ..)
      have hnd := hc.nodup
      rw [hIds] at hnd
      have hx : e0.1 ∉ es.map Prod.fst := (List.nodup_cons.mp hnd).1
      rw [hHead]
      split
      · rename_i hle
        rw [hAt] at hle
        have hA := processOneReplenishmentOnCore_releaseStateAgree st c e0.1 now hI
        have hQ1 := hA.replenishQueueOnCore c
        have hR1 := hA.refined hR
        have hI1 := processOneReplenishmentOnCore_preserves_objects_invExt st c e0.1 now hI
        have hfree : (processOneReplenishmentOnCore st c e0.1 now).releaseFreeFor c e0.1 = true := by
          have hq : (processOneReplenishmentOnCore st c e0.1 now).releaseQueuedOn c e0.1 = true :=
            ((hR1 c).queued e0.1).mpr (by
              show e0.1 ∈ (SchedulerState.replenishQueueOnCore _ c).entries.map Prod.fst
              rw [hQ1, hE]; exact List.mem_cons_self ..)
          unfold SystemState.releaseFreeFor
          rw [SystemState.releaseCoreOf_of_queuedOn hq]; simp
        apply drainDueOnCore_establishes c now f
        · exact SystemState.releasePlace_refined hR1 c e0.1
        · exact SystemState.releasePlace_objects_invExt _ c e0.1 hI1
        · exact replenishOnCore_preserves_replenishQueueValidOnCore _ c e0.1
            (by unfold replenishQueueValidOnCore; rw [hQ1]; exact hV)
        · have hD' : (dueEntries es now).length ≤ f := by
            rw [hE] at hD; unfold dueEntries at hD
            rw [List.filter_cons, if_pos (by simpa using hle), List.length_cons] at hD
            show (es.filter fun e => decide (e.2 ≤ now)).length ≤ f
            omega
          rw [SystemState.releasePlace_replenishQueueOnCore_self hfree, hQ1]
          have hGt := processOneReplenishmentOnCore_releaseKeyOf_gt st c e0.1 now hI
          cases hk : (processOneReplenishmentOnCore st c e0.1 now).releaseKeyOf e0.1 with
          | none =>
            simp only [ReplenishQueue.remove, hE]
            rw [filter_drop_head e0 es hx]; exact hD'
          | some t =>
            simp only [ReplenishQueue.insert, ReplenishQueue.remove, hE]
            rw [filter_drop_head e0 es hx, dueEntries_insertSorted es e0.1 t now (hGt t hk)]
            exact hD'
      · rename_i hgt
        rw [hAt] at hgt
        intro e he
        rw [hE] at he
        rcases List.mem_cons.mp he with rfl | hm
        · omega
        · have hS := hV.1
          unfold replenishQueueSorted at hS
          rw [hE] at hS
          have := pairwiseSortedBy_tail_ge_head e0 es hS e hm
          omega

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
    (st : SystemState) (c : CoreId) (hRef : st.releaseQueueRefined) (hInv : st.objects.invExt)
    (hValid : replenishQueueValidOnCore st c)
    (hPeriod : ∀ scId sc, (timerTickOnCorePrepared st c).getSchedContext? scId = some sc →
      0 < sc.period.val)
    (hFuture : currentRefillsFutureOnCore (timerTickOnCorePrepared st c) c) :
    replenishmentPipelineOrderOnCore (timerTickOnCore st c) c := by
  have hPrepSelf : replenishmentPipelineOrderOnCore (timerTickOnCorePrepared st c) c := by
    intro pair hMem
    rw [timerTickOnCorePrepared_machine_eq]
    let st0 : SystemState := { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] }
    have hA : SystemState.releaseStateAgree st0 st := .of_objects_eq rfl rfl
    have hQ : st0.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c :=
      hA.replenishQueueOnCore c
    refine drainDueOnCore_establishes c st.machine.timer _ st0 (hA.refined hRef) hInv
      (by unfold replenishQueueValidOnCore; rw [hQ]; exact hValid) ?_ pair hMem
    rw [((hA.refined hRef) c).count]
    exact List.length_filter_le _ _
  have hInvP : (timerTickOnCorePrepared st c).objects.invExt :=
    processReplenishmentsDueOnCore_preserves_objects_invExt _ c _ hInv
  refine timerTickOnCore_of_current (P := fun s => replenishmentPipelineOrderOnCore s c) st c
    hPrepSelf ?_ ?_ ?_
  · intro s hs
    have hH := handleRescheduleSgiOnCore_eq_state s c
    exact pipeline_frame_of_queue_timer_eq _ _ c
      (handleRescheduleSgiOnCore_replenishQueueOnCore _ c _ c hH)
      (handleRescheduleSgiOnCore_machine_timer _ c _ hH) hs
  · intro s hs
    exact scheduleEffectiveOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ c hs
      (scheduleEffectiveOnCore_eq_state s c)
  · intro tid tcb hTcb st3 b hCur hb
    exact timerTickBudgetOnCore_preserves_replenishmentPipelineOrderOnCore _ c _ _ _ _ c
      hPrepSelf hInvP hPeriod (fun scId sc hB hSc => hFuture tid tcb scId sc hCur hTcb hB hSc) hb

/-- WS-SM (PR #880 round 4, the drain guarantee): a core's **committed run-loop
step** re-establishes strict pipeline order on its own queue — the release
queues travel across the clock advance (scheduler and store untouched), the
tick drains the due refills at the advanced clock, and the domain tick
preserves the result.  Instantiated at a remote core's own next PPI, this is
exactly what closes the due-now window `tickClockedState_bootCore_replenish_ge`
bounds. -/
theorem perCoreTimerTickStep_establishes_replenishmentPipelineOrderOnCore_self
    (st : SystemState) (coreId : UInt64) (h : coreId.toNat < numCores)
    (hRef : st.releaseQueueRefined) (hInv : st.objects.invExt)
    (hValid : replenishQueueValidOnCore st ⟨coreId.toNat, h⟩)
    (hPeriod : ∀ scId sc,
      (timerTickOnCorePrepared (tickClockedState st ⟨coreId.toNat, h⟩)
          ⟨coreId.toNat, h⟩).getSchedContext? scId = some sc → 0 < sc.period.val)
    (hFuture : currentRefillsFutureOnCore
      (timerTickOnCorePrepared (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩)
      ⟨coreId.toNat, h⟩) :
    replenishmentPipelineOrderOnCore (perCoreTimerTickStep st coreId).1 ⟨coreId.toNat, h⟩ := by
  rw [perCoreTimerTickStep_valid_core st coreId h]
  have hA : SystemState.releaseStateAgree (tickClockedState st ⟨coreId.toNat, h⟩) st :=
    .of_objects_eq (tickClockedState_objects _ _) (by rw [tickClockedState_scheduler])
  have hValid' : replenishQueueValidOnCore (tickClockedState st ⟨coreId.toNat, h⟩)
      ⟨coreId.toNat, h⟩ := by
    unfold replenishQueueValidOnCore; rw [hA.replenishQueueOnCore]; exact hValid
  have hSelf := timerTickOnCore_establishes_replenishmentPipelineOrderOnCore_self
    (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ (hA.refined hRef)
    (by rw [tickClockedState_objects]; exact hInv) hValid' hPeriod hFuture
  exact scheduleDomainOnCore_preserves_replenishmentPipelineOrderOnCore _
    ⟨coreId.toNat, h⟩ _ ⟨coreId.toNat, h⟩ hSelf (scheduleDomainOnCore_eq_state _ _)

end SeLe4n.Kernel
