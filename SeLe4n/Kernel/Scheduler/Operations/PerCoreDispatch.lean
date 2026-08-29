-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle

/-!
# WS-SM SM5.E — Per-core idle-aware dispatcher (the SM5.I dispatch-loop seed)

Surface theorems for the production per-core idle dispatch.  **Post-fold (review #4
closure, v0.31.49)** the idle dispatch lives *inside* `scheduleEffectiveOnCore`'s
`none` branch (`idleFallbackOnCore`, `Scheduler/Operations/Core.lean`) — so the live
per-core tick / domain paths (`timerTickOnCore` / `scheduleDomainOnCore`, which call
`scheduleEffectiveOnCore`) reach core `c`'s **idle thread** on the running kernel,
instead of leaving the core at `current = none`.  `scheduleOrIdleOnCore` is now
*definitionally* `scheduleEffectiveOnCore`; its soundness is established once on
`scheduleEffectiveOnCore` (PerCoreTimerTick §7, via the `idleFallbackOnCore_*`
case-analysis lemmas) so the mature SM5.D / `timerTickOnCore` proof base is untouched.

* **Headline (`scheduleOrIdleOnCore_runs_idle`)** — when the budget-aware selector
  goes idle (`chooseThreadEffectiveOnCore = .ok none`) and core `c`'s idle thread is
  *dispatchable* on the context-saved state (installed + in-domain + affinity-admits),
  the result has `current = some (idleThreadId c)`: idle is genuinely dispatched in a
  production transition.
* **Live-tick witness (`scheduleDomainOnCore_runs_idle`)** — the same idle dispatch
  on the live per-core domain-tick path (a domain boundary in single-domain mode).
* **Soundness (thin aliases to the `scheduleEffectiveOnCore_*` establishment
  theorems)** — the result satisfies `currentThreadValidOnCore`,
  `queueCurrentConsistentOnCore`, `currentThreadInActiveDomainOnCore`,
  `runnableThreadsAreTCBsOnCore`, `runQueueOnCoreWellFormed`, and `objects.invExt`.
* **Strong no-starvation** — idle is dispatched only when no in-domain
  budget-eligible thread is runnable (never preempts a runnable user thread of any
  priority).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Headline: idle is dispatched in a production transition
-- ============================================================================

/-- WS-SM SM5.E (the headline — *idle is dispatched in production*): when the
budget-aware selector finds nothing runnable on core `c`
(`chooseThreadEffectiveOnCore st c = .ok none`) and core `c`'s idle thread is
dispatchable on the context-saved state (installed + in-domain + admissible), the
folded idle-aware `scheduleEffectiveOnCore` runs the idle thread — the result has
`current = some (idleThreadId c)`.  This is the live production realisation of plan
§4.3 ("idle is always a fallback"): a core with nothing else to do runs its idle
TCB rather than sitting at `current = none`.

Post-fold, `scheduleOrIdleOnCore` is the SM5.E name for `scheduleEffectiveOnCore`
(definitionally equal — the idle dispatch lives in `scheduleEffectiveOnCore`'s
`none` branch via `idleFallbackOnCore`), so the live per-core tick / domain paths
(`timerTickOnCore` / `scheduleDomainOnCore`, which call `scheduleEffectiveOnCore`)
reach the idle thread on the running kernel. -/
theorem scheduleOrIdleOnCore_runs_idle (st : SystemState) (c : CoreId) (st'' : SystemState)
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none)
    (hDisp : idleDispatchableOnCore (saveOutgoingContextOnCore st c) c = true)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    st''.scheduler.currentOnCore c = some (idleThreadId c) := by
  unfold scheduleOrIdleOnCore scheduleEffectiveOnCore at hStep
  rw [hChoose] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  unfold idleFallbackOnCore
  rw [if_pos hDisp]
  exact dispatchIdleOnCore_currentOnCore _ c

-- ============================================================================
-- §2  Soundness: the idle-aware dispatcher preserves the per-core invariants.
--     Post-fold (`scheduleOrIdleOnCore = scheduleEffectiveOnCore`), the idle
--     dispatch is folded into `scheduleEffectiveOnCore`'s `none` branch
--     (`idleFallbackOnCore`), so each per-core invariant is *established once* on
--     `scheduleEffectiveOnCore` (PerCoreTimerTick §7 + the `idleFallbackOnCore_*`
--     lemmas) and surfaced here under the SM5.E `scheduleOrIdleOnCore` name.  The
--     hypotheses are accepted by defeq (`scheduleOrIdleOnCore st c` reduces to
--     `scheduleEffectiveOnCore st c`).
-- ============================================================================

/-- WS-SM SM5.E (soundness): `scheduleOrIdleOnCore` preserves the object-store
RobinHood invariant — the idle dispatch touches only the scheduler + `machine.regs`. -/
theorem scheduleOrIdleOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') : st''.objects.invExt :=
  scheduleEffectiveOnCore_preserves_objects_invExt st c st'' hInv hStep

/-- WS-SM SM5.E (soundness): `scheduleOrIdleOnCore` establishes core `c`'s
current-thread validity — the idle case resolves to the (installed) idle TCB. -/
theorem scheduleOrIdleOnCore_establishes_currentThreadValidOnCore (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') : currentThreadValidOnCore st'' c :=
  scheduleEffectiveOnCore_establishes_currentThreadValidOnCore st c st'' hInv hStep

/-- WS-SM SM5.E (soundness, dequeue-on-dispatch): `scheduleOrIdleOnCore`
establishes that core `c`'s current thread is not in its run queue — the idle case
dequeues the idle thread before making it current (`RunQueue.remove`). -/
theorem scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    queueCurrentConsistentOnCore st''.scheduler c :=
  scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore st c st'' hStep

/-- WS-SM SM5.E (soundness): `scheduleOrIdleOnCore` preserves core `c`'s run-queue
well-formedness — the idle dispatch only `remove`s the idle thread. -/
theorem scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed (st : SystemState) (c : CoreId)
    (st'' : SystemState) (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    (st''.scheduler.runQueueOnCore c).wellFormed :=
  scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed st c st'' hwf hStep

/-- WS-SM SM5.E (soundness, parity with `scheduleEffectiveOnCore`): the idle-aware
dispatcher establishes that core `c`'s current thread is in its active domain — the
idle case dispatches a thread whose domain matches (the `idleDispatchableOnCore`
gate checks exactly this).  Closes the parity gap: the dispatcher is as sound as
the selector it folds idle into. -/
theorem scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore (st : SystemState)
    (c : CoreId) (st'' : SystemState) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    currentThreadInActiveDomainOnCore st'' c :=
  scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore st c st'' hInv hStep

/-- WS-SM SM5.E (soundness, parity with `scheduleEffectiveOnCore`): the idle-aware
dispatcher preserves "every runnable thread resolves to a TCB" — the idle case only
`remove`s the idle thread from the run queue (a subset of the pre run queue). -/
theorem scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c : CoreId) (st'' : SystemState) (hInv : st.objects.invExt)
    (h : runnableThreadsAreTCBsOnCore st c)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    runnableThreadsAreTCBsOnCore st'' c :=
  scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore st c st'' hInv hStep h

-- ============================================================================
-- §3  Strong no-starvation: the dispatcher runs idle only when nothing eligible
-- ============================================================================

/-- WS-SM SM5.E (no-starvation foundation): `scheduleEffectiveOnCore` yields a
state with `current = none` on core `c` **only** when the budget-aware selector
found nothing dispatchable (`chooseThreadEffectiveOnCore` returned `.ok none`).
Its `some` branch always commits `current = some tid`, so a `none` result forces
the idle (selector-found-nothing) branch. -/
theorem scheduleEffectiveOnCore_currentNone_imp_chooseEffectiveNone (st : SystemState)
    (c : CoreId) (st' : SystemState)
    (hEff : scheduleEffectiveOnCore st c = .ok st')
    (hcur : st'.scheduler.currentOnCore c = none) :
    chooseThreadEffectiveOnCore st c = .ok none := by
  unfold scheduleEffectiveOnCore at hEff
  split at hEff
  · exact absurd hEff (by simp)
  · rename_i heq; exact heq
  · exfalso
    split at hEff
    · split at hEff
      · simp only [Except.ok.injEq] at hEff
        subst hEff
        rw [SchedulerState.setCurrentOnCore_currentOnCore_self] at hcur
        exact absurd hcur (by simp)
      · exact absurd hEff (by simp)
    · exact absurd hEff (by simp)

/-- WS-SM SM5.E (the strong no-starvation property for the production dispatcher,
addressing the "idle below same-priority user threads" concern): the precondition
under which the folded dispatcher reaches its idle path is exactly
`chooseThreadEffectiveOnCore st c = .ok none` (the budget-aware selector found
nothing dispatchable — see the headline `scheduleOrIdleOnCore_runs_idle`).  Under
that precondition **every** thread in core `c`'s run queue is either out of the
active domain or out of budget.

Whether the dispatcher then *runs* the idle thread (`current = some (idleThreadId
c)`, idle installed + dispatchable) or falls back to the legacy `current = none`
(no idle installed), it does so **only when no in-domain, budget-eligible thread is
runnable at all** — so it never preempts a runnable user thread of *any* priority,
including priority `0`.  This is strictly stronger than `idleThread_no_starvation`
(which only rules out *higher*-priority threads).  Unlike the run-queue-resident
form (`enqueueIdleThreadOnCore` + `chooseThreadOnCore`, where idle is a priority-`0`
peer and FIFO could pick it over a same-priority-`0` user thread), the production
dispatcher never makes that mistake. -/
theorem scheduleOrIdleOnCore_idle_starves_no_eligible_thread (st : SystemState) (c : CoreId)
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none) :
    ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
      st.getTcb? tid = some tcb →
      ¬(tcb.domain = st.scheduler.activeDomainOnCore c ∧ hasSufficientBudget st tcb = true) :=
  chooseThreadEffectiveOnCore_none_no_eligible st c hChoose

-- ============================================================================
-- §4  The folded idle dispatch is reachable on the live per-core tick path
-- ============================================================================

/-- WS-SM SM5.E (the live-wiring witness — review #4 closure): the folded idle
dispatch is reachable on the **live per-core domain-tick path**.  At a domain
boundary (`domainTimeRemainingOnCore c ≤ 1`) in single-domain mode
(`domainSchedule = []`, the RPi5 v1.0.0 configuration), `scheduleDomainOnCore`
re-dispatches via `scheduleEffectiveOnCore`; when nothing is budget-eligible and
core `c`'s idle thread is dispatchable, the live domain tick runs the idle thread
(`current = some (idleThreadId c)`).  This makes "the idle thread runs on the
live kernel" a theorem about a production transition the timer drives, not just
about the standalone dispatcher.

The `hCur` precondition (`currentOnCore c = none`) states the scenario honestly:
idle adoption is the *nothing-is-running-and-nothing-is-eligible* boundary.  With
a thread current, the boundary prologue (`singleDomainBoundaryPrep`) re-enqueues
it, and the selection outcome is `chooseThreadEffectiveOnCore`'s to decide on the
prepped queue — that path is covered by the establishment lemmas, not this
witness.  With `current = none` the prologue is the identity
(`singleDomainBoundaryPrep_of_current_none`), so the selector and dispatchability
hypotheses transport unchanged to the re-dispatch. -/
theorem scheduleDomainOnCore_runs_idle (st : SystemState) (c : CoreId) (st'' : SystemState)
    (hBoundary : st.scheduler.domainTimeRemainingOnCore c ≤ 1)
    (hSched : st.scheduler.domainSchedule = [])
    (hCur : st.scheduler.currentOnCore c = none)
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none)
    (hDisp : idleDispatchableOnCore (saveOutgoingContextOnCore st c) c = true)
    (hStep : scheduleDomainOnCore st c = .ok st'') :
    st''.scheduler.currentOnCore c = some (idleThreadId c) := by
  unfold scheduleDomainOnCore at hStep
  rw [if_pos hBoundary, hSched] at hStep
  rw [singleDomainBoundaryPrep_of_current_none st c hCur] at hStep
  exact scheduleOrIdleOnCore_runs_idle st c st'' hChoose hDisp hStep

end SeLe4n.Kernel
