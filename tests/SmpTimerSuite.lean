-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.D — Per-core timer tick test suite

Surface anchors + elaboration-time theorem applications + the SM5.D.10 runtime
tick scenarios for the per-core timer tick (`timerTickOnCore` and its SM5.D.4
CBS-replenishment / SM5.D.6 domain-rotation / SM5.D.5 budget-tick components).
Runnable as `lake exe smp_timer_suite`.
-/

namespace SeLe4n.Testing.SmpTimer

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.D public symbol resolves
-- ============================================================================

-- SM5.D.2/.4/.5/.6/.9 production transitions (Scheduler.Operations.Core).
#check @timerTickOnCore
#check @timerTickBudgetOnCore
#check @processReplenishmentsDueOnCore
#check @processOneReplenishmentOnCore
#check @replenishWakeTarget
#check @decrementDomainTimeOnCore
#check @scheduleEffectiveOnCore
#check @saveOutgoingContextOnCore
#check @switchDomainOnCore
#check @scheduleDomainOnCore

-- SM5.D.3 cross-domain lock-set (+ replenish-queue lock domain).
#check @ReplenishQueueLockId
#check @ReplenishQueueLockId.replenishQueueLockLevel
#check @SchedLockId.object_lt_replenishQueue
#check @SchedLockId.runQueue_lt_replenishQueue
#check @timerTickOnCoreLockSet
#check @timerTickOnCoreLockSet_length
#check @timerTickOnCoreLockSet_write_only
#check @timerTickOnCoreLockSet_contains_objStore_write
#check @timerTickOnCoreLockSet_contains_runQueue_write
#check @timerTickOnCoreLockSet_contains_replenishQueue_write
#check @timerTickOnCoreLockSet_keys_nodup
#check @timerTickOnCoreLockSet_pairwise_le
#check @timerTickOnCoreLockSet_size_le_maxLockSetSize

-- SM5.D.6 domain accounting (audit-pass-2: pure non-boundary decrement; rotation
-- is the separate atomic scheduleDomainOnCore).
#check @decrementDomainTimeOnCore_decrements
#check @decrementDomainTimeOnCore_activeDomainOnCore
#check @decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne
#check @decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore

-- SM5.D.4 CBS replenishment + cross-core wake.
#check @cbsReplenish_can_wake_remote_core
#check @runningOnSomeCore
#check @processOneReplenishmentOnCore_local_no_sgi
#check @processOneReplenishmentOnCore_no_sgi_if_no_target
#check @processOneReplenishmentOnCore_preserves_objects_invExt
#check @processReplenishmentsDueOnCore_preserves_objects_invExt
#check @processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed
#check @processReplenishmentsDueOnCore_machine_eq

-- SM5.D.5 budget tick (+ IPC-timeout objects preservation chain).
#check @timerTickBudgetOnCore_unbound_not_preempted
#check @timerTickBudgetOnCore_unbound_preempts
#check @timerTickBudgetOnCore_preserves_objects_invExt
#check @timeoutThread_preserves_objects_invExt
#check @timeoutBlockedThreads_preserves_objects_invExt
#check @revertPriorityInheritance_preserves_objects_invExt
#check @scheduleEffectiveOnCore_preserves_objects_invExt

-- SM5.D.2 headline theorems + preservation.
#check @timerTickOnCore_idle
#check @timerTickOnCore_advances_per_core
#check @timerTickOnCore_clears_lastTimeoutErrors
#check @timerTickOnCore_preempts_local
#check @timerTickOnCore_preserves_objects_invExt
-- audit-pass-2 capstone: the budget-only tick preserves currentThreadInActiveDomain.
#check @timerTickOnCore_preserves_currentThreadInActiveDomainOnCore
#check @scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore
#check @timerTickOnCore_eq_prepared
#check @timerTickOnCorePrepared
#check @timerTickOnCorePreDomain

-- SM5.D.8 decidability witnesses.
#check @timerTickOnCoreSucceeds
#check @timerTickOnCoreEmitsSgi
#check @timerTickBudgetOnCorePreempts

-- SM5.I per-core run-loop step (PerCoreRunLoop) — the verified, FFI-free decision
-- core the (HAL-linked) per-core timer entry drives.  The `@[export]`
-- `perCoreTimerTickEntry` itself references the `ffiSendSgi` extern (via
-- `fireCrossCoreSgis`), so it is NOT imported here (a test exe does not link the
-- HAL); its signature + `perCoreTimerTickEntry_def` body-shape marker are anchored
-- in `test_tier3_invariant_surface.sh` (elaboration-only, no link).
#check @perCoreTimerTickStep
#check @perCoreTimerTickStep_invalid_core
#check @perCoreTimerTickStep_ok
#check @perCoreTimerTickStep_error
#check @perCoreTimerTickStep_domain_error
#check @perCoreTimerTickStep_sgis_eq_tick
#check @perCoreTimerTickStep_preserves_objects_invExt
#check @perCoreTimerTickStep_ok_currentThreadValidOnCore
#check @tickClockedState
#check @tickClockedState_objects
#check @tickClockedState_scheduler
#check @tickClockedState_bootCore_timer
#check @tickClockedState_nonBoot
-- Commit-coupled shadow clock (PR #880 follow-up): the flagged step the live
-- entry drives — the clock-advance report is definitionally the committed
-- state's machine.timer delta, so the HAL TICK_COUNT shadow moves iff the
-- model clock moved (fail-closed arms report false).
#check @perCoreTimerTickStepWithClockAdvance
#check @perCoreTimerTickStepWithClockAdvance_state
#check @perCoreTimerTickStepWithClockAdvance_sgis
#check @perCoreTimerTickStepWithClockAdvance_flag_def
#check @perCoreTimerTickStepWithClockAdvance_flag_iff
#check @perCoreTimerTickStepWithClockAdvance_flag_invalid_core
#check @perCoreTimerTickStepWithClockAdvance_flag_error
#check @perCoreTimerTickStepWithClockAdvance_flag_domain_error
#check @scheduleDomainOnCore_preserves_currentThreadValidOnCore

-- §4b SM5.D.6 full per-core domain re-dispatch (switchDomainOnCore / scheduleDomainOnCore).
#check @switchDomainOnCore_singleDomain_noop
#check @switchDomainOnCore_preserves_objects_invExt
#check @switchDomainOnCore_sets_currentOnCore_none
#check @switchDomainOnCore_rotates
#check @scheduleDomainOnCore_decrements
#check @scheduleDomainOnCore_preserves_objects_invExt
-- Single-domain mode is inert (PR #880 review rounds 2 + 4): with no domain
-- schedule there is no boundary — nothing decrements, rotates or
-- re-dispatches, so the domain layer provably cannot perturb the budget
-- tick's time-slice scheduling on the RPi5 v1.0.0 default.
#check @scheduleDomainOnCore_singleDomain_inert

-- §7 SM5.D.5/.6 per-core invariant preservation (B1/B2/B3).
#check @decrementDomainTimeOnCore_preserves_currentThreadValidOnCore
#check @decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore
#check @decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed
#check @saveOutgoingContextOnCore_scheduler_eq
#check @saveOutgoingContextOnCore_getTcb?_isSome
#check @scheduleEffectiveOnCore_objects_eq
#check @scheduleEffectiveOnCore_getTcb?_isSome
#check @scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed
#check @scheduleEffectiveOnCore_establishes_currentThreadValidOnCore
#check @scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore
#check @scheduleEffectiveOnCore_runQueue_toList_subset
#check @scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @timerTickBudgetOnCore_notPreempted_scheduler_eq
#check @timerTickBudgetOnCore_notPreempted_getTcb?_tid
#check @timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed
#check @timerTickOnCore_preserves_currentThreadValidOnCore
#check @timerTickOnCorePrepared_runQueueOnCore_wellFormed
#check @timerTickOnCore_preserves_runQueueOnCoreWellFormed
#check @timerTickOnCore_preserves_queueCurrentConsistentOnCore

-- ============================================================================
-- §2  Elaboration-time examples: apply each headline theorem to verified inputs
-- ============================================================================

/-- SM5.D.2 / plan §6.1: the per-core tick advances core `c`'s state without
advancing the global timer (idle path). -/
example (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hNoWake : (timerTickOnCorePrepared st c).2.2 = false)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) : st'.machine = st.machine :=
  timerTickOnCore_advances_per_core st c st' sgis hCur hNoWake hStep

/-- SM5.D.4 / plan §6.1: a remote-targeted CBS replenish (of a thread not running
on any core — audit-pass-2 / Codex-P2 guard) emits a cross-core SGI. -/
example (st : SystemState) (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hTcb : (refillSchedContext st scId now).getTcb? tid = some tcb)
    (hNotRunning : runningOnSomeCore (refillSchedContext st scId now) tid = false)
    (hRemote : determineTargetCore (refillSchedContext st scId now) tid ≠ execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2.1
      = some (determineTargetCore (refillSchedContext st scId now) tid, SgiKind.reschedule) :=
  cbsReplenish_can_wake_remote_core st execCore scId now tid tcb hTarget hTcb hNotRunning hRemote

/-- SM5.D.5 / plan §6.1: budget-tick preemption re-dispatches via the budget-aware
reschedule. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 st' : SystemState)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid)
    (hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb)
    (hBud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, true))
    (hSched : scheduleEffectiveOnCore st3 c = .ok st') :
    timerTickOnCore st c = .ok (st', (timerTickOnCorePrepared st c).2.1) :=
  timerTickOnCore_preempts_local st c tid tcb st3 st' hCur hTcb hBud hSched

/-- SM5.D.6 (audit-pass-2): domain rotation is the separate atomic `scheduleDomainOnCore`
(via `switchDomainOnCore`), NOT the tick — so a running thread never outlives its
domain.  `switchDomainOnCore_rotates` is the rotation witness. -/
example (st : SystemState) (c : CoreId) (entry : DomainScheduleEntry) (st' : SystemState)
    (hLookup : st.scheduler.domainSchedule[((st.scheduler.domainScheduleIndexOnCore c) + 1) %
        st.scheduler.domainSchedule.length]? = some entry)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hStep : switchDomainOnCore st c = .ok st') :
    st'.scheduler.activeDomainOnCore c = DomainScheduleEntry.domain entry :=
  switchDomainOnCore_rotates st c st' entry hLookup hSched hStep

/-- SM5.D.6 (audit-pass-2 capstone): the per-core timer tick PRESERVES
`currentThreadInActiveDomainOnCore` (it does no in-tick rotation), given the
replenishment preserves it. -/
example (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hInv : st.objects.invExt)
    (hPrepDom : currentThreadInActiveDomainOnCore (timerTickOnCorePrepared st c).1 c)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    currentThreadInActiveDomainOnCore st' c :=
  timerTickOnCore_preserves_currentThreadInActiveDomainOnCore st c st' sgis hInv hPrepDom hStep

/-- SM5.D.2 (preservation): the tick preserves the object-store invariant. -/
example (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hInv : st.objects.invExt) (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    st'.objects.invExt :=
  timerTickOnCore_preserves_objects_invExt st c st' sgis hInv hStep

/-- SM5.D.3 (plan §4.4): the tick lock-set acquires object < run-queue < replenish-queue. -/
example (c : CoreId) :
    SchedLockId.runQueue (⟨c⟩ : RunQueueLockId)
      < SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
  SchedLockId.runQueue_lt_replenishQueue _ _

/-- SM5.D.5/.6 (B1): the per-core tick preserves per-core current-thread validity
UNCONDITIONALLY (idle / not-preempted / preempted all discharge). -/
example (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hInv : st.objects.invExt) (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    currentThreadValidOnCore st' c :=
  timerTickOnCore_preserves_currentThreadValidOnCore st c st' sgis hInv hStep

/-- SM5.D.5/.6 (B2): the per-core tick preserves per-core run-queue well-formedness,
given the budget-tick discharge `hBudgetRqWf` (unconditional on clean paths via
`timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed`; the
bound-budget-exhausted re-enqueue is the SM5.F tracked gap). -/
example (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hBudgetRqWf : ∀ tid tcb st3 b,
       (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid →
       (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb →
       timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, b) →
       (st3.scheduler.runQueueOnCore c).wellFormed)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) :
    (st'.scheduler.runQueueOnCore c).wellFormed :=
  timerTickOnCore_preserves_runQueueOnCoreWellFormed st c st' sgis hwf hBudgetRqWf hStep

/-- SM5.D.6: a successful per-core domain switch (non-empty schedule) clears the
current thread on core `c`. -/
example (st : SystemState) (c : CoreId) (st' : SystemState)
    (hStep : switchDomainOnCore st c = .ok st')
    (hSched : st.scheduler.domainSchedule ≠ []) :
    st'.scheduler.currentOnCore c = none :=
  switchDomainOnCore_sets_currentOnCore_none st c st' hStep hSched

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.D.10 per-core tick scenarios
-- ============================================================================

/-- Minimal test TCB at `tid`, priority `prio`, scheduling domain `dom`. -/
private def mkTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

private def core1 : CoreId := ⟨1, by decide⟩

/-- An unbound thread with an explicit time-slice (for the SM5.D.5 budget tick). -/
private def mkUnboundTcb (ts : Nat) : TCB :=
  { mkTcb 300 10 0 with schedContextBinding := .unbound, timeSlice := ts }

/-- A freshly-booted (idle) state: no current thread on any core, empty run /
replenish queues, single-domain mode, domain time = 5. -/
private def stIdle : SystemState := BootstrapBuilder.empty.build

/-- Two-entry domain schedule for the SM5.D.6 rotation scenario. -/
private def dom0 : DomainScheduleEntry := { domain := ⟨0⟩, length := 5 }
private def dom1 : DomainScheduleEntry := { domain := ⟨1⟩, length := 3 }

/-- A state on the boot core's last domain tick (`domainTimeRemaining = 1`) with a
two-entry domain schedule, so `switchDomainOnCore` rotates to `dom1`. -/
private def stDomain : SystemState :=
  let st := BootstrapBuilder.empty.build
  { st with scheduler :=
      ({ st.scheduler with domainSchedule := [dom0, dom1] }).setDomainTimeRemainingOnCore bootCoreId 1 }

private def budgetPreempts (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) : Bool :=
  match timerTickBudgetOnCore st c tid tcb with
  | .ok (_, b) => b
  | .error _ => false

private def tickOk (st : SystemState) (c : CoreId) : Bool :=
  match timerTickOnCore st c with
  | .ok _ => true
  | .error _ => false

private def tickMachineTimer (st : SystemState) (c : CoreId) : Option Nat :=
  match timerTickOnCore st c with
  | .ok (s, _) => some s.machine.timer
  | .error _ => none

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  ✓ {name}"
  else
    IO.eprintln s!"  ✗ FAIL: {name}"
    throw (IO.userError s!"assertion failed: {name}")

/-- §3.1 SM5.D.3: the timer-tick lock-set is the 3-lock object/run-queue/
replenish-queue write set in plan §4.4 ascending order. -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.1 SM5.D.3 tick lock-set ---"
  assertBool "tick lock-set has exactly 3 locks"
    ((timerTickOnCoreLockSet bootCoreId).length == 3)
  assertBool "tick lock-set contains the object-store write lock"
    ((timerTickOnCoreLockSet bootCoreId).contains (SchedLockId.object schedObjStoreLockId, .write))
  assertBool "tick lock-set contains the run-queue write lock"
    ((timerTickOnCoreLockSet bootCoreId).contains (SchedLockId.runQueue ⟨bootCoreId⟩, .write))
  assertBool "tick lock-set contains the replenish-queue write lock"
    ((timerTickOnCoreLockSet bootCoreId).contains (SchedLockId.replenishQueue ⟨bootCoreId⟩, .write))
  assertBool "tick lock-set is write-only (no read locks)"
    ((timerTickOnCoreLockSet bootCoreId).all (fun p => p.2 == .write))
  assertBool "tick lock-set keys are duplicate-free"
    (decide (((timerTickOnCoreLockSet bootCoreId).map (·.1)).Nodup))

/-- §3.2 SM5.D.7: the tick is in the bounded-WCRT class (lock-set size ≤ 8). -/
private def runWcrtChecks : IO Unit := do
  IO.println "--- §3.2 SM5.D.7 WCRT-bounded tick ---"
  assertBool "tick lock-set size ≤ maxLockSetSize (8)"
    (decide ((timerTickOnCoreLockSet bootCoreId).length ≤ 8))
  assertBool "object-domain locks acquired before run-queue locks (level 9 < 10)"
    (decide (RunQueueLockId.runQueueLockLevel < ReplenishQueueLockId.replenishQueueLockLevel))

/-- §3.3 SM5.D.6: a non-expired domain time decrements by one. -/
private def runDomainDecrementChecks : IO Unit := do
  IO.println "--- §3.3 SM5.D.6 domain-time decrement ---"
  -- stIdle's boot-core domain time is 5 (> 1): decrement → 4.
  assertBool "idle boot-core domain time starts at 5"
    (stIdle.scheduler.domainTimeRemainingOnCore bootCoreId == 5)
  assertBool "decrementDomainTimeOnCore decrements 5 → 4"
    ((decrementDomainTimeOnCore stIdle bootCoreId).scheduler.domainTimeRemainingOnCore bootCoreId == 4)
  assertBool "decrement leaves the active domain unchanged (no rotation when not expired)"
    ((decrementDomainTimeOnCore stIdle bootCoreId).scheduler.activeDomainOnCore bootCoreId
      == stIdle.scheduler.activeDomainOnCore bootCoreId)

/-- §3.4 SM5.D.6 (audit-pass-2): an expired domain time rotates to the next schedule
entry — via the **atomic** `switchDomainOnCore` (rotation + re-dispatch), NOT the
timer tick.  (`decrementDomainTimeOnCore` is now the pure non-boundary decrement.) -/
private def runDomainRotateChecks : IO Unit := do
  IO.println "--- §3.4 SM5.D.6 domain rotation (switchDomainOnCore) ---"
  assertBool "stDomain boot-core domain time is at its last tick (1)"
    (stDomain.scheduler.domainTimeRemainingOnCore bootCoreId == 1)
  assertBool "switchDomainOnCore rotates active domain to dom1 (index 0 → 1)"
    (match switchDomainOnCore stDomain bootCoreId with
     | .ok st' => st'.scheduler.activeDomainOnCore bootCoreId == dom1.domain
     | .error _ => false)
  assertBool "rotation resets domain time to dom1.length (3)"
    (match switchDomainOnCore stDomain bootCoreId with
     | .ok st' => st'.scheduler.domainTimeRemainingOnCore bootCoreId == 3
     | .error _ => false)
  assertBool "rotation advances the schedule index to 1"
    (match switchDomainOnCore stDomain bootCoreId with
     | .ok st' => st'.scheduler.domainScheduleIndexOnCore bootCoreId == 1
     | .error _ => false)
  -- a sibling core (core 1) is unaffected by the boot core's rotation.
  assertBool "domain rotation is core-local (core 1 active domain unchanged)"
    (match switchDomainOnCore stDomain bootCoreId with
     | .ok st' => st'.scheduler.activeDomainOnCore core1 == stDomain.scheduler.activeDomainOnCore core1
     | .error _ => false)
  -- audit-pass-2: the pure decrement does NOT rotate (the in-tick domain step was retired).
  assertBool "decrementDomainTimeOnCore does NOT rotate (active domain unchanged)"
    ((decrementDomainTimeOnCore stDomain bootCoreId).scheduler.activeDomainOnCore bootCoreId
      == stDomain.scheduler.activeDomainOnCore bootCoreId)

/-- §3.5 SM5.D.5: per-core budget-tick time-slice preemption. -/
private def runBudgetPreemptChecks : IO Unit := do
  IO.println "--- §3.5 SM5.D.5 budget-tick preemption ---"
  let tid := ThreadId.ofNat 300
  assertBool "unbound thread with expired time-slice (1) IS preempted"
    (budgetPreempts stIdle bootCoreId tid (mkUnboundTcb 1))
  assertBool "unbound thread with running time-slice (5) is NOT preempted"
    (! budgetPreempts stIdle bootCoreId tid (mkUnboundTcb 5))
  -- the decidable predicate agrees.
  assertBool "timerTickBudgetOnCorePreempts decides the expired case true"
    (decide (timerTickBudgetOnCorePreempts stIdle bootCoreId tid (mkUnboundTcb 1)))
  assertBool "timerTickBudgetOnCorePreempts decides the running case false"
    (! decide (timerTickBudgetOnCorePreempts stIdle bootCoreId tid (mkUnboundTcb 5)))
  -- the budget tick reads but does not advance the machine timer.
  assertBool "budget tick does not advance machine.timer"
    (match timerTickBudgetOnCore stIdle bootCoreId tid (mkUnboundTcb 5) with
     | .ok (s, _) => s.machine.timer == stIdle.machine.timer
     | .error _ => false)

/-- §3.6 SM5.D.2 / .9: the idle tick succeeds, preserves the global timer, and
clears the timeout-error diagnostic. -/
private def runIdleTickChecks : IO Unit := do
  IO.println "--- §3.6 SM5.D.2/.9 idle tick ---"
  assertBool "idle tick succeeds (returns .ok)"
    (tickOk stIdle bootCoreId)
  assertBool "idle tick does not advance the global machine timer"
    (tickMachineTimer stIdle bootCoreId == some stIdle.machine.timer)
  assertBool "timerTickOnCoreSucceeds decides the idle tick succeeds"
    (decide (timerTickOnCoreSucceeds stIdle bootCoreId))
  -- the prepared state has the boot core's lastTimeoutErrors cleared.
  assertBool "the prepared state clears core's lastTimeoutErrors (SM5.D.9)"
    ((timerTickOnCorePrepared stIdle bootCoreId).1.scheduler.lastTimeoutErrorsOnCore bootCoreId == [])
  -- the idle tick result is exactly the prepared state.
  assertBool "idle tick result is the prepared state"
    (match timerTickOnCore stIdle bootCoreId with
     | .ok r => r.1.scheduler.currentOnCore bootCoreId == none
     | .error _ => false)

/-- §3.7 SM5.D.4: a replenishment with no wake target emits no cross-core SGI. -/
private def runReplenishChecks : IO Unit := do
  IO.println "--- §3.7 SM5.D.4 CBS replenishment ---"
  -- On the idle state, there is no SchedContext at scId 99, so `replenishWakeTarget`
  -- is `none` and `processOneReplenishmentOnCore` emits no SGI.
  let scId : SeLe4n.SchedContextId := ⟨99⟩
  assertBool "no SchedContext ⇒ no wake target"
    (replenishWakeTarget stIdle (refillSchedContext stIdle scId 0) scId == none)
  assertBool "no wake target ⇒ no cross-core SGI"
    ((processOneReplenishmentOnCore stIdle bootCoreId scId 0).2.1 == none)
  assertBool "no wake target ⇒ no local-wake bit either"
    ((processOneReplenishmentOnCore stIdle bootCoreId scId 0).2.2 == false)
  -- the replenishment leaves the boot run queue empty (no thread became runnable).
  assertBool "no-op replenishment leaves the run queue empty"
    ((processReplenishmentsDueOnCore stIdle bootCoreId 0).1.scheduler.runQueueOnCore bootCoreId).toList.isEmpty
  -- the per-core CBS replenishment does not advance the global timer.
  assertBool "replenishment does not advance machine.timer"
    ((processReplenishmentsDueOnCore stIdle bootCoreId 0).1.machine.timer == stIdle.machine.timer)

/-- §3.8 SM5.I: the verified per-core run-loop step (`perCoreTimerTickStep`) — the
FFI-free decision core the (HAL-linked) per-core timer entry drives.  The entry's
runtime behaviour (firing SGIs through `ffiSendSgi`) is not host-runnable (the test
exe does not link the HAL); we exercise the pure step here. -/
private def runRunLoopStepChecks : IO Unit := do
  IO.println "--- §3.8 SM5.I per-core run-loop step ---"
  let st := stIdle
  -- Out-of-range core id is a fail-closed no-op: state unchanged, no SGIs.
  assertBool "step: out-of-range core id (99) is a no-op, no SGIs"
    (((perCoreTimerTickStep st 99).2).isEmpty)
  assertBool "step: out-of-range core id (99) leaves the timer untouched"
    ((perCoreTimerTickStep st 99).1.machine.timer == st.machine.timer)
  -- On a valid idle core (currentOnCore = none), the tick emits no cross-core SGIs.
  assertBool "step: idle valid core (0) emits no cross-core SGIs"
    (((perCoreTimerTickStep st 0).2).isEmpty)
  -- The step never fabricates SGIs beyond what `timerTickOnCore` returns.
  assertBool "step on valid core 3 emits no SGIs on the idle fixture"
    (((perCoreTimerTickStep st 3).2).isEmpty)
  -- Success path COMMITS a genuine state change (vs the fail-closed no-op):
  -- seed core 0's lastTimeoutErrors with a stale record, then a valid-core step
  -- runs the SM5.D.9 clear so the post-step record is empty — proving the step
  -- took the `.ok result → result` branch and installed the new state, not `(st, [])`.
  let staleErrs : List (ThreadId × KernelError) := [(ThreadId.ofNat 1, KernelError.invalidArgument)]
  let stStale : SystemState :=
    { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore bootCoreId staleErrs }
  assertBool "step on valid core 0 commits the tick (SM5.D.9 clears lastTimeoutErrors)"
    (((perCoreTimerTickStep stStale 0).1.scheduler.lastTimeoutErrorsOnCore bootCoreId).isEmpty)
  -- ... whereas the fail-closed out-of-range step leaves the stale record untouched
  -- (it returns the input state unchanged, never committing a partial tick).
  assertBool "step on out-of-range core 99 does NOT clear lastTimeoutErrors (true no-op)"
    (((perCoreTimerTickStep stStale 99).1.scheduler.lastTimeoutErrorsOnCore bootCoreId).length == 1)
  -- Single-authority clock (the boot-core advance re-homed at the composition
  -- point): a committed boot-core step advances `machine.timer` by exactly one —
  -- the CBS/timeout clock ticks on the live path, matching the single-core
  -- `timerTick` which advanced it on every committed path.
  assertBool "step on boot core 0 advances machine.timer by exactly 1"
    ((perCoreTimerTickStep st 0).1.machine.timer == st.machine.timer + 1)
  -- ... and a non-boot core's step reads the shared clock without advancing it
  -- (only the boot core is the clock authority; four cores ticking must not run
  -- the clock at 4x).
  assertBool "step on non-boot core 3 leaves machine.timer untouched"
    ((perCoreTimerTickStep st 3).1.machine.timer == st.machine.timer)
  -- SM5.D.6 composition (the run loop genuinely invokes the tick THEN the
  -- domain transition): with a NON-EMPTY domain schedule, away from a
  -- boundary, a committed step decrements the ticked core's domain time
  -- remaining — pinned on a state whose remaining time is safely above the
  -- boundary.  (Single-domain mode is inert — pinned below.)
  let schedTwoDomains := { st.scheduler with domainSchedule := [dom0, dom1] }
  let stMidDomain : SystemState :=
    { st with scheduler := schedTwoDomains.setDomainTimeRemainingOnCore bootCoreId 10 }
  assertBool "step runs the domain transition (in-domain decrement 10 -> 9, non-empty schedule)"
    (((perCoreTimerTickStep stMidDomain 0).1.scheduler.domainTimeRemainingOnCore
        bootCoreId) == 9)
  -- Single-domain mode (empty schedule — the RPi5 v1.0.0 default): the domain
  -- layer is inert, so the committed step leaves the countdown untouched
  -- (PR #880 round 4 — no drift toward a perpetual boundary).
  let stIdleCountdown : SystemState :=
    { st with scheduler := st.scheduler.setDomainTimeRemainingOnCore bootCoreId 10 }
  assertBool "step leaves the countdown untouched in single-domain mode (inert)"
    (((perCoreTimerTickStep stIdleCountdown 0).1.scheduler.domainTimeRemainingOnCore
        bootCoreId) == 10)

/-- A single-domain (empty schedule) idle state, for the SM5.D.6 no-op witness. -/
private def stSingleDomain : SystemState :=
  let st := BootstrapBuilder.empty.build
  { st with scheduler := { st.scheduler with domainSchedule := [] } }

/-- §3.9 SM5.D.6: the full per-core domain re-dispatch (switchDomainOnCore /
scheduleDomainOnCore). -/
private def runDomainRedispatchChecks : IO Unit := do
  IO.println "--- §3.9 SM5.D.6 domain re-dispatch ---"
  -- single-domain mode: the domain switch is a no-op (the current thread, which is
  -- `none` on the freshly-built state, is unchanged).
  assertBool "switchDomainOnCore is a no-op under an empty domain schedule"
    (match switchDomainOnCore stSingleDomain bootCoreId with
     | .ok st' => st'.scheduler.currentOnCore bootCoreId == stSingleDomain.scheduler.currentOnCore bootCoreId
     | .error _ => false)
  -- a domain switch on a non-empty schedule clears the current thread on core c.
  assertBool "switchDomainOnCore clears current on a non-empty schedule"
    (match switchDomainOnCore stDomain bootCoreId with
     | .ok st' => st'.scheduler.currentOnCore bootCoreId == none
     | .error _ => false)
  -- and rotates the active domain to the next entry (dom1).
  assertBool "switchDomainOnCore rotates the active domain to dom1"
    (match switchDomainOnCore stDomain bootCoreId with
     | .ok st' => st'.scheduler.activeDomainOnCore bootCoreId == dom1.domain
     | .error _ => false)
  -- the domain switch preserves the object-store invariant.
  assertBool "switchDomainOnCore succeeds on the rotation fixture"
    (match switchDomainOnCore stDomain bootCoreId with | .ok _ => true | .error _ => false)
  -- a sub-boundary scheduleDomainOnCore (domainTimeRemaining > 1) just decrements.
  let stMid := { stDomain with scheduler :=
    stDomain.scheduler.setDomainTimeRemainingOnCore bootCoreId 5 }
  assertBool "scheduleDomainOnCore decrements domain time when not at the boundary"
    (match scheduleDomainOnCore stMid bootCoreId with
     | .ok st' => st'.scheduler.domainTimeRemainingOnCore bootCoreId == 4
     | .error _ => false)

private def tidHigh : SeLe4n.ThreadId := ThreadId.ofNat 400
private def tidLow : SeLe4n.ThreadId := ThreadId.ofNat 401

/-- Empty-schedule domain boundary with a high-priority (200) thread RUNNING and
a low-priority (10) thread queued: `domainSchedule = []` (the RPi5 v1.0.0
default) and `domainTimeRemaining = 1`, so the next `scheduleDomainOnCore` takes
the single-domain boundary arm. -/
private def stBoundaryBusy : SystemState :=
  let base :=
    (BootstrapBuilder.empty.withObject tidHigh.toObjId (.tcb (mkTcb 400 200 0))
      |>.withObject tidLow.toObjId (.tcb (mkTcb 401 10 0))
      |>.withRunnable [tidLow]
      |>.withCurrent (some tidHigh)).build
  { base with scheduler := base.scheduler.setDomainTimeRemainingOnCore bootCoreId 1 }

/-- §3.10 (PR #880 review rounds 2 + 4): single-domain mode is **inert** — with
no domain schedule there is no boundary, so the domain tick can neither drop
the running thread (the round-2 hazard) nor degrade the time-slice quantum to
per-tick re-dispatch churn (the round-4 hazard: the empty-schedule arm had no
entry to reload the countdown from, so once `domainTimeRemainingOnCore`
reached the boundary every subsequent tick re-prepped and re-dispatched,
capable of immediately reversing an equal-priority switch the budget tick had
just made).  Regression pins on the busy fixture (high-priority current,
low-priority queued, countdown at the old boundary value): the domain tick is
the identity — incumbent untouched, waiter untouched, countdown untouched (no
perpetual boundary) — and the composed live step preserves all three. -/
private def runEmptyBoundaryRequeueChecks : IO Unit := do
  IO.println "--- §3.10 single-domain mode is inert ---"
  assertBool "fixture: single-domain mode (empty schedule)"
    (stBoundaryBusy.scheduler.domainSchedule.isEmpty)
  assertBool "fixture: countdown at the old boundary value (1)"
    (stBoundaryBusy.scheduler.domainTimeRemainingOnCore bootCoreId == 1)
  assertBool "fixture: high-priority thread current, low-priority thread queued"
    (stBoundaryBusy.scheduler.currentOnCore bootCoreId == some tidHigh
      && decide (tidLow ∈ (stBoundaryBusy.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "inert domain tick keeps the incumbent current (no dispatch at all)"
    (match scheduleDomainOnCore stBoundaryBusy bootCoreId with
     | .ok st' => st'.scheduler.currentOnCore bootCoreId == some tidHigh
     | .error _ => false)
  assertBool "inert domain tick leaves the low-priority waiter queued"
    (match scheduleDomainOnCore stBoundaryBusy bootCoreId with
     | .ok st' => decide (tidLow ∈ (st'.scheduler.runQueueOnCore bootCoreId).toList)
     | .error _ => false)
  -- Round 4's specific hazard: the countdown must NOT stick at a perpetual
  -- boundary — in inert mode it is simply never touched.
  assertBool "inert domain tick leaves the countdown untouched (no perpetual boundary)"
    (match scheduleDomainOnCore stBoundaryBusy bootCoreId with
     | .ok st' => st'.scheduler.domainTimeRemainingOnCore bootCoreId == 1
     | .error _ => false)
  -- The composed live step (tick THEN domain transition) preserves the
  -- incumbent and the countdown through single-domain mode as well.
  assertBool "live run-loop step keeps the incumbent current in single-domain mode"
    ((perCoreTimerTickStep stBoundaryBusy 0).1.scheduler.currentOnCore bootCoreId
      == some tidHigh)
  assertBool "live run-loop step leaves the countdown untouched in single-domain mode"
    ((perCoreTimerTickStep stBoundaryBusy 0).1.scheduler.domainTimeRemainingOnCore
        bootCoreId == 1)
  -- And on the idle single-domain state the whole domain tick is the identity.
  assertBool "single-domain domain tick is the identity on the idle state"
    (match scheduleDomainOnCore stSingleDomain bootCoreId with
     | .ok st' => st'.scheduler.currentOnCore bootCoreId
          == stSingleDomain.scheduler.currentOnCore bootCoreId
        && ((st'.scheduler.runQueueOnCore bootCoreId).toList.isEmpty : Bool)
     | .error _ => false)

/-- §3.11 (PR #880 follow-up — commit-coupled shadow clock): the flagged step's
clock-advance report is exactly the committed state's `machine.timer` delta,
so the HAL `TICK_COUNT` shadow (advanced by the live entry iff this flag is
set) moves iff the model clock moved — no arm, fail-closed ones included, can
put the two out of step. -/
private def runClockAdvanceFlagChecks : IO Unit := do
  IO.println "--- §3.11 commit-coupled shadow-clock flag ---"
  -- A committed boot-core step advances the model clock and reports it.
  assertBool "boot-core committed step reports the clock advance (flag true)"
    ((perCoreTimerTickStepWithClockAdvance stIdle 0).1.2 == true)
  -- ... and the flag agrees with the committed state it was computed against.
  assertBool "flag-true step committed machine.timer + 1 (report matches commit)"
    ((perCoreTimerTickStepWithClockAdvance stIdle 0).2.machine.timer
      == stIdle.machine.timer + 1)
  -- A non-boot core's committed step reads the shared clock without advancing
  -- it, and reports exactly that.
  assertBool "non-boot committed step reports no clock advance (flag false)"
    ((perCoreTimerTickStepWithClockAdvance stIdle 3).1.2 == false)
  assertBool "flag-false step committed machine.timer unchanged"
    ((perCoreTimerTickStepWithClockAdvance stIdle 3).2.machine.timer
      == stIdle.machine.timer)
  -- Fail-closed: an out-of-range core id commits nothing and reports nothing.
  assertBool "out-of-range core id reports no clock advance (fail-closed)"
    ((perCoreTimerTickStepWithClockAdvance stIdle 99).1.2 == false)
  -- The flagged step commits the plain step's state and SGIs verbatim (the
  -- flag is a report beside the commit, never a change to it).
  assertBool "flagged step commits the plain step's state (timer agrees)"
    ((perCoreTimerTickStepWithClockAdvance stIdle 0).2.machine.timer
      == (perCoreTimerTickStep stIdle 0).1.machine.timer)
  assertBool "flagged step emits the plain step's SGIs"
    ((perCoreTimerTickStepWithClockAdvance stIdle 0).1.1.length
      == (perCoreTimerTickStep stIdle 0).2.length)
  -- The busy boundary fixture (§3.10) also commits a boot-core advance: the
  -- flag rides every committed boot step, whatever the scheduling outcome.
  assertBool "busy boundary fixture's boot step reports the clock advance"
    ((perCoreTimerTickStepWithClockAdvance stBoundaryBusy 0).1.2 == true)

/-- §3.12 (PR #880 round 4 — clock-advance honesty): the boot core's committed
clock advance can leave a REMOTE core's queued replenishment due at exactly
the new clock — never strictly overdue (the weak form
`tickClockedState_bootCore_replenish_ge` holds) — and the owning core's own
next committed step drains it, restoring the strict pipeline-order form
(`perCoreTimerTickStep_ok_establishes_replenishmentPipelineOrderOnCore_self`).
The two-phase pin of the bounded release window inherent to per-core release
queues (each core drains its own queue on its own PPI). -/
private def runClockAdvanceReplenishChecks : IO Unit := do
  IO.println "--- §3.12 clock-advance replenish window ---"
  let scId : SeLe4n.SchedContextId := ⟨77⟩
  -- Seed core 1's queue with an entry due one tick in the future: the strict
  -- form holds at the current clock.
  let stSeeded := replenishOnCore stIdle core1 scId (stIdle.machine.timer + 1)
  assertBool "seeded: core 1 holds one future replenishment (strict form)"
    (((stSeeded.scheduler.replenishQueueOnCore core1).entries.length == 1)
      && decide (∀ p ∈ (stSeeded.scheduler.replenishQueueOnCore core1).entries,
            p.2 > stSeeded.machine.timer))
  -- Boot core ticks: the shared clock advances; core 1's entry is untouched
  -- and now due at exactly the new clock — the documented window.
  let stAfterBoot := (perCoreTimerTickStep stSeeded 0).1
  assertBool "boot step advances the clock and leaves the remote entry queued"
    (stAfterBoot.machine.timer == stSeeded.machine.timer + 1
      && ((stAfterBoot.scheduler.replenishQueueOnCore core1).entries.length == 1))
  assertBool "remote entry is due-now, never strictly overdue (weak form holds)"
    (decide (∀ p ∈ (stAfterBoot.scheduler.replenishQueueOnCore core1).entries,
        p.2 ≥ stAfterBoot.machine.timer))
  -- Core 1's own committed step drains the due entry: the strict form is
  -- restored on its queue at the current clock.
  let stAfterOwn := (perCoreTimerTickStep stAfterBoot 1).1
  assertBool "the owner's next step drains the due entry (strict form restored)"
    ((stAfterOwn.scheduler.replenishQueueOnCore core1).entries.isEmpty)
  assertBool "the owner's step reads the shared clock without advancing it"
    (stAfterOwn.machine.timer == stAfterBoot.machine.timer)

/-- §3.13 (PR #880 round 7 — local replenish-wake reschedule): a due CBS
replenishment that refills a HIGHER-priority thread queued on the executing
core itself preempts the lower-priority current thread in the very tick that
made it eligible.  The wake is otherwise invisible — placement suppressed (the
thread sat queued since its exhaustion re-enqueue), no SGI (local target), no
preemption flag (the current thread's budget survives the charge) — so before
round 7 the refilled thread waited out the current thread's entire remaining
budget on the default empty domain schedule.  Also pins the idle-slot arm (a
vacated core dispatches its refilled thread — the round-17 carve-out) and the
quiet-tick identity (no local wake, no re-dispatch). -/
private def runLocalReplenishRescheduleChecks : IO Unit := do
  IO.println "--- §3.13 local replenish-wake reschedule ---"
  let tidLo := ThreadId.ofNat 310   -- low-priority current, unbound, slice not expiring
  let tidHi := ThreadId.ofNat 311   -- high-priority, bound to an exhausted SC
  let scHi : SeLe4n.SchedContextId := ⟨88⟩
  let tcbLo : TCB := { mkTcb 310 5 0 with schedContextBinding := .unbound, timeSlice := 10 }
  let tcbHi : TCB := { mkTcb 311 20 0 with schedContextBinding := .bound scHi }
  let scObj : SchedContext :=
    { (default : SchedContext) with
        priority := ⟨20⟩, boundThread := some tidHi,
        budget := ⟨5⟩, period := ⟨10⟩, budgetRemaining := ⟨0⟩,
        replenishments := [{ amount := ⟨5⟩, eligibleAt := 0 }] }
  -- exhausted tidHi queued on the boot core (its exhaustion re-enqueue), tidLo
  -- current with plenty of slice, single-domain mode (the RPi5 default).
  let stBase : SystemState :=
    ((((BootstrapBuilder.empty.withObject tidLo.toObjId (.tcb tcbLo)).withObject
        tidHi.toObjId (.tcb tcbHi)).withObject
        scHi.toObjId (.schedContext scObj)).withRunnable [tidHi]).build
  let stBusy := { stBase with scheduler := stBase.scheduler.setCurrentOnCore bootCoreId (some tidLo) }
  let stDue := replenishOnCore stBusy bootCoreId scHi stBusy.machine.timer
  -- The drain raises the local-wake bit: the wake resolved and targeted the
  -- executing core, where no SGI can poke.
  assertBool "the prepared phase raises the local-wake bit"
    ((timerTickOnCorePrepared stDue bootCoreId).2.2 == true)
  assertBool "the local wake fires no SGI (local target)"
    ((timerTickOnCorePrepared stDue bootCoreId).2.1.isEmpty)
  -- THE round-7 pin: the tick that refills tidHi dispatches it — the
  -- lower-priority current is preempted at the release point, not after its
  -- remaining budget.
  assertBool "the refilling tick preempts the lower-priority current (tidHi runs)"
    (match timerTickOnCore stDue bootCoreId with
     | .ok r => r.1.scheduler.currentOnCore bootCoreId == some tidHi
     | .error _ => false)
  assertBool "the preempted current is re-enqueued, not dropped"
    (match timerTickOnCore stDue bootCoreId with
     | .ok r => (r.1.scheduler.runQueueOnCore bootCoreId).contains tidLo
     | .error _ => false)
  -- Idle-slot arm (the round-17 carve-out): a vacated core whose queued thread
  -- was ineligible at vacate time is dispatched the moment its refill lands.
  let stVacantDue := replenishOnCore stBase bootCoreId scHi stBase.machine.timer
  assertBool "a vacated core dispatches its refilled thread in the same tick"
    (match timerTickOnCore stVacantDue bootCoreId with
     | .ok r => r.1.scheduler.currentOnCore bootCoreId == some tidHi
     | .error _ => false)
  -- Quiet tick: with no due replenishment the bit stays down and the tick is
  -- the plain budget charge — no re-dispatch, tidLo keeps the core.
  assertBool "a quiet tick raises no local-wake bit"
    ((timerTickOnCorePrepared stBusy bootCoreId).2.2 == false)
  assertBool "a quiet non-preempting tick keeps the current thread"
    (match timerTickOnCore stBusy bootCoreId with
     | .ok r => r.1.scheduler.currentOnCore bootCoreId == some tidLo
     | .error _ => false)

def runAll : IO Unit := do
  IO.println "=== WS-SM SM5.D — Per-core timer tick suite ==="
  runLockSetChecks
  runWcrtChecks
  runDomainDecrementChecks
  runDomainRotateChecks
  runBudgetPreemptChecks
  runIdleTickChecks
  runReplenishChecks
  runRunLoopStepChecks
  runDomainRedispatchChecks
  runEmptyBoundaryRequeueChecks
  runClockAdvanceFlagChecks
  runClockAdvanceReplenishChecks
  runLocalReplenishRescheduleChecks
  IO.println "=== SM5.D timer suite: all checks passed ==="

end SeLe4n.Testing.SmpTimer

def main : IO Unit := SeLe4n.Testing.SmpTimer.runAll
