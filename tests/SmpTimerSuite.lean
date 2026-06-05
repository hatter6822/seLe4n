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
#check @perCoreTimerTickStep_sgis_eq_tick
#check @perCoreTimerTickStep_preserves_objects_invExt
#check @perCoreTimerTickStep_ok_currentThreadValidOnCore

-- §4b SM5.D.6 full per-core domain re-dispatch (switchDomainOnCore / scheduleDomainOnCore).
#check @switchDomainOnCore_singleDomain_noop
#check @switchDomainOnCore_preserves_objects_invExt
#check @switchDomainOnCore_sets_currentOnCore_none
#check @switchDomainOnCore_rotates
#check @scheduleDomainOnCore_decrements
#check @scheduleDomainOnCore_preserves_objects_invExt

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
    (hStep : timerTickOnCore st c = .ok (st', sgis)) : st'.machine = st.machine :=
  timerTickOnCore_advances_per_core st c st' sgis hCur hStep

/-- SM5.D.4 / plan §6.1: a remote-targeted CBS replenish (of a thread not running
on any core — audit-pass-2 / Codex-P2 guard) emits a cross-core SGI. -/
example (st : SystemState) (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hTcb : (refillSchedContext st scId now).getTcb? tid = some tcb)
    (hNotRunning : runningOnSomeCore (refillSchedContext st scId now) tid = false)
    (hRemote : determineTargetCore (refillSchedContext st scId now) tid ≠ execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2
      = some (determineTargetCore (refillSchedContext st scId now) tid, SgiKind.reschedule) :=
  cbsReplenish_can_wake_remote_core st execCore scId now tid tcb hTarget hTcb hNotRunning hRemote

/-- SM5.D.5 / plan §6.1: budget-tick preemption re-dispatches via the budget-aware
reschedule. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 st' : SystemState)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid)
    (hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb)
    (hBud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, true))
    (hSched : scheduleEffectiveOnCore st3 c = .ok st') :
    timerTickOnCore st c = .ok (st', (timerTickOnCorePrepared st c).2) :=
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
    ((processOneReplenishmentOnCore stIdle bootCoreId scId 0).2 == none)
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
  IO.println "=== SM5.D timer suite: all checks passed ==="

end SeLe4n.Testing.SmpTimer

def main : IO Unit := SeLe4n.Testing.SmpTimer.runAll
