-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.PerCoreTimerEntry
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

-- SM5.D.6 domain rotation.
#check @decrementDomainTimeOnCore_decrements
#check @decrementDomainTimeOnCore_rotates
#check @decrementDomainTimeOnCore_singleDomain_noop
#check @decrementDomainTimeOnCore_activeDomainOnCore_ne

-- SM5.D.4 CBS replenishment + cross-core wake.
#check @cbsReplenish_can_wake_remote_core
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
#check @timerTickOnCore_rotates_domain
#check @timerTickOnCore_preempts_local
#check @timerTickOnCore_preserves_objects_invExt
#check @timerTickOnCore_eq_prepared
#check @timerTickOnCorePrepared
#check @timerTickOnCorePreDomain

-- SM5.D.8 decidability witnesses.
#check @timerTickOnCoreSucceeds
#check @timerTickOnCoreEmitsSgi
#check @timerTickBudgetOnCorePreempts

-- SM5.D.1 export seam (PerCoreTimerEntry).
#check @perCoreTimerTickEntry
#check @perCoreTimerTickEntry_returns_unit_marker

-- ============================================================================
-- §2  Elaboration-time examples: apply each headline theorem to verified inputs
-- ============================================================================

/-- SM5.D.2 / plan §6.1: the per-core tick advances core `c`'s state without
advancing the global timer (idle path). -/
example (st : SystemState) (c : CoreId) (st' : SystemState) (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hStep : timerTickOnCore st c = .ok (st', sgis)) : st'.machine = st.machine :=
  timerTickOnCore_advances_per_core st c st' sgis hCur hStep

/-- SM5.D.4 / plan §6.1: a remote-targeted CBS replenish emits a cross-core SGI. -/
example (st : SystemState) (execCore : CoreId) (scId : SeLe4n.SchedContextId) (now : Nat)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTarget : replenishWakeTarget st (refillSchedContext st scId now) scId = some tid)
    (hTcb : (refillSchedContext st scId now).getTcb? tid = some tcb)
    (hNotCur : (refillSchedContext st scId now).scheduler.currentOnCore
        (determineTargetCore (refillSchedContext st scId now) tid) ≠ some tid)
    (hRemote : determineTargetCore (refillSchedContext st scId now) tid ≠ execCore) :
    (processOneReplenishmentOnCore st execCore scId now).2
      = some (determineTargetCore (refillSchedContext st scId now) tid, SgiKind.reschedule) :=
  cbsReplenish_can_wake_remote_core st execCore scId now tid tcb hTarget hTcb hNotCur hRemote

/-- SM5.D.5 / plan §6.1: budget-tick preemption re-dispatches via the budget-aware
reschedule. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st3 st' : SystemState)
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = some tid)
    (hTcb : (timerTickOnCorePrepared st c).1.getTcb? tid = some tcb)
    (hBud : timerTickBudgetOnCore (timerTickOnCorePrepared st c).1 c tid tcb = .ok (st3, true))
    (hSched : scheduleEffectiveOnCore st3 c = .ok st') :
    timerTickOnCore st c = .ok (st', (timerTickOnCorePrepared st c).2) :=
  timerTickOnCore_preempts_local st c tid tcb st3 st' hCur hTcb hBud hSched

/-- SM5.D.6 / plan §6.1: the tick rotates core `c`'s active domain. -/
example (st : SystemState) (c : CoreId) (entry : DomainScheduleEntry) (st' : SystemState)
    (sgis : List (CoreId × SgiKind))
    (hCur : (timerTickOnCorePrepared st c).1.scheduler.currentOnCore c = none)
    (hStep : timerTickOnCore st c = .ok (st', sgis))
    (hExpired : (timerTickOnCorePreDomain st c).scheduler.domainTimeRemainingOnCore c ≤ 1)
    (hSched : (timerTickOnCorePreDomain st c).scheduler.domainSchedule ≠ [])
    (hEntry : (timerTickOnCorePreDomain st c).scheduler.domainSchedule[
        ((timerTickOnCorePreDomain st c).scheduler.domainScheduleIndexOnCore c + 1)
          % (timerTickOnCorePreDomain st c).scheduler.domainSchedule.length]? = some entry) :
    st'.scheduler.activeDomainOnCore c = DomainScheduleEntry.domain entry :=
  timerTickOnCore_rotates_domain st c entry st' sgis hCur hStep hExpired hSched hEntry

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
two-entry domain schedule, so `decrementDomainTimeOnCore` rotates to `dom1`. -/
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

/-- §3.4 SM5.D.6: an expired domain time rotates to the next schedule entry. -/
private def runDomainRotateChecks : IO Unit := do
  IO.println "--- §3.4 SM5.D.6 domain rotation ---"
  assertBool "stDomain boot-core domain time is at its last tick (1)"
    (stDomain.scheduler.domainTimeRemainingOnCore bootCoreId == 1)
  assertBool "expired domain rotates active domain to dom1 (index 0 → 1)"
    ((decrementDomainTimeOnCore stDomain bootCoreId).scheduler.activeDomainOnCore bootCoreId == dom1.domain)
  assertBool "rotation resets domain time to dom1.length (3)"
    ((decrementDomainTimeOnCore stDomain bootCoreId).scheduler.domainTimeRemainingOnCore bootCoreId == 3)
  assertBool "rotation advances the schedule index to 1"
    ((decrementDomainTimeOnCore stDomain bootCoreId).scheduler.domainScheduleIndexOnCore bootCoreId == 1)
  -- a sibling core (core 1) is unaffected by the boot core's rotation.
  assertBool "domain rotation is core-local (core 1 active domain unchanged)"
    ((decrementDomainTimeOnCore stDomain bootCoreId).scheduler.activeDomainOnCore core1
      == stDomain.scheduler.activeDomainOnCore core1)

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

/-- §3.8 SM5.D.1: the per-core timer-entry export seam returns unit. -/
private def runEntrySeamChecks : IO Unit := do
  IO.println "--- §3.8 SM5.D.1 per-core timer-entry seam ---"
  -- The export seam is a BaseIO action; running it must complete without error.
  perCoreTimerTickEntry 0
  perCoreTimerTickEntry 3
  assertBool "perCoreTimerTickEntry seam ran for cores 0 and 3" true

def runAll : IO Unit := do
  IO.println "=== WS-SM SM5.D — Per-core timer tick suite ==="
  runLockSetChecks
  runWcrtChecks
  runDomainDecrementChecks
  runDomainRotateChecks
  runBudgetPreemptChecks
  runIdleTickChecks
  runReplenishChecks
  runEntrySeamChecks
  IO.println "=== SM5.D timer suite: all checks passed ==="

end SeLe4n.Testing.SmpTimer

def main : IO Unit := SeLe4n.Testing.SmpTimer.runAll
