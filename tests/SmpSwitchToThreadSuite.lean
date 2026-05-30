-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.B — Per-core `switchToThread` test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM5.B "Per-core switchToThread" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.2, §5).

* **§1 Surface anchors** — every public SM5.B symbol resolves at
  elaboration time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem
  (sets-current, preempts-previous, rejects-remote, excludes-current,
  cross-core independence, totality, lock-set) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_switch_to_thread_suite`
  exercises the actual `switchToThreadOnCore` computation on the SM5.B.9
  scenarios: sets-current, dequeue-on-dispatch, preempt-previous,
  reject-remote, admit-unbound / admit-matching-affinity, cross-core
  independence, and the non-TCB error path, plus the SM5.B.2 lock-set
  witnesses and the SM5.B.7 FFI seam.
-/

namespace SeLe4n.Testing.SmpSwitchToThread

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.B public symbol resolves
-- ============================================================================

-- SM5.B.4 foundation: the per-thread CPU-affinity field + reject-remote error.
#check @TCB.cpuAffinity
#check KernelError.threadOnDifferentCore

-- SM5.B.1/.3/.4 production operations (Scheduler.Operations.Selection):
#check @affinityAdmitsCore
#check @affinityAdmitsCore_none
#check @affinityAdmitsCore_some
#check @preemptCurrentOnCore
#check @switchToThreadOnCore

-- SM5.B.2 lock-set:
#check @switchToThreadOnCoreLockSet
#check @switchToThreadOnCoreLockSet_length
#check @switchToThreadOnCoreLockSet_write_only
#check @switchToThreadOnCoreLockSet_contains_objStore_write
#check @switchToThreadOnCoreLockSet_contains_runQueue_write
#check @switchToThreadOnCoreLockSet_object_before_runQueue
#check @switchToThreadOnCoreLockSet_keys_nodup

-- §2 preempt frame lemmas:
#check @preemptCurrentOnCore_currentOnCore
#check @preemptCurrentOnCore_runQueueOnCore_ne
#check @preemptCurrentOnCore_runQueueOnCore_self_active

-- SM5.B.1/.3/.4/.5/.6 switch-semantics theorems:
#check @switchToThreadOnCore_rejects_remote
#check @switchToThreadOnCore_ok_of_admits
#check @switchToThreadOnCore_sets_current
#check @switchToThreadOnCore_runQueueOnCore_excludes_current
#check @switchToThreadOnCore_preempts_previous
#check @switchToThreadOnCore_independent_of_other_core

-- SM5.B.8 totality + decidability:
#check @switchToThreadOnCore_total
#check @switchToThreadOnCoreSucceeds
#check @switchToThreadOnCoreRejectsRemote

-- SM5.B.7 FFI seam (Platform.FFI extern + Concurrency typed wrappers):
#check @Platform.FFI.ffiSwitchToThread
#check @Platform.FFI.ffiPerCoreCurrentThread
#check @switchToThreadHw
#check @perCoreCurrentThreadHw
#check @switchToThreadHw_returns_baseio_uint64_marker
#check @perCoreCurrentThreadHw_returns_baseio_uint64_marker

-- ============================================================================
-- §2  Elaboration-time examples: apply each headline theorem to verified inputs
-- ============================================================================

/-- SM5.B.1 / Theorem 3.2.1: a successful switch sets the current thread. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.currentOnCore c = some tid :=
  switchToThreadOnCore_sets_current st c tid st' h

/-- SM5.B.5: dequeue-on-dispatch — the new current thread is not in the queue. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (h : switchToThreadOnCore st c tid = .ok st') :
    tid ∉ (st'.scheduler.runQueueOnCore c).toList :=
  switchToThreadOnCore_runQueueOnCore_excludes_current st c tid st' h

/-- SM5.B.3 / Theorem 3.2.2: the preempted previous current thread is re-enqueued. -/
example (st : SystemState) (c : CoreId) (tid prevTid : SeLe4n.ThreadId) (prevTcb : TCB)
    (st' : SystemState)
    (hCur : st.scheduler.currentOnCore c = some prevTid) (hNe : prevTid ≠ tid)
    (hPrev : st.getTcb? prevTid = some prevTcb)
    (h : switchToThreadOnCore st c tid = .ok st') :
    prevTid ∈ (st'.scheduler.runQueueOnCore c).toList :=
  switchToThreadOnCore_preempts_previous st c tid prevTid prevTcb st' hCur hNe hPrev h

/-- SM5.B.4 / Theorem 3.2.3: reject-remote — a switch onto a non-affinity core. -/
example (st : SystemState) (c c' : CoreId) (tid : SeLe4n.ThreadId) (tidTcb : TCB)
    (hTcb : st.getTcb? tid = some tidTcb) (hAff : tidTcb.cpuAffinity = some c')
    (hNe : c' ≠ c) :
    switchToThreadOnCore st c tid = .error .threadOnDifferentCore :=
  switchToThreadOnCore_rejects_remote st c c' tid tidTcb hTcb hAff hNe

/-- SM5.B.6: cross-core independence — other cores' slots are untouched. -/
example (st : SystemState) (c c' : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hcc : c ≠ c') (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
      ∧ st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' :=
  switchToThreadOnCore_independent_of_other_core st c c' tid st' hcc h

/-- SM5.B.4 dual: a thread whose affinity admits the core succeeds. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tidTcb : TCB)
    (hTcb : st.getTcb? tid = some tidTcb) (hAff : affinityAdmitsCore tidTcb c = true) :
    ∃ st', switchToThreadOnCore st c tid = .ok st' :=
  switchToThreadOnCore_ok_of_admits st c tid tidTcb hTcb hAff

/-- SM5.B.8: totality. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    ∃ r, switchToThreadOnCore st c tid = r :=
  switchToThreadOnCore_total st c tid

/-- SM5.B.2: the lock-set acquires the object lock before the run-queue lock. -/
example (c : CoreId) :
    SchedLockId.object schedObjStoreLockId < SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
  switchToThreadOnCoreLockSet_object_before_runQueue c

/-- SM5.B.4: affinity-admits algebra — an unbound thread runs on any core. -/
example (tcb : TCB) (c : CoreId) (h : tcb.cpuAffinity = none) :
    affinityAdmitsCore tcb c = true := affinityAdmitsCore_none tcb c h

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.B.9 switch scenarios
-- ============================================================================

/-- Minimal test TCB at `tid`, priority `prio`, scheduling domain `dom`. -/
private def mkTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

private def tidA : SeLe4n.ThreadId := ThreadId.ofNat 100   -- unbound runnable
private def tidP : SeLe4n.ThreadId := ThreadId.ofNat 101   -- previous current
private def tidR : SeLe4n.ThreadId := ThreadId.ofNat 102   -- bound to core 1 (remote)
private def tidBoot : SeLe4n.ThreadId := ThreadId.ofNat 103 -- bound to the boot core
private def tidGhost : SeLe4n.ThreadId := ThreadId.ofNat 999 -- not a TCB

/-- A non-boot core, used by the reject-remote / cross-core scenarios. -/
private def core1 : CoreId := ⟨1, by decide⟩

/-- Boot core has the unbound runnable thread `tidA`; no current thread. -/
private def stRunnable : SystemState :=
  ((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).withRunnable
    [tidA]).build

/-- Boot core's current is `tidP` (a TCB); `tidA` is runnable in its queue.
Switching to `tidA` must preempt `tidP` back into the boot core's run queue. -/
private def stPreempt : SystemState :=
  let base := (((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).withObject
    tidP.toObjId (.tcb (mkTcb 101 15 0))).withRunnable [tidA]).build
  { base with scheduler := base.scheduler.setCurrentOnCore bootCoreId (some tidP) }

/-- `tidR` is a TCB bound to core 1 (`cpuAffinity = some core1`), sitting in the
boot core's run queue.  A switch on the boot core must reject it; a switch on
core 1 (its affinity) must succeed. -/
private def stRemote : SystemState :=
  ((BootstrapBuilder.empty.withObject tidR.toObjId
    (.tcb { mkTcb 102 10 0 with cpuAffinity := some core1 })).withRunnable [tidR]).build

/-- `tidBoot` is a TCB whose affinity is the boot core — a switch on the boot
core must succeed (matching affinity). -/
private def stAffinityBoot : SystemState :=
  ((BootstrapBuilder.empty.withObject tidBoot.toObjId
    (.tcb { mkTcb 103 10 0 with cpuAffinity := some bootCoreId })).withRunnable [tidBoot]).build

/-- The boot core's run queue references a "ghost" thread that does not resolve
to a TCB; a switch to it must surface `.error schedulerInvariantViolation`. -/
private def stGhost : SystemState :=
  (BootstrapBuilder.empty.withRunnable [tidGhost]).build

/-- Boot core has runnable `tidA`; core 1 independently holds current `tidP` and
a run queue `[tidP]`.  A switch on the boot core must leave core 1 untouched. -/
private def stCrossCore : SystemState :=
  let base := (((BootstrapBuilder.empty.withObject tidA.toObjId (.tcb (mkTcb 100 10 0))).withObject
    tidP.toObjId (.tcb (mkTcb 101 15 0))).withRunnable [tidA]).build
  let core1Sched := (base.scheduler.setCurrentOnCore core1 (some tidP)).setRunQueueOnCore core1 (RunQueue.ofList [(tidP, ⟨15⟩)])
  { base with scheduler := core1Sched }

/-- Run `switchToThreadOnCore` and evaluate a Bool predicate on the `.ok`
post-state; `false` if the switch errored. -/
private def switchOkAnd (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (p : SystemState → Bool) : Bool :=
  match switchToThreadOnCore st c tid with
  | .ok st' => p st'
  | .error _ => false

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1–§3.8: the SM5.B.9 switch scenarios, each evaluating the real
`switchToThreadOnCore` computation. -/
private def runSwitchScenarios : IO Unit := do
  IO.println "--- §3 SM5.B.9 per-core switchToThread scenarios ---"
  -- Scenario 1 (SM5.B.1 / Thm 3.2.1): switching to a runnable thread succeeds
  -- and sets it as the core's current thread.
  assertBool "scenario 1: switch to tidA ⇒ succeeds"
    (decide (switchToThreadOnCoreSucceeds stRunnable bootCoreId tidA))
  assertBool "scenario 1: switch to tidA ⇒ current thread is tidA"
    (switchOkAnd stRunnable bootCoreId tidA
      (fun st' => st'.scheduler.currentOnCore bootCoreId == some tidA))
  -- Scenario 2 (SM5.B.5): dequeue-on-dispatch — the new current thread is NOT
  -- simultaneously in the run queue.
  assertBool "scenario 2: after switch, tidA is dequeued (not in the run queue)"
    (switchOkAnd stRunnable bootCoreId tidA
      (fun st' => !decide (tidA ∈ (st'.scheduler.runQueueOnCore bootCoreId).toList)))
  -- Scenario 3 (SM5.B.3 / Thm 3.2.2): the evicted previous current thread tidP
  -- is re-enqueued into the same core's run queue (preempted, not lost).
  assertBool "scenario 3: preempted previous current tidP is re-enqueued"
    (switchOkAnd stPreempt bootCoreId tidA
      (fun st' => decide (tidP ∈ (st'.scheduler.runQueueOnCore bootCoreId).toList)))
  assertBool "scenario 3: after preempt-switch, current is the incoming tidA"
    (switchOkAnd stPreempt bootCoreId tidA
      (fun st' => st'.scheduler.currentOnCore bootCoreId == some tidA))
  assertBool "scenario 3: the incoming tidA is dequeued (not in the run queue)"
    (switchOkAnd stPreempt bootCoreId tidA
      (fun st' => !decide (tidA ∈ (st'.scheduler.runQueueOnCore bootCoreId).toList)))
  -- Scenario 4 (SM5.B.4 / Thm 3.2.3): reject-remote — tidR is bound to core 1,
  -- so a switch on the boot core is rejected with .threadOnDifferentCore.
  assertBool "scenario 4: switch tidR (affinity core1) on boot core ⇒ rejected"
    (decide (switchToThreadOnCoreRejectsRemote stRemote bootCoreId tidR))
  assertBool "scenario 4: rejected switch does NOT succeed"
    (!decide (switchToThreadOnCoreSucceeds stRemote bootCoreId tidR))
  -- Scenario 5 (SM5.B.4 dual): tidR's affinity admits core 1, so a switch on
  -- core 1 succeeds — the gate admits the matching core.
  assertBool "scenario 5: switch tidR on its affinity core1 ⇒ succeeds"
    (decide (switchToThreadOnCoreSucceeds stRemote core1 tidR))
  assertBool "scenario 5: switch on the matching core is NOT a reject-remote"
    (!decide (switchToThreadOnCoreRejectsRemote stRemote core1 tidR))
  -- Scenario 6: an unbound thread (affinity none) runs on any core; a thread
  -- bound to the boot core runs on the boot core.
  assertBool "scenario 6: unbound tidA admitted on the boot core"
    (decide (switchToThreadOnCoreSucceeds stRunnable bootCoreId tidA))
  assertBool "scenario 6: boot-affinity tidBoot admitted on the boot core"
    (decide (switchToThreadOnCoreSucceeds stAffinityBoot bootCoreId tidBoot))
  -- Scenario 7 (SM5.B.6): cross-core independence — switching on the boot core
  -- leaves core 1's current thread and run queue untouched.
  assertBool "scenario 7: switch on boot core leaves core 1's current = tidP"
    (switchOkAnd stCrossCore bootCoreId tidA
      (fun st' => st'.scheduler.currentOnCore core1 == some tidP))
  assertBool "scenario 7: switch on boot core leaves core 1's run queue (tidP ∈)"
    (switchOkAnd stCrossCore bootCoreId tidA
      (fun st' => decide (tidP ∈ (st'.scheduler.runQueueOnCore core1).toList)))
  -- Scenario 8: non-TCB error path — switching to a ghost thread errors with
  -- .schedulerInvariantViolation (neither succeeds nor reject-remote).
  assertBool "scenario 8: switch to a non-TCB ghost ⇒ does not succeed"
    (!decide (switchToThreadOnCoreSucceeds stGhost bootCoreId tidGhost))
  assertBool "scenario 8: the ghost error is NOT a reject-remote (it is a sched-invariant violation)"
    (!decide (switchToThreadOnCoreRejectsRemote stGhost bootCoreId tidGhost))

/-- §3.9: the SM5.B.2 cross-domain lock-set witnesses. -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.9 SM5.B.2 switchToThread lock-set ---"
  assertBool "switchToThreadOnCoreLockSet bootCoreId has both domain locks (length 2)"
    (decide ((switchToThreadOnCoreLockSet bootCoreId).length == 2))
  assertBool "footprint contains the object-store WRITE lock (guards getTcb? + save)"
    (decide ((SchedLockId.object schedObjStoreLockId, AccessMode.write)
              ∈ switchToThreadOnCoreLockSet bootCoreId))
  assertBool "footprint contains the boot core's run-queue WRITE lock"
    (decide ((SchedLockId.runQueue ⟨bootCoreId⟩, AccessMode.write)
              ∈ switchToThreadOnCoreLockSet bootCoreId))
  assertBool "footprint acquires the object-store lock before the run-queue lock (§4.4)"
    (decide (SchedLockId.object schedObjStoreLockId
              < SchedLockId.runQueue (⟨bootCoreId⟩ : RunQueueLockId)))
  assertBool "footprint keys are duplicate-free"
    (decide (((switchToThreadOnCoreLockSet bootCoreId).map (·.1)).Nodup))
  -- Every core's footprint has both domain locks.
  assertBool "every core's switchToThread footprint has both domain locks (length 2)"
    (allCores.all (fun c => (switchToThreadOnCoreLockSet c).length == 2))

/-- §3.10: the SM5.B.4 affinity-admits algebra (the reject-remote gate's core
computation), exercised directly on concrete TCBs. -/
private def runAffinityAlgebraChecks : IO Unit := do
  IO.println "--- §3.10 SM5.B.4 affinity-admits algebra ---"
  -- An unbound thread (default `cpuAffinity = none`) is admitted on every core.
  assertBool "unbound thread (cpuAffinity none) admitted on every core"
    (allCores.all (fun c => affinityAdmitsCore (mkTcb 100 10 0) c))
  -- A thread bound to core 1 is admitted ONLY on core 1.
  assertBool "core1-bound thread admitted on core 1"
    (affinityAdmitsCore { mkTcb 102 10 0 with cpuAffinity := some core1 } core1)
  assertBool "core1-bound thread REJECTED on the boot core"
    (!affinityAdmitsCore { mkTcb 102 10 0 with cpuAffinity := some core1 } bootCoreId)

def runSmpSwitchToThreadChecks : IO Unit := do
  IO.println "WS-SM SM5.B — Per-core switchToThread suite"
  IO.println "===================================="
  runSwitchScenarios
  runLockSetChecks
  runAffinityAlgebraChecks
  IO.println "===================================="
  IO.println "All SM5.B per-core switchToThread checks PASS."

end SeLe4n.Testing.SmpSwitchToThread

def main : IO Unit :=
  SeLe4n.Testing.SmpSwitchToThread.runSmpSwitchToThreadChecks

