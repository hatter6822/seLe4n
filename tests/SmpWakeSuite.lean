-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.C — Cross-core wake via SGI test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.C
"Cross-core wake via SGI" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.3, §4.4, §5).

* **§1 Surface anchors** — every public SM5.C symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (SGI emission,
  target-run-queue membership, losslessness, the SGI handler, the affinity op,
  the latency bound) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_wake_suite` exercises the actual
  `wakeThread` / `enqueueRunnableOnCore` / `handleRescheduleSgiOnCore` /
  `setThreadCpuAffinity` computations on the SM5.C.12 cross-core wake round-trip
  scenarios: determine-target, enqueue + make-ready, local vs remote wake (SGI
  emission), cross-core independence, the full wake→SGI→handle round-trip,
  affinity control, plus the SM5.C.3 lock-set and SM5.C.11 latency-bound
  witnesses.
-/

namespace SeLe4n.Testing.SmpWake

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.C public symbol resolves
-- ============================================================================

-- SM5.C.1/.2/.5/.8 production transitions (Scheduler.Operations.Selection):
#check @enqueueRunnableOnCore
#check @determineTargetCore
#check @wakeThread
#check @handleRescheduleSgiOnCore
#check @setThreadCpuAffinity

-- SM5.C.3 lock-sets:
#check @wakeThreadLockSet
#check @wakeThreadLockSet_length
#check @wakeThreadLockSet_write_only
#check @wakeThreadLockSet_contains_objStore_write
#check @wakeThreadLockSet_contains_runQueue_write
#check @wakeThreadLockSet_object_before_runQueue
#check @wakeThreadLockSet_keys_nodup
#check @wakeThreadLockSet_pairwise_le
#check @handleRescheduleSgiOnCoreLockSet
#check @handleRescheduleSgiOnCoreLockSet_eq

-- SM5.C.9 determineTargetCore:
#check @determineTargetCore_bound_eq_affinity
#check @determineTargetCore_unbound_eq_bootCore
#check @determineTargetCore_no_tcb_eq_bootCore
#check @determineTargetCore_in_range

-- SM5.C.1 enqueueRunnableOnCore:
#check @enqueueRunnableOnCore_preserves_objects_invExt
#check @enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed
#check @enqueueRunnableOnCore_mem_runQueueOnCore
#check @enqueueRunnableOnCore_makes_ready
#check @enqueueRunnableOnCore_runQueueOnCore_ne
#check @enqueueRunnableOnCore_currentOnCore
#check @enqueueRunnableOnCore_getTcb?_ne
#check @enqueueRunnableOnCore_no_tcb_noop

-- SM5.C.2/.4/.10 wakeThread semantics:
#check @wakeThread_state_eq_enqueue
#check @wakeThread_emits_sgi_if_remote
#check @wakeThread_no_sgi_if_local
#check @wakeThread_sgi_is_reschedule
#check @wakeThread_target_runQueue_contains
#check @wakeThread_preserves_objects_invExt
#check @wakeThread_preserves_target_runQueue_wellFormed
#check @wakeThread_independent_of_other_core

-- SM5.C.6 losslessness:
#check @SchedStep
#check @SchedReachable
#check @SchedReachable.of_enqueue
#check @SchedReachable.trans
#check @wakeThread_lossless

-- SM5.C.5 SGI handler:
#check @handleRescheduleSgiOnCore_idle_when_none
#check @handleRescheduleSgiOnCore_eq_switch_of_choose_some
#check @handleRescheduleSgiOnCore_switches_current
#check @handleRescheduleSgiOnCore_preserves_objects_invExt
#check @handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed
#check @handleRescheduleSgiOnCore_independent_of_other_core

-- SM5.C.11 SGI delivery latency bound:
#check @wakeSgiCount
#check @wakeThread_emits_at_most_one_sgi
#check @rescheduleSgi_intid_eq_zero
#check @rescheduleSgi_lowest_intid
#check @sgiDeliveryLatencyBound
#check @sgiDeliveryLatencyBound_eq_zero

-- SM5.C.8 affinity-control op:
#check @setThreadCpuAffinity_ok_of_tcb
#check @setThreadCpuAffinity_error_of_no_tcb
#check @setThreadCpuAffinity_sets_affinity
#check @setThreadCpuAffinity_preserves_objects_invExt
#check @setThreadCpuAffinity_preserves_scheduler
#check @setThreadCpuAffinity_getTcb?_ne
#check @setThreadCpuAffinity_affects_determineTargetCore

-- SM5.C decidability witnesses:
#check @handleRescheduleSgiOnCoreSucceeds
#check @setThreadCpuAffinitySucceeds

-- SM5.C.4 SGI-emission typed wrappers (Concurrency.Runtime):
#check @coreIdTargetMask
#check @sgiIntidU8
#check @sendSgiToCore
#check @sendRescheduleSgi
#check @emitWakeSgi
#check @sendSgiToCore_eq_ffi
#check @sendRescheduleSgi_eq
#check @emitWakeSgi_none
#check @emitWakeSgi_some
#check @sgiIntidU8_reschedule
#check @coreIdTargetMask_bootCore

-- ============================================================================
-- §2  Elaboration-time examples: apply each headline theorem to verified inputs
-- ============================================================================

/-- SM5.C.4 / Thm 3.3.1: a remote wake emits a reschedule SGI to the target. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (h : determineTargetCore st tid ≠ executingCore) :
    (wakeThread st tid executingCore).2
      = some (determineTargetCore st tid, SgiKind.reschedule) :=
  wakeThread_emits_sgi_if_remote st tid executingCore h

/-- SM5.C.4: a local wake emits no SGI. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (h : determineTargetCore st tid = executingCore) :
    (wakeThread st tid executingCore).2 = none :=
  wakeThread_no_sgi_if_local st tid executingCore h

/-- SM5.C.10: the woken thread lands in the target core's run queue. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    tid ∈ ((wakeThread st tid executingCore).1.scheduler.runQueueOnCore
            (determineTargetCore st tid)).toList :=
  wakeThread_target_runQueue_contains st tid executingCore tcb hTcb

/-- SM5.C.6 / Thm 3.3.2: cross-core wake is lossless. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    ∃ futureState : SystemState,
      SchedReachable (wakeThread st tid executingCore).1 futureState ∧
      (futureState.scheduler.currentOnCore (determineTargetCore st tid) = some tid ∨
       tid ∈ (futureState.scheduler.runQueueOnCore (determineTargetCore st tid)).toList) :=
  wakeThread_lossless st tid executingCore tcb hTcb

/-- SM5.C.9: an unbound thread wakes onto the boot core. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hAff : tcb.cpuAffinity = none) :
    determineTargetCore st tid = bootCoreId :=
  determineTargetCore_unbound_eq_bootCore st tid tcb hTcb hAff

/-- SM5.C.5: a successful SGI-handler dispatch sets the chosen thread current. -/
example (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hc : chooseThreadOnCore st c = .ok (some tid))
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c = some tid :=
  handleRescheduleSgiOnCore_switches_current st c tid st' hc h

/-- SM5.C.8: setting affinity feeds the wake target. -/
example (st : SystemState) (targetTid : SeLe4n.ThreadId) (c : CoreId) (st' : SystemState)
    (tcb : TCB) (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (h : setThreadCpuAffinity st targetTid (some c) = .ok st') :
    determineTargetCore st' targetTid = c :=
  setThreadCpuAffinity_affects_determineTargetCore st targetTid c st' tcb hTcb hInv h

/-- SM5.C.3: the wake lock-set acquires the object lock before the run-queue lock. -/
example (target : CoreId) :
    SchedLockId.object schedObjStoreLockId
      < SchedLockId.runQueue (⟨target⟩ : RunQueueLockId) :=
  wakeThreadLockSet_object_before_runQueue target

/-- SM5.C.11: a wake emits at most one SGI. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    wakeSgiCount (wakeThread st tid executingCore).2 ≤ 1 :=
  wakeThread_emits_at_most_one_sgi st tid executingCore

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM5.C.12 cross-core wake scenarios
-- ============================================================================

/-- Minimal test TCB at `tid`, priority `prio`, scheduling domain `dom`. -/
private def mkTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

private def core1 : CoreId := ⟨1, by decide⟩

private def tidU : SeLe4n.ThreadId := ThreadId.ofNat 200   -- unbound
private def tidW : SeLe4n.ThreadId := ThreadId.ofNat 201   -- bound to core1
private def tidGhost : SeLe4n.ThreadId := ThreadId.ofNat 999 -- not a TCB

/-- Object store holds an unbound TCB `tidU` and a core1-bound TCB `tidW`; no run
queues populated and no current thread on any core. -/
private def stWake : SystemState :=
  ((BootstrapBuilder.empty.withObject tidU.toObjId (.tcb (mkTcb 200 10 0))).withObject
    tidW.toObjId (.tcb { mkTcb 201 10 0 with cpuAffinity := some core1 })).build

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- Bool membership test on a core's run queue (avoids `Decidable (· ∈ ·)` on
the `RunQueue`'s `Prop`-valued `Membership` by going through the `Bool`-valued
`RunQueue.contains`). -/
private def rqHas (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) : Bool :=
  (st.scheduler.runQueueOnCore c).contains tid

/-- Evaluate a Bool predicate on the post-wake state. -/
private def wakeStateAnd (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (p : SystemState → Bool) : Bool :=
  p (wakeThread st tid ec).1

/-- Evaluate a Bool predicate on the `.ok` SGI-handler post-state; `false` on error. -/
private def handlerOkAnd (st : SystemState) (c : CoreId) (p : SystemState → Bool) : Bool :=
  match handleRescheduleSgiOnCore st c with
  | .ok st' => p st'
  | .error _ => false

/-- §3.1 SM5.C.9: determine-target — affinity routing. -/
private def runDetermineTargetChecks : IO Unit := do
  IO.println "--- §3.1 SM5.C.9 determine-target ---"
  assertBool "unbound tidU wakes onto the boot core"
    (decide (determineTargetCore stWake tidU = bootCoreId))
  assertBool "core1-bound tidW wakes onto core 1"
    (decide (determineTargetCore stWake tidW = core1))
  assertBool "non-TCB ghost defaults to the boot core (fail-safe)"
    (decide (determineTargetCore stWake tidGhost = bootCoreId))

/-- §3.2 SM5.C.1: enqueue + make-ready + frame. -/
private def runEnqueueChecks : IO Unit := do
  IO.println "--- §3.2 SM5.C.1 enqueueRunnableOnCore ---"
  assertBool "tidU enqueued on the boot core"
    (rqHas (enqueueRunnableOnCore stWake bootCoreId tidU) bootCoreId tidU)
  assertBool "tidU made IPC-ready by the enqueue"
    (match (enqueueRunnableOnCore stWake bootCoreId tidU).getTcb? tidU with
     | some t => decide (t.ipcState = .ready)
     | none   => false)
  assertBool "enqueue on core 1 leaves the boot core's run queue empty (frame)"
    (!rqHas (enqueueRunnableOnCore stWake core1 tidW) bootCoreId tidW)
  assertBool "enqueue of a non-TCB ghost is a no-op (boot run queue stays empty)"
    (((enqueueRunnableOnCore stWake bootCoreId tidGhost).scheduler.runQueueOnCore bootCoreId).toList.isEmpty)

/-- §3.3 SM5.C.2/.4: local vs remote wake (SGI emission). -/
private def runWakeSgiChecks : IO Unit := do
  IO.println "--- §3.3 SM5.C.2/.4 wake SGI emission ---"
  -- Local wake: unbound tidU, executing on the boot core (target = boot core).
  assertBool "local wake (unbound, exec boot core) emits no SGI"
    (decide ((wakeThread stWake tidU bootCoreId).2 = none))
  assertBool "local wake enqueues tidU on the boot core"
    (wakeStateAnd stWake tidU bootCoreId (fun st' => rqHas st' bootCoreId tidU))
  -- Remote wake: core1-bound tidW, executing on the boot core (target = core 1).
  assertBool "remote wake (bound core1, exec boot core) emits a reschedule SGI to core 1"
    (decide ((wakeThread stWake tidW bootCoreId).2 = some (core1, SgiKind.reschedule)))
  assertBool "remote wake enqueues tidW on core 1"
    (wakeStateAnd stWake tidW bootCoreId (fun st' => rqHas st' core1 tidW))
  -- Local-to-affinity wake: core1-bound tidW, executing on core 1 (target = core 1).
  assertBool "local-to-affinity wake (bound core1, exec core1) emits no SGI"
    (decide ((wakeThread stWake tidW core1).2 = none))
  -- Cross-core independence: a remote wake to core 1 leaves the boot core untouched.
  assertBool "remote wake to core1 leaves the boot core's run queue untouched"
    (wakeStateAnd stWake tidW bootCoreId
      (fun st' => (st'.scheduler.runQueueOnCore bootCoreId).toList
                    == (stWake.scheduler.runQueueOnCore bootCoreId).toList))

/-- §3.4 SM5.C.5/.12: the full wake → SGI → handle round-trip. -/
private def runRoundTripChecks : IO Unit := do
  IO.println "--- §3.4 SM5.C.5/.12 wake → SGI → handle round-trip ---"
  -- Step 1: wake core1-bound tidW from the boot core → enqueued on core 1 + remote SGI.
  let st1 := (wakeThread stWake tidW bootCoreId).1
  assertBool "round-trip step 1: wake enqueues tidW on core 1"
    (rqHas st1 core1 tidW)
  assertBool "round-trip step 1: wake emits a reschedule SGI to core 1"
    (decide ((wakeThread stWake tidW bootCoreId).2 = some (core1, SgiKind.reschedule)))
  -- Step 2: core 1 handles the reschedule SGI → re-chooses tidW and switches to it.
  assertBool "round-trip step 2: core 1's SGI handler succeeds"
    (decide (handleRescheduleSgiOnCoreSucceeds st1 core1))
  assertBool "round-trip step 2: after handling, tidW is current on core 1"
    (handlerOkAnd st1 core1 (fun st2 => st2.scheduler.currentOnCore core1 == some tidW))
  assertBool "round-trip step 2: after handling, tidW is dequeued from core 1's run queue"
    (handlerOkAnd st1 core1 (fun st2 => !rqHas st2 core1 tidW))
  -- Idle handler: an empty run queue → no dispatch (current stays none, queue empty).
  assertBool "SGI handler on an empty run queue is idle (no current set, queue empty)"
    (handlerOkAnd stWake core1
      (fun st2 => (st2.scheduler.currentOnCore core1 == none)
                    && (st2.scheduler.runQueueOnCore core1).toList.isEmpty))

/-- §3.5 SM5.C.8: affinity-control op. -/
private def runAffinityOpChecks : IO Unit := do
  IO.println "--- §3.5 SM5.C.8 setThreadCpuAffinity ---"
  assertBool "setting tidU's affinity to core 1 succeeds"
    (decide (setThreadCpuAffinitySucceeds stWake tidU (some core1)))
  assertBool "after binding tidU to core 1, its wake target is core 1"
    (match setThreadCpuAffinity stWake tidU (some core1) with
     | .ok st' => decide (determineTargetCore st' tidU = core1)
     | .error _ => false)
  assertBool "after binding tidU to core 1, getTcb? reflects the affinity"
    (match setThreadCpuAffinity stWake tidU (some core1) with
     | .ok st' => match st'.getTcb? tidU with
                  | some t => decide (t.cpuAffinity = some core1)
                  | none   => false
     | .error _ => false)
  assertBool "setting affinity on a non-TCB ghost does not succeed"
    (!decide (setThreadCpuAffinitySucceeds stWake tidGhost (some core1)))
  assertBool "unbinding tidW (affinity none) re-targets it to the boot core"
    (match setThreadCpuAffinity stWake tidW none with
     | .ok st' => decide (determineTargetCore st' tidW = bootCoreId)
     | .error _ => false)

/-- §3.6 SM5.C.3: the wake / handler lock-set witnesses. -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.6 SM5.C.3 wake / handler lock-sets ---"
  assertBool "wakeThreadLockSet core1 has both domain locks (length 2)"
    (decide ((wakeThreadLockSet core1).length = 2))
  assertBool "wake footprint contains the object-store WRITE lock"
    (decide ((SchedLockId.object schedObjStoreLockId, AccessMode.write)
              ∈ wakeThreadLockSet core1))
  assertBool "wake footprint contains core 1's run-queue WRITE lock"
    (decide ((SchedLockId.runQueue ⟨core1⟩, AccessMode.write) ∈ wakeThreadLockSet core1))
  assertBool "wake footprint acquires the object lock before the run-queue lock (§4.4)"
    (decide (SchedLockId.object schedObjStoreLockId
              < SchedLockId.runQueue (⟨core1⟩ : RunQueueLockId)))
  assertBool "wake footprint keys are duplicate-free"
    (decide (((wakeThreadLockSet core1).map (·.1)).Nodup))
  assertBool "every core's wake footprint has both domain locks"
    (allCores.all (fun c => (wakeThreadLockSet c).length == 2))
  assertBool "the SGI-handler footprint coincides with the switch footprint"
    (decide (handleRescheduleSgiOnCoreLockSet core1 = switchToThreadOnCoreLockSet core1))

/-- §3.7 SM5.C.11: the SGI delivery latency-bound witnesses. -/
private def runLatencyChecks : IO Unit := do
  IO.println "--- §3.7 SM5.C.11 SGI delivery latency bound ---"
  assertBool "reschedule SGI maps to INTID 0"
    (decide (SgiKind.reschedule.toIntid.val = 0))
  assertBool "reschedule is the lowest-INTID (highest-priority) kernel SGI"
    (SgiKind.all.all (fun k => SgiKind.reschedule.toIntid.val ≤ k.toIntid.val))
  assertBool "kernel-SGI service-slot latency bound for reschedule is 0"
    (decide (sgiDeliveryLatencyBound = 0))
  assertBool "a remote wake emits at most one SGI"
    (decide (wakeSgiCount (wakeThread stWake tidW bootCoreId).2 ≤ 1))
  assertBool "a local wake emits zero SGIs"
    (decide (wakeSgiCount (wakeThread stWake tidU bootCoreId).2 = 0))
  assertBool "the reschedule SGI's INTID byte is 0 (sgiIntidU8)"
    (decide (sgiIntidU8 SgiKind.reschedule = 0))
  assertBool "the boot core's GIC target mask is bit 0 (= 1)"
    (decide (coreIdTargetMask bootCoreId = 1))
  assertBool "core 1's GIC target mask is bit 1 (= 2)"
    (decide (coreIdTargetMask core1 = 2))

def runSmpWakeChecks : IO Unit := do
  IO.println "WS-SM SM5.C — Cross-core wake via SGI suite"
  IO.println "===================================="
  runDetermineTargetChecks
  runEnqueueChecks
  runWakeSgiChecks
  runRoundTripChecks
  runAffinityOpChecks
  runLockSetChecks
  runLatencyChecks
  IO.println "===================================="
  IO.println "All SM5.C cross-core wake checks PASS."

end SeLe4n.Testing.SmpWake

def main : IO Unit :=
  SeLe4n.Testing.SmpWake.runSmpWakeChecks
