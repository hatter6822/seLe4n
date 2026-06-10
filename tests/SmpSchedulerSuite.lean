-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrt
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.K.1 — Aggregate SMP per-core scheduler suite

The acceptance-gate aggregate suite for WS-SM Phase SM5
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §8): a **4-thread workload
distributed across 4 cores**, exercising the full SM5 per-core scheduler surface
end-to-end on a single deterministic fixture.

The fixture `stFourCore` binds one user thread to each of the 4 RPi5 cores
(thread A→core 0, B→core 1, C→core 2, D→core 3) with distinct priorities, each in
its own per-core run queue.  The 50+ runtime scenarios cover:

* **§1** per-core selection — each core selects its own bound thread, and never a
  thread bound to a different core (`chooseThreadOnCore`, SM5.A);
* **§2** cross-core independence — mutating one core's run queue frames every other
  core's selection (SM5.A.3);
* **§3** affinity admission — each thread is admitted only on its bound core
  (`affinityAdmitsCore`, SM5.B.4);
* **§4** wake routing — `determineTargetCore` routes each thread to its bound core,
  and `wakeThread` emits a cross-core `.reschedule` SGI iff the target is remote
  (SM5.C);
* **§5** switch — `switchToThreadOnCore` sets the per-core current thread and rejects
  a remote-bound target (SM5.B.1/.4);
* **§6** WCRT under fine locks — each core's op footprints are within the RPi5
  `maxLockSetSize · 3 · tCs` bound (SM5.J);
* **§7** idle fallback — an empty core with its idle thread enqueued never stalls
  (SM5.E / SM5.J.4);
* **§8** the **multi-step dynamic simulation** — concurrent two-core dispatch
  threaded through the state, then a full cross-core wake → `.reschedule` SGI →
  target-core-handler round-trip on a genuinely blocked thread, with cross-core
  framing observed across the four transitions (SM5.K.1 completion);
* **§9** the **deterministic 4-core scheduler trace** (including the §8 round-trip's
  wake-SGI + handler-dispatch lines) verified byte-for-byte against the
  `tests/fixtures/smp_4core_scheduler.expected` golden fixture (SM5.K.4).

`lake exe smp_scheduler_suite` runs all scenarios; a scheduling-logic regression
flips a decidable check or diverges the golden trace.
-/

namespace SeLe4n.Testing.SmpScheduler

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- The deterministic 4-core / 4-thread fixture
-- ============================================================================

/-- The four RPi5 cores. -/
private def c0 : CoreId := bootCoreId
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩
private def c3 : CoreId := ⟨3, by decide⟩

/-- The four user threads, one bound to each core. -/
private def tA : SeLe4n.ThreadId := ThreadId.ofNat 100
private def tB : SeLe4n.ThreadId := ThreadId.ofNat 101
private def tC : SeLe4n.ThreadId := ThreadId.ofNat 102
private def tD : SeLe4n.ThreadId := ThreadId.ofNat 103

/-- A user TCB at `tid`, priority `prio`, domain `dom`, bound to core `aff`. -/
private def mkTcb (tid prio dom : Nat) (aff : CoreId) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0, cpuAffinity := some aff }

/-- The 4-core / 4-thread workload: all four threads in the object store (domain 0),
each in its **own** core's run queue, each bound to that core via `cpuAffinity`. -/
private def stFourCore : SystemState :=
  let base := ((((BootstrapBuilder.empty.withObject tA.toObjId (.tcb (mkTcb 100 10 0 c0))).withObject
    tB.toObjId (.tcb (mkTcb 101 20 0 c1))).withObject
    tC.toObjId (.tcb (mkTcb 102 15 0 c2))).withObject
    tD.toObjId (.tcb (mkTcb 103 25 0 c3))).build
  { base with scheduler :=
      ((((base.scheduler.setRunQueueOnCore c0 (RunQueue.ofList [(tA, ⟨10⟩)])).setRunQueueOnCore
        c1 (RunQueue.ofList [(tB, ⟨20⟩)])).setRunQueueOnCore
        c2 (RunQueue.ofList [(tC, ⟨15⟩)])).setRunQueueOnCore
        c3 (RunQueue.ofList [(tD, ⟨25⟩)])) }

/-- `stFourCore` with core 0's run queue emptied and its idle thread enqueued — the
SM5.J.4 / SM5.E no-stall fixture (core 0 has no user thread but must not stall). -/
private def stCore0Idle : SystemState :=
  let emptied := { stFourCore with scheduler := stFourCore.scheduler.setRunQueueOnCore c0 (RunQueue.ofList []) }
  enqueueIdleThreadOnCore emptied c0

-- ============================================================================
-- Decidable trace/label helpers
-- ============================================================================

/-- Human label for a thread id (stable across `ThreadId` internals). -/
private def threadLabel (t : SeLe4n.ThreadId) : String :=
  if t == tA then "thread A" else if t == tB then "thread B"
  else if t == tC then "thread C" else if t == tD then "thread D" else "thread ?"

/-- The label of the thread core `c` selects on state `st` (or the idle/error case).
The per-core idle thread is recognised explicitly so the no-stall fallback reads as
"the idle thread" rather than an anonymous id. -/
private def selLabel (st : SystemState) (c : CoreId) : String :=
  match chooseThreadOnCore st c with
  | .ok (some t) => if t == idleThreadId c then "the idle thread" else threadLabel t
  | .ok none     => "idle-fallback"
  | .error _     => "selection-error"

/-- The SGI a wake of `tid` (executing on `executing`) emits, as a label. -/
private def wakeSgiLabel (st : SystemState) (tid : SeLe4n.ThreadId) (executing : CoreId) : String :=
  match (wakeThread st tid executing).2 with
  | some (tgt, _) => s!"SGI reschedule to core {tgt.val}"
  | none          => "no SGI (local)"

/-- The label of the per-core current thread after `switchToThreadOnCore`. -/
private def switchCurrentLabel (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) : String :=
  match switchToThreadOnCore st c tid with
  | .ok st' => match st'.scheduler.currentOnCore c with
               | some t => threadLabel t
               | none   => "none"
  | .error _ => "switch-error"

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

-- ============================================================================
-- §1  Per-core selection — each core selects its own bound thread
-- ============================================================================

private def runSelectionScenarios : IO Unit := do
  IO.println "--- §1 per-core selection (4-thread / 4-core workload) ---"
  assertBool "core 0 selects its bound thread A" (decide (chooseThreadOnCoreSelects stFourCore c0 tA))
  assertBool "core 1 selects its bound thread B" (decide (chooseThreadOnCoreSelects stFourCore c1 tB))
  assertBool "core 2 selects its bound thread C" (decide (chooseThreadOnCoreSelects stFourCore c2 tC))
  assertBool "core 3 selects its bound thread D" (decide (chooseThreadOnCoreSelects stFourCore c3 tD))
  -- Each core selects only its OWN thread — never a thread bound to another core.
  assertBool "core 0 does NOT select B (bound to core 1)" (!decide (chooseThreadOnCoreSelects stFourCore c0 tB))
  assertBool "core 0 does NOT select C (bound to core 2)" (!decide (chooseThreadOnCoreSelects stFourCore c0 tC))
  assertBool "core 0 does NOT select D (bound to core 3)" (!decide (chooseThreadOnCoreSelects stFourCore c0 tD))
  assertBool "core 3 does NOT select A (bound to core 0)" (!decide (chooseThreadOnCoreSelects stFourCore c3 tA))
  -- All four cores schedule a thread (no core stalls on the full workload).
  assertBool "core 0 makes a selection (not idle-fallback)" (!decide (chooseThreadOnCoreIdleFallback stFourCore c0))
  assertBool "core 1 makes a selection (not idle-fallback)" (!decide (chooseThreadOnCoreIdleFallback stFourCore c1))
  assertBool "core 2 makes a selection (not idle-fallback)" (!decide (chooseThreadOnCoreIdleFallback stFourCore c2))
  assertBool "core 3 makes a selection (not idle-fallback)" (!decide (chooseThreadOnCoreIdleFallback stFourCore c3))

-- ============================================================================
-- §2  Cross-core independence — mutating one core frames the others
-- ============================================================================

/-- `stFourCore` with core 1's run queue swapped to hold thread A's id at a new
priority — used to witness that core 1's mutation frames cores 0/2/3. -/
private def stMutatedCore1 : SystemState :=
  { stFourCore with scheduler := stFourCore.scheduler.setRunQueueOnCore c1 (RunQueue.ofList [(tA, ⟨5⟩)]) }

private def runIndependenceScenarios : IO Unit := do
  IO.println "--- §2 cross-core independence (mutate core 1, frame 0/2/3) ---"
  -- Core 1's selection changes (now resolves tA via core 1's queue) ...
  assertBool "core 1's selection changed after its run-queue mutation"
    (!decide (chooseThreadOnCoreSelects stMutatedCore1 c1 tB))
  -- ... but cores 0/2/3 are completely unaffected (same selection as before).
  assertBool "core 0 still selects A after core 1's mutation (frame)"
    (decide (chooseThreadOnCoreSelects stMutatedCore1 c0 tA))
  assertBool "core 2 still selects C after core 1's mutation (frame)"
    (decide (chooseThreadOnCoreSelects stMutatedCore1 c2 tC))
  assertBool "core 3 still selects D after core 1's mutation (frame)"
    (decide (chooseThreadOnCoreSelects stMutatedCore1 c3 tD))
  -- The per-core run queues are genuinely distinct slots.
  assertBool "core 0's run queue is unchanged by core 1's mutation"
    (decide ((stMutatedCore1.scheduler.runQueueOnCore c0).toList = (stFourCore.scheduler.runQueueOnCore c0).toList))
  assertBool "core 2's run queue is unchanged by core 1's mutation"
    (decide ((stMutatedCore1.scheduler.runQueueOnCore c2).toList = (stFourCore.scheduler.runQueueOnCore c2).toList))

-- ============================================================================
-- §3  Affinity admission — each thread is admitted only on its bound core
-- ============================================================================

private def runAffinityScenarios : IO Unit := do
  IO.println "--- §3 affinity admission (each thread admitted only on its core) ---"
  assertBool "A is admitted on core 0 (its bound core)" (decide (affinityAdmitsCore (mkTcb 100 10 0 c0) c0 = true))
  assertBool "A is NOT admitted on core 1" (decide (affinityAdmitsCore (mkTcb 100 10 0 c0) c1 = false))
  assertBool "A is NOT admitted on core 2" (decide (affinityAdmitsCore (mkTcb 100 10 0 c0) c2 = false))
  assertBool "A is NOT admitted on core 3" (decide (affinityAdmitsCore (mkTcb 100 10 0 c0) c3 = false))
  assertBool "B is admitted on core 1 (its bound core)" (decide (affinityAdmitsCore (mkTcb 101 20 0 c1) c1 = true))
  assertBool "B is NOT admitted on core 0" (decide (affinityAdmitsCore (mkTcb 101 20 0 c1) c0 = false))
  assertBool "C is admitted on core 2 (its bound core)" (decide (affinityAdmitsCore (mkTcb 102 15 0 c2) c2 = true))
  assertBool "D is admitted on core 3 (its bound core)" (decide (affinityAdmitsCore (mkTcb 103 25 0 c3) c3 = true))

-- ============================================================================
-- §4  Wake routing — determineTargetCore + cross-core SGI emission
-- ============================================================================

private def runWakeScenarios : IO Unit := do
  IO.println "--- §4 wake routing (determineTargetCore + cross-core SGI) ---"
  -- determineTargetCore routes each thread to its bound core.
  assertBool "determineTargetCore A = core 0" (decide (determineTargetCore stFourCore tA = c0))
  assertBool "determineTargetCore B = core 1" (decide (determineTargetCore stFourCore tB = c1))
  assertBool "determineTargetCore C = core 2" (decide (determineTargetCore stFourCore tC = c2))
  assertBool "determineTargetCore D = core 3" (decide (determineTargetCore stFourCore tD = c3))
  -- Waking a remote-bound thread from core 0 emits a cross-core .reschedule SGI.
  assertBool "wake D from core 0 emits SGI to core 3 (remote)"
    (match (wakeThread stFourCore tD c0).2 with | some (tgt, k) => tgt == c3 && k == SgiKind.reschedule | none => false)
  assertBool "wake C from core 0 emits SGI to core 2 (remote)"
    (match (wakeThread stFourCore tC c0).2 with | some (tgt, _) => tgt == c2 | none => false)
  -- Waking a locally-bound thread (executing on its own core) emits NO SGI.
  assertBool "wake A from core 0 emits no SGI (target = executing core)"
    (match (wakeThread stFourCore tA c0).2 with | none => true | some _ => false)
  assertBool "wake B from core 1 emits no SGI (target = executing core)"
    (match (wakeThread stFourCore tB c1).2 with | none => true | some _ => false)

-- ============================================================================
-- §5  Switch — set per-core current, reject remote-bound target
-- ============================================================================

private def runSwitchScenarios : IO Unit := do
  IO.println "--- §5 switch (set per-core current, reject remote) ---"
  assertBool "switch core 1 to B succeeds and sets current(core 1) = B"
    (match switchToThreadOnCore stFourCore c1 tB with
     | .ok st' => st'.scheduler.currentOnCore c1 == some tB | .error _ => false)
  assertBool "switch core 2 to C succeeds and sets current(core 2) = C"
    (match switchToThreadOnCore stFourCore c2 tC with
     | .ok st' => st'.scheduler.currentOnCore c2 == some tC | .error _ => false)
  -- Switching a thread bound to a DIFFERENT core is rejected (Theorem 3.2.3).
  assertBool "switch core 0 to B (bound to core 1) is rejected (.error)"
    (match switchToThreadOnCore stFourCore c0 tB with | .error _ => true | .ok _ => false)
  assertBool "switch core 3 to A (bound to core 0) is rejected (.error)"
    (match switchToThreadOnCore stFourCore c3 tA with | .error _ => true | .ok _ => false)
  -- A switch frames the OTHER cores' current thread (cross-core independence).
  assertBool "switch core 1 to B leaves core 2's current unchanged"
    (match switchToThreadOnCore stFourCore c1 tB with
     | .ok st' => st'.scheduler.currentOnCore c2 == stFourCore.scheduler.currentOnCore c2 | .error _ => false)

-- ============================================================================
-- §6  WCRT under fine locks — each core's op footprints within the RPi5 bound
-- ============================================================================

private def runWcrtScenarios : IO Unit := do
  IO.println "--- §6 WCRT under fine locks (SM5.J RPi5 bound per core) ---"
  -- tCs = 60 (µs): chooseThread = 360, switch = 360, wake = 360, timer = 540, replenish = 180.
  assertBool "core 0 chooseThread lock-WCRT = 360 (= 2·3·60)"
    (decide (WCRT_lockSet (chooseThreadOnCoreLockSet c0) 60 = 360))
  assertBool "core 3 timerTick lock-WCRT = 540 (= 3·3·60)"
    (decide (WCRT_lockSet (timerTickOnCoreLockSet c3) 60 = 540))
  assertBool "core 2 wake lock-WCRT = 360 (= 2·3·60)"
    (decide (WCRT_lockSet (wakeThreadLockSet c2) 60 = 360))
  -- Every per-core op is within the RPi5 maxLockSetSize·3·tCs = 1440 bound.
  assertBool "core 1 switch lock-WCRT ≤ RPi5 bound (1440)"
    (decide (WCRT_lockSet (switchToThreadOnCoreLockSet c1) 60 ≤ maxLockSetSize * (3 * 60)))
  assertBool "core 3 timerTick lock-WCRT ≤ RPi5 bound (1440)"
    (decide (WCRT_lockSet (timerTickOnCoreLockSet c3) 60 ≤ maxLockSetSize * (3 * 60)))
  -- A typical syscall (≤ 4 locks) fits the 1 ms (1000 µs) timer-tick budget.
  assertBool "typical 4-lock syscall WCRT (720 µs) < 1 ms tick budget (1000 µs)"
    (decide (4 * (3 * 60) < 1000))

-- ============================================================================
-- §7  Idle fallback — an empty core with idle enqueued never stalls
-- ============================================================================

private def runIdleScenarios : IO Unit := do
  IO.println "--- §7 idle fallback (no core stalls — SM5.E / SM5.J.4) ---"
  assertBool "core 0 (emptied) with idle enqueued: idle is an in-domain candidate"
    (decide (idleAvailableOnCoreB stCore0Idle c0 = true))
  assertBool "core 0 (emptied) with idle enqueued: selects the idle thread (no stall)"
    (decide (chooseThreadOnCoreSelects stCore0Idle c0 (idleThreadId c0)))
  assertBool "core 0 (emptied) with idle enqueued: selection succeeds (.ok some)"
    (match chooseThreadOnCore stCore0Idle c0 with | .ok (some _) => true | _ => false)
  -- The idle thread does not leak onto the other cores' run queues.
  assertBool "core 0's idle thread is NOT on core 1's run queue (locality)"
    (!decide (idleThreadId c0 ∈ (stCore0Idle.scheduler.runQueueOnCore c1).toList))
  -- The other cores still schedule their own threads (idle is only a core-0 fallback).
  assertBool "core 1 still selects B while core 0 idles"
    (decide (chooseThreadOnCoreSelects stCore0Idle c1 tB))

-- ============================================================================
-- §8  Multi-step dynamic simulation (concurrent dispatch + cross-core round-trip)
-- ============================================================================

/-- A fifth thread `E` (priority 30, bound to core 3) that is **blocked** — present
in the object store but in no run queue — used by the cross-core wake round-trip.
Added only to `stWithBlocked` (a derived state), so the §9 golden trace computed
from `stFourCore` is unaffected. -/
private def tE : SeLe4n.ThreadId := ThreadId.ofNat 104

/-- `stFourCore` plus the blocked thread `E` in the object store (no run-queue entry).
`chooseThreadOnCore` / `determineTargetCore` on A–D are unchanged (E is in no queue). -/
private def stWithBlocked : SystemState :=
  { stFourCore with objects := stFourCore.objects.insert tE.toObjId (.tcb (mkTcb 104 30 0 c3)) }

/-- §8: a genuine multi-step run — concurrent two-core dispatch threaded through the
state, then a full cross-core wake → `.reschedule` SGI → target-core handler
round-trip, observing the evolving per-core state across four transitions. -/
private def runDynamicSimulation : IO Unit := do
  IO.println "--- §8 multi-step dynamic simulation (concurrent dispatch + cross-core round-trip) ---"
  match switchToThreadOnCore stWithBlocked c0 tA with
  | .error _ => assertBool "step 1: core 0 dispatches A (succeeds)" false
  | .ok st1 =>
    assertBool "step 1: core 0 dispatches A ⇒ current(core 0) = A"
      (st1.scheduler.currentOnCore c0 == some tA)
    match switchToThreadOnCore st1 c1 tB with
    | .error _ => assertBool "step 2: core 1 dispatches B (succeeds)" false
    | .ok st2 =>
      -- Genuine concurrent multi-core execution: BOTH cores run their own thread at once.
      assertBool "step 2: core 1 dispatches B ⇒ current(core 1) = B AND current(core 0) STILL = A"
        (st2.scheduler.currentOnCore c1 == some tB && st2.scheduler.currentOnCore c0 == some tA)
      -- Step 3: cross-core wake — E (blocked, bound core 3) is woken from core 0.
      let (st3, sgi) := wakeThread st2 tE c0
      assertBool "step 3: wake E (bound core 3) from core 0 ⇒ .reschedule SGI to core 3"
        (match sgi with | some (tgt, k) => tgt == c3 && k == SgiKind.reschedule | none => false)
      assertBool "step 3: E is now runnable on core 3's run queue (was blocked)"
        (decide (tE ∈ (st3.scheduler.runQueueOnCore c3).toList))
      assertBool "step 3: E was NOT runnable before the wake (genuinely blocked)"
        (!decide (tE ∈ (st2.scheduler.runQueueOnCore c3).toList))
      -- Step 4: target core 3 handles the reschedule SGI ⇒ dispatches the woken E.
      match handleRescheduleSgiOnCore st3 c3 with
      | .error _ => assertBool "step 4: core 3 handles the reschedule SGI (succeeds)" false
      | .ok st4 =>
        assertBool "step 4: core 3's handler dispatches E (prio 30, the highest in its queue)"
          (st4.scheduler.currentOnCore c3 == some tE)
        -- The handler on core 3 frames the OTHER cores' dispatched threads (independence).
        assertBool "step 4: core 3's handler frames core 0's current (still A)"
          (st4.scheduler.currentOnCore c0 == some tA)
        assertBool "step 4: core 3's handler frames core 1's current (still B)"
          (st4.scheduler.currentOnCore c1 == some tB)

/-- The §8 round-trip chain computed **once** (dispatch A on core 0 → dispatch B on
core 1 → wake blocked E from core 0 → handle the SGI on core 3): the emitted SGI
paired with the target-core handler's outcome.  Single source of truth for the §9
golden trace's round-trip labels (`none` = a dispatch step failed; the inner
`Except` = the handler's own outcome). -/
private def roundTripOutcome :
    Option (Option (CoreId × SgiKind) × Except KernelError SystemState) :=
  match switchToThreadOnCore stWithBlocked c0 tA with
  | .error _ => none
  | .ok st1 =>
    match switchToThreadOnCore st1 c1 tB with
    | .error _ => none
    | .ok st2 =>
      let (st3, sgi) := wakeThread st2 tE c0
      some (sgi, handleRescheduleSgiOnCore st3 c3)

/-- The label of the SGI the §8 round-trip's wake emits. -/
private def roundTripSgiLabel : String :=
  match roundTripOutcome with
  | some (some (tgt, _), _) => s!"SGI reschedule to core {tgt.val}"
  | some (none, _)          => "no SGI (local)"
  | none                    => "dispatch-error"

/-- The label of core 3's current thread after the §8 round-trip's SGI handler. -/
private def roundTripDispatchLabel : String :=
  match roundTripOutcome with
  | some (_, .ok st4) =>
      match st4.scheduler.currentOnCore c3 with
      | some t => if t == tE then "thread E" else threadLabel t
      | none   => "none"
  | some (_, .error _) => "handler-error"
  | none               => "dispatch-error"

-- ============================================================================
-- §9  The deterministic 4-core scheduler trace (SM5.K.4 golden fixture)
-- ============================================================================

/-- The deterministic 4-core scheduler trace — each line is COMPUTED from the actual
`chooseThreadOnCore` / `determineTargetCore` / `wakeThread` / `switchToThreadOnCore`
decisions on `stFourCore`, so a scheduling-logic regression diverges the golden
fixture.  Every line carries the `[smp-4core]` prefix (the fixture extraction key). -/
private def fourCoreTraceLines : List String :=
  [ s!"[smp-4core] core 0 selects {selLabel stFourCore c0}"
  , s!"[smp-4core] core 1 selects {selLabel stFourCore c1}"
  , s!"[smp-4core] core 2 selects {selLabel stFourCore c2}"
  , s!"[smp-4core] core 3 selects {selLabel stFourCore c3}"
  , s!"[smp-4core] determineTargetCore A = core {(determineTargetCore stFourCore tA).val}"
  , s!"[smp-4core] determineTargetCore B = core {(determineTargetCore stFourCore tB).val}"
  , s!"[smp-4core] determineTargetCore C = core {(determineTargetCore stFourCore tC).val}"
  , s!"[smp-4core] determineTargetCore D = core {(determineTargetCore stFourCore tD).val}"
  , s!"[smp-4core] wake D from core 0 emits {wakeSgiLabel stFourCore tD c0}"
  , s!"[smp-4core] wake A from core 0 emits {wakeSgiLabel stFourCore tA c0}"
  , s!"[smp-4core] switch core 1 to B sets current = {switchCurrentLabel stFourCore c1 tB}"
  , s!"[smp-4core] core 0 emptied with idle enqueued selects {selLabel stCore0Idle c0}"
  -- The multi-step cross-core round-trip (§8): wake blocked E onto core 3, then the
  -- target-core handler dispatches it — the dynamic counterpart of the snapshot above.
  , s!"[smp-4core] round-trip: wake blocked E from core 0 emits {roundTripSgiLabel}"
  , s!"[smp-4core] round-trip: core 3 handler dispatches current = {roundTripDispatchLabel}" ]

private def fixturePath : String := "tests/fixtures/smp_4core_scheduler.expected"

/-- §9: print the deterministic 4-core trace and verify it byte-for-byte against the
golden fixture.  The lines print before the (strict) verification, so the fixture is
regenerable via `lake exe smp_scheduler_suite | grep '^\[smp-4core\]'` (the brackets
MUST be escaped — unescaped they form a regex character class that also matches the
suite's `---` section headers, corrupting the regenerated fixture). -/
private def runTraceFixtureCheck : IO Unit := do
  IO.println "--- §9 deterministic 4-core scheduler trace (SM5.K.4 fixture) ---"
  for l in fourCoreTraceLines do
    IO.println l
  let expectedContent := String.intercalate "\n" fourCoreTraceLines ++ "\n"
  let fixtureExists ← System.FilePath.pathExists fixturePath
  if !fixtureExists then
    IO.println s!"  FAIL: golden fixture {fixturePath} not found"
    IO.println s!"        regenerate: lake exe smp_scheduler_suite | grep '^\\[smp-4core\\]' > {fixturePath}"
    throw (IO.userError s!"missing fixture {fixturePath}")
  let actual ← IO.FS.readFile fixturePath
  if actual == expectedContent then
    IO.println s!"  PASS: 4-core scheduler trace matches golden fixture {fixturePath}"
  else
    IO.println s!"  FAIL: 4-core scheduler trace differs from golden fixture {fixturePath}"
    IO.println s!"        the live trace is printed above; regenerate the golden fixture with:"
    IO.println s!"          lake exe smp_scheduler_suite | grep '^\\[smp-4core\\]' > {fixturePath}"
    IO.println s!"          (then refresh {fixturePath}.sha256 — see tests/fixtures/README.md)"
    throw (IO.userError "4-core scheduler trace fixture mismatch")

def main : IO Unit := do
  IO.println "=== WS-SM SM5.K.1 — Aggregate SMP per-core scheduler suite (4 threads / 4 cores) ==="
  runSelectionScenarios
  runIndependenceScenarios
  runAffinityScenarios
  runWakeScenarios
  runSwitchScenarios
  runWcrtScenarios
  runIdleScenarios
  runDynamicSimulation
  runTraceFixtureCheck
  IO.println "=== SM5.K.1 suite: all scenarios passed ==="

end SeLe4n.Testing.SmpScheduler

def main : IO Unit := SeLe4n.Testing.SmpScheduler.main
