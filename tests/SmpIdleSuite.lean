-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdleInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDispatch
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM5.E — Per-core idle thread test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.E
"Per-core idle threads" deliverable
(`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.5, §4.3, §5).

* **§1 Surface anchors** — every public SM5.E symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem
  (`idleThread_priority_zero`, `createIdleThread_cpuAffinity`,
  `chooseThreadOnCore_always_succeeds`, `idleThread_core_locality`, the enqueue
  preservation lemmas) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_idle_suite` exercises the actual
  `enqueueIdleThreadOnCore` + `chooseThreadOnCore` computation on concrete
  fixtures: empty core falls back to idle; after `enqueueIdleThreadOnCore` the
  selection picks the idle thread; a higher-priority user thread still outranks
  idle (priority-0 ⇒ no starvation); the idle thread is core-local (frame +
  affinity); the field lemmas; and the inventory partition counts.
-/

namespace SeLe4n.Testing.SmpIdle

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing
-- WS-SM SM5.E: `idleThreadId` now lives in `SeLe4n.Kernel.Scheduler.IdleThread`
-- (resolved via `open SeLe4n.Kernel`); only `createIdleThread` is still in `Boot`.
open SeLe4n.Platform.Boot (createIdleThread)

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM5.E public symbol resolves
-- ============================================================================

-- SM5.E.1 / SM5.E.2 idle definitions (recap from SM4.G, refined at SM5.E.2):
#check @idleThreadId
#check @createIdleThread

-- SM5.E.5 + companion field lemmas:
#check @idleThread_priority_zero
#check @createIdleThread_domain_zero
#check @createIdleThread_cpuAffinity
#check @createIdleThread_tid

-- SM5.E.3 enqueue op + frame / membership / preservation:
#check @enqueueIdleThreadOnCore
#check @enqueueIdleThreadOnCore_objects
#check @enqueueIdleThreadOnCore_scheduler
#check @enqueueIdleThreadOnCore_runQueueOnCore_self
#check @enqueueIdleThreadOnCore_runQueueOnCore_ne
#check @enqueueIdleThreadOnCore_activeDomainOnCore
#check @enqueueIdleThreadOnCore_currentOnCore
#check @enqueueIdleThreadOnCore_mem_runQueueOnCore_self
#check @enqueueIdleThreadOnCore_getTcb?_self
#check @enqueueIdleThreadOnCore_getTcb?_ne
#check @enqueueIdleThreadOnCore_preserves_objects_invExt
#check @enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed
#check @enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore

-- SM5.E.6 always-succeeds:
#check @idleThreadEnqueuedOnCore
#check @enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore
#check @chooseThreadOnCore_always_succeeds
#check @enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds

-- SM5.E.4 core locality:
#check @runQueueAffinityConsistentOnCore
#check @idleThread_core_locality
#check @idleThread_core_locality_of_enqueue

-- SM5.E idle-aware dispatcher (SM5.I seed): production defs + establishment.
-- Post-fold: idle dispatch lives in `scheduleEffectiveOnCore`'s `none` branch
-- (`idleFallbackOnCore`); `scheduleOrIdleOnCore` is the SM5.E name for it.
#check @idleDispatchableOnCore
#check @dispatchIdleOnCore
#check @idleFallbackOnCore
#check @scheduleOrIdleOnCore
#check @scheduleOrIdleOnCore_runs_idle
#check @scheduleOrIdleOnCore_establishes_currentThreadValidOnCore
#check @scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore
#check @scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore
#check @scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed
#check @scheduleOrIdleOnCore_preserves_objects_invExt
#check @scheduleDomainOnCore_runs_idle

-- SM5.E inventory:
#check @perCoreIdleTheorems
#check @perCoreIdleTheorems_count
#check @perCoreIdleTheorems_partition_sum
#check @perCoreIdleTheorems_identifiers_nodup

-- ============================================================================
-- §2  Elaboration-time examples (Tier-3): apply each headline theorem
-- ============================================================================

-- SM5.E.5: the idle thread is priority 0.
example (c : CoreId) : (createIdleThread c).priority = ⟨0⟩ := idleThread_priority_zero c

-- SM5.E.2: the idle thread is pinned to its own core.
example (c : CoreId) : (createIdleThread c).cpuAffinity = some c := createIdleThread_cpuAffinity c

-- SM5.E.6: when idle is enqueued + in-domain, selection succeeds.
example (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hIdle : idleThreadEnqueuedOnCore st c) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  chooseThreadOnCore_always_succeeds st c hwf hRunnable hIdle

-- SM5.E.6: the discharge predicate is satisfiable via `enqueueIdleThreadOnCore`.
example (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hDom : st.scheduler.activeDomainOnCore c = ⟨0⟩) :
    idleThreadEnqueuedOnCore (enqueueIdleThreadOnCore st c) c :=
  enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore st c hInv hDom

-- SM5.E.6: end-to-end — enqueuing idle on a boot-domain state makes selection succeed.
example (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hDom : st.scheduler.activeDomainOnCore c = ⟨0⟩) :
    ∃ tid, chooseThreadOnCore (enqueueIdleThreadOnCore st c) c = .ok (some tid) :=
  enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds st c hInv hwf hRunnable hDom

-- SM5.E.4: affinity-based core locality — idle `c` is never on another core's queue.
example (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hIdleTcb : st.getTcb? (idleThreadId c) = some (createIdleThread c))
    (hAff : runQueueAffinityConsistentOnCore st c') :
    idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList :=
  idleThread_core_locality st c c' h hIdleTcb hAff

-- SM5.E.4: frame-based core locality — the enqueue does not leak idle `c` to `c'`.
example (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hAbsent : idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList) :
    idleThreadId c ∉ ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c').toList :=
  idleThread_core_locality_of_enqueue st c c' h hAbsent

-- SM5.E.3: enqueuing idle preserves the runnable-are-TCBs invariant.
example (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hr : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore (enqueueIdleThreadOnCore st c) c :=
  enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore st c hInv hr

-- SM5.E.3: the idle thread is a run-queue member after the enqueue.
example (st : SystemState) (c : CoreId) :
    idleThreadId c ∈ ((enqueueIdleThreadOnCore st c).scheduler.runQueueOnCore c).toList :=
  enqueueIdleThreadOnCore_mem_runQueueOnCore_self st c

-- SM5.E (dispatcher headline, post-fold): when the budget-aware selector goes idle
-- (`chooseThreadEffectiveOnCore = .ok none`) and idle is dispatchable on the
-- context-saved state, the folded `scheduleEffectiveOnCore` runs the idle thread.
example (st st'' : SystemState) (c : CoreId)
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none)
    (hDisp : idleDispatchableOnCore (saveOutgoingContextOnCore st c) c = true)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    st''.scheduler.currentOnCore c = some (idleThreadId c) :=
  scheduleOrIdleOnCore_runs_idle st c st'' hChoose hDisp hStep

-- SM5.E (dispatcher soundness): the idle-aware dispatcher establishes current-thread
-- validity, dequeue-on-dispatch consistency, current-in-domain, runnable-are-TCBs,
-- run-queue well-formedness, and the object-store invariant (parity with
-- `scheduleEffectiveOnCore`).
example (st st'' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    currentThreadValidOnCore st'' c :=
  scheduleOrIdleOnCore_establishes_currentThreadValidOnCore st c st'' hInv hStep

example (st st'' : SystemState) (c : CoreId)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    queueCurrentConsistentOnCore st''.scheduler c :=
  scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore st c st'' hStep

example (st st'' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    currentThreadInActiveDomainOnCore st'' c :=
  scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore st c st'' hInv hStep

example (st st'' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hr : runnableThreadsAreTCBsOnCore st c)
    (hStep : scheduleOrIdleOnCore st c = .ok st'') :
    runnableThreadsAreTCBsOnCore st'' c :=
  scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore st c st'' hInv hr hStep

-- SM5.E (strong no-starvation, post-fold): under the idle-dispatch precondition
-- (`chooseThreadEffectiveOnCore = .ok none`), every run-queue thread is
-- out-of-domain or out-of-budget — idle preempts no eligible user thread of any
-- priority.
example (st : SystemState) (c : CoreId)
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none)
    (tid : SeLe4n.ThreadId) (htid : tid ∈ (st.scheduler.runQueueOnCore c).toList)
    (tcb : TCB) (htcb : st.getTcb? tid = some tcb) :
    ¬(tcb.domain = st.scheduler.activeDomainOnCore c ∧ hasSufficientBudget st tcb = true) :=
  scheduleOrIdleOnCore_idle_starves_no_eligible_thread st c hChoose tid htid tcb htcb

-- SM5.E (live-wiring witness, review #4 closure): the folded idle dispatch is
-- reachable on the live per-core domain-tick path (`scheduleDomainOnCore`).
example (st st'' : SystemState) (c : CoreId)
    (hBoundary : st.scheduler.domainTimeRemainingOnCore c ≤ 1)
    (hSched : st.scheduler.domainSchedule = [])
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none)
    (hDisp : idleDispatchableOnCore (saveOutgoingContextOnCore st c) c = true)
    (hStep : scheduleDomainOnCore st c = .ok st'') :
    st''.scheduler.currentOnCore c = some (idleThreadId c) :=
  scheduleDomainOnCore_runs_idle st c st'' hBoundary hSched hChoose hDisp hStep

-- ============================================================================
-- §3  Runtime assertions (Tier-2): concrete `enqueueIdleThreadOnCore` + selection
-- ============================================================================

/-- Minimal user TCB at `tid`, priority `prio`, scheduling domain `dom`. -/
private def mkUserTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- Core 1 — a non-boot core, used for the cross-core locality scenarios. -/
private def core1 : CoreId := ⟨1, by decide⟩
private def tidUser : SeLe4n.ThreadId := ThreadId.ofNat 100

/-- Empty boot state: no objects, empty run queues, active domain `⟨0⟩`. -/
private def stEmpty : SystemState := BootstrapBuilder.empty.build

/-- The empty boot state with the **boot core's** idle thread enqueued. -/
private def stEmptyIdle : SystemState := enqueueIdleThreadOnCore stEmpty bootCoreId

/-- A boot state whose boot-core run queue holds a higher-priority (10) user
thread. -/
private def stUser : SystemState :=
  ((BootstrapBuilder.empty.withObject tidUser.toObjId (.tcb (mkUserTcb 100 10 0))).withRunnable
    [tidUser]).build

/-- `stUser` with the boot core's idle thread *also* enqueued (priority 0). -/
private def stUserIdle : SystemState := enqueueIdleThreadOnCore stUser bootCoreId

/-- The empty boot state with **core 1's** idle thread enqueued. -/
private def stCore1Idle : SystemState := enqueueIdleThreadOnCore stEmpty core1

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1: SM5.E.1 / .2 / .5 idle field facts. -/
private def runFieldChecks : IO Unit := do
  IO.println "--- §3.1 SM5.E.1/.2/.5 idle field facts ---"
  assertBool "SM5.E.5: idle thread is priority 0"
    (decide ((createIdleThread bootCoreId).priority = ⟨0⟩))
  assertBool "idle thread is in domain 0 (boot active domain)"
    (decide ((createIdleThread bootCoreId).domain = ⟨0⟩))
  assertBool "SM5.E.2: idle thread is pinned to its own core (cpuAffinity = some bootCoreId)"
    (decide ((createIdleThread bootCoreId).cpuAffinity = some bootCoreId))
  assertBool "SM5.E.1: idle thread ids are distinct across cores"
    (decide (idleThreadId bootCoreId ≠ idleThreadId core1))

/-- §3.2: SM5.E.6 — an empty core falls back to idle; after `enqueueIdleThreadOnCore`
the selection picks the idle thread. -/
private def runAlwaysSucceedsChecks : IO Unit := do
  IO.println "--- §3.2 SM5.E.6 chooseThreadOnCore_always_succeeds ---"
  assertBool "empty boot-core run queue ⇒ idle-fallback signal (.ok none)"
    (decide (chooseThreadOnCoreIdleFallback stEmpty bootCoreId))
  assertBool "after enqueue: idle thread IS a member of the boot-core run queue"
    (decide (idleThreadId bootCoreId ∈ (stEmptyIdle.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "after enqueue: idle resolves to a TCB in the object store"
    (decide (stEmptyIdle.getTcb? (idleThreadId bootCoreId)).isSome)
  assertBool "after enqueue: chooseThreadOnCore SELECTS the idle thread"
    (decide (chooseThreadOnCoreSelects stEmptyIdle bootCoreId (idleThreadId bootCoreId)))
  assertBool "after enqueue: selection is no longer the idle-fallback signal"
    (!decide (chooseThreadOnCoreIdleFallback stEmptyIdle bootCoreId))

/-- §3.3: SM5.E.5 — priority-0 idle never starves a higher-priority thread. -/
private def runNoStarvationChecks : IO Unit := do
  IO.println "--- §3.3 SM5.E.5 priority-0 idle never starves a runnable user thread ---"
  -- The boot-core run queue holds both the priority-10 user thread and the
  -- priority-0 idle thread; selection picks the user thread.
  assertBool "user thread (prio 10) is selected over idle (prio 0)"
    (decide (chooseThreadOnCoreSelects stUserIdle bootCoreId tidUser))
  assertBool "idle (prio 0) is NOT selected while a higher-priority thread is runnable"
    (!decide (chooseThreadOnCoreSelects stUserIdle bootCoreId (idleThreadId bootCoreId)))
  assertBool "idle is still present in the run queue (available as fallback)"
    (decide (idleThreadId bootCoreId ∈ (stUserIdle.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "the user thread is still present in the run queue"
    (decide (tidUser ∈ (stUserIdle.scheduler.runQueueOnCore bootCoreId).toList))

/-- §3.4: SM5.E.4 — per-core idle locality (frame + affinity + cross-core). -/
private def runLocalityChecks : IO Unit := do
  IO.println "--- §3.4 SM5.E.4 idle_core_locality ---"
  -- Frame: enqueuing the boot core's idle thread does NOT add it to core 1's queue.
  assertBool "boot-core idle thread is NOT on core 1's run queue (frame locality)"
    (!decide (idleThreadId bootCoreId ∈ (stEmptyIdle.scheduler.runQueueOnCore core1).toList))
  -- Affinity: idle bootCore is admitted on bootCore but not on core 1.
  assertBool "idle bootCore is admitted on its own core"
    (decide (affinityAdmitsCore (createIdleThread bootCoreId) bootCoreId = true))
  assertBool "idle bootCore is NOT admitted on core 1 (affinity = some bootCoreId)"
    (decide (affinityAdmitsCore (createIdleThread bootCoreId) core1 = false))
  -- Cross-core symmetry: core 1's own idle thread is enqueued on core 1, selected
  -- by core 1's scheduler, and absent from the boot core's queue.
  assertBool "core 1 selects its OWN idle thread"
    (decide (chooseThreadOnCoreSelects stCore1Idle core1 (idleThreadId core1)))
  assertBool "core 1's idle thread is NOT on the boot core's run queue"
    (!decide (idleThreadId core1 ∈ (stCore1Idle.scheduler.runQueueOnCore bootCoreId).toList))
  assertBool "the boot core (empty) still falls back to idle when only core 1 has its idle thread"
    (decide (chooseThreadOnCoreIdleFallback stCore1Idle bootCoreId))

/-- A boot state with the boot core's idle thread *installed* (object store) but
nothing runnable — the idle-aware dispatcher's exercise state. -/
private def stIdleInstalled : SystemState :=
  (BootstrapBuilder.empty.withObject (idleThreadId bootCoreId).toObjId
    (.tcb (createIdleThread bootCoreId))).build

/-- An idle slot holding a TCB BOUND TO ANOTHER CORE (`cpuAffinity := some core1`)
— the review-#3 affinity-hardening probe.  Its domain matches the boot active
domain, so a domain-only gate would (wrongly) admit it as core 0's idle thread; the
`affinityAdmitsCore` conjunct of `idleDispatchableOnCore` rejects it. -/
private def stForeignIdle : SystemState :=
  (BootstrapBuilder.empty.withObject (idleThreadId bootCoreId).toObjId
    (.tcb { createIdleThread bootCoreId with cpuAffinity := some core1 })).build

/-- The current thread after the per-core idle-aware dispatcher runs. -/
private def dispatchedCurrent (st : SystemState) (c : CoreId) : Option SeLe4n.ThreadId :=
  match SeLe4n.Kernel.scheduleOrIdleOnCore st c with
  | .ok s => s.scheduler.currentOnCore c
  | .error _ => none

/-- §3.6: the SM5.E idle-aware dispatcher (`scheduleOrIdleOnCore`) — idle is
genuinely dispatched in a production transition. -/
private def runDispatcherChecks : IO Unit := do
  IO.println "--- §3.6 SM5.E idle-aware dispatcher (scheduleOrIdleOnCore) ---"
  -- Idle installed + in-domain ⇒ dispatchable; idle absent ⇒ not dispatchable.
  assertBool "idle is dispatchable on the idle-installed boot state"
    (decide (idleDispatchableOnCore stIdleInstalled bootCoreId = true))
  assertBool "idle is NOT dispatchable when no idle thread is installed"
    (decide (idleDispatchableOnCore stEmpty bootCoreId = false))
  -- review #3: a slot-TCB bound to another core is NOT dispatchable as core 0's idle
  -- (its domain matches, so only the affinity gate rejects it).
  assertBool "a remote-bound TCB at the idle slot is NOT dispatchable (affinity gate)"
    (decide (idleDispatchableOnCore stForeignIdle bootCoreId = false))
  assertBool "the remote-bound idle slot dispatches to current = none (fallback)"
    (decide (dispatchedCurrent stForeignIdle bootCoreId = none))
  -- The idle-aware dispatcher runs the idle thread (current = some idleThreadId).
  assertBool "idle-aware dispatcher runs the idle thread (current = some idleThreadId)"
    (decide (dispatchedCurrent stIdleInstalled bootCoreId = some (idleThreadId bootCoreId)))
  -- For the same state the legacy single-core `schedule` goes to current = none.
  assertBool "legacy single-core schedule leaves current = none (idle not dispatched)"
    (decide ((match SeLe4n.Kernel.schedule stIdleInstalled with
              | .ok (_, s) => s.scheduler.currentOnCore bootCoreId
              | .error _ => some (idleThreadId bootCoreId)) = none))
  -- Without an idle thread installed the dispatcher falls back to current = none.
  assertBool "dispatcher falls back to current = none when no idle thread is installed"
    (decide (dispatchedCurrent stEmpty bootCoreId = none))
  -- Dequeue-on-dispatch: the dispatched idle thread is not in the run queue.
  assertBool "dispatched idle is absent from the run queue (dequeue-on-dispatch)"
    (match SeLe4n.Kernel.scheduleOrIdleOnCore stIdleInstalled bootCoreId with
     | .ok s => !(s.scheduler.runQueueOnCore bootCoreId).toList.any (· == idleThreadId bootCoreId)
     | .error _ => false)

/-- §3.7: the SM5.E.3 `enqueueIdleThreadOnCore` lock-set witnesses. -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.7 SM5.E.3 enqueueIdleThreadOnCore lock-set ---"
  assertBool "idle-enqueue footprint has the two cross-domain locks (length 2)"
    (decide ((enqueueIdleThreadOnCoreLockSet bootCoreId).length = 2))
  assertBool "idle-enqueue footprint is write-only"
    (decide ((enqueueIdleThreadOnCoreLockSet bootCoreId).all (fun p => p.2 == AccessMode.write)))
  assertBool "idle-enqueue footprint contains the object-store write lock"
    (decide ((SchedLockId.object schedObjStoreLockId, AccessMode.write)
              ∈ enqueueIdleThreadOnCoreLockSet bootCoreId))
  assertBool "idle-enqueue footprint acquires object-store before run-queue (§4.4)"
    (decide (SchedLockId.object schedObjStoreLockId
              < SchedLockId.runQueue (⟨bootCoreId⟩ : RunQueueLockId)))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.8 SM5.E theorem inventory ---"
  assertBool "inventory has 64 entries"
    (decide (perCoreIdleTheorems.length = 64))
  assertBool "field category has 6 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .field)).length = 6))
  assertBool "enqueue category has 13 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .enqueue)).length = 13))
  assertBool "preservation category has 5 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .preservation)).length = 5))
  assertBool "lockSet category has 8 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .lockSet)).length = 8))
  assertBool "alwaysSucceeds category has 7 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .alwaysSucceeds)).length = 7))
  assertBool "locality category has 6 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .locality)).length = 6))
  assertBool "dispatch category has 19 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .dispatch)).length = 19))
  assertBool "inventory identifiers are duplicate-free"
    (decide (perCoreIdleTheorems.map (·.identifier)).Nodup)

def runSmpIdleChecks : IO Unit := do
  IO.println "WS-SM SM5.E — Per-core idle thread suite"
  IO.println "===================================="
  runFieldChecks
  runAlwaysSucceedsChecks
  runNoStarvationChecks
  runLocalityChecks
  runDispatcherChecks
  runLockSetChecks
  runInventoryChecks
  IO.println "===================================="
  IO.println "All SM5.E per-core idle thread checks PASS."

end SeLe4n.Testing.SmpIdle

def main : IO Unit :=
  SeLe4n.Testing.SmpIdle.runSmpIdleChecks

