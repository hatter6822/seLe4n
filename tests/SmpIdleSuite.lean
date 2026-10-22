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
import SeLe4n.Testing.InvariantChecks
import SeLe4n.Testing.BootCoreOps

/-!
# WS-SM SM5.E — Per-core idle thread test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM5.E
"Per-core idle threads" deliverable
(WS-SM SM5 §3.5, §4.3, §5).

* **§1 Surface anchors** — every public SM5.E symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem
  (`idleThread_priority_zero`, `createIdleThread_cpuAffinity`,
  `scheduleEffectiveOnCore_current_isSome`, `idleThread_core_locality`, the
  store preservation lemmas) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_idle_suite` exercises the actual
  `storeIdleThreadOnCore` + scheduling-point computation on concrete fixtures:
  the store queues nothing (seL4's posture: an idle thread is never queued); an
  empty core's scheduling point runs its idle thread from the selection
  fallback; a runnable user thread is dispatched instead of idle; the idle
  thread is core-local (frame + affinity); the field lemmas; and the inventory
  partition counts.
-/

namespace SeLe4n.Testing.SmpIdle

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing
-- WS-SM SM5.E / v0.35.68: `idleThreadId`, `createIdleThread` and `readyIdleThread`
-- all live in `SeLe4n.Kernel.Scheduler.IdleThread` (resolved via `open SeLe4n.Kernel`);
-- the store primitive lives in `SeLe4n.Kernel.Scheduler.Operations.IdleStore`.

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

-- SM5.E.3 store op + frames / preservation:
#check @storeIdleThreadOnCore
#check @storeIdleThreadOnCore_scheduler
#check @storeIdleThreadOnCore_runQueueOnCore
#check @storeIdleThreadOnCore_activeDomainOnCore
#check @storeIdleThreadOnCore_currentOnCore
#check @storeIdleThreadOnCore_objects_self
#check @storeIdleThreadOnCore_objects_ne
#check @storeIdleThreadOnCore_getTcb?_self
#check @storeIdleThreadOnCore_getTcb?_ne
#check @storeIdleThreadOnCore_runQueueRefined
#check @storeIdleThreadOnCore_preserves_objects_invExt
#check @storeIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore

-- SM5.E.6 no stall:
#check @scheduleEffectiveOnCore_current_isSome
#check @scheduleEffectiveOnCore_idle_only_when_none
#check @storeIdleThreadOnCore_idleDispatchableOnCore

-- WS-RR RR5.11/RR5.12: the boot-level idle store, its fold, and the
-- production boot state's discharge of the no-stall premise.
#check @SeLe4n.Platform.Boot.storeIdleThread
-- v0.35.68: the boot's idle install IS the kernel model's store -- one body.
-- `storeIdleThread_state` is definitional, and decisive: a second body in the
-- boot, however faithfully it mirrored `storeIdleThreadOnCore`, is not `rfl`
-- to it.  The four `IntermediateState` witnesses are the operation's own.
#check @SeLe4n.Platform.Boot.storeIdleThread_state
#check @storeIdleThreadOnCore_preserves_allTablesInvExtK
#check @storeIdleThreadOnCore_preserves_perObjectSlotsInvariant
#check @storeIdleThreadOnCore_preserves_perObjectMappingsInvariant
#check @storeIdleThreadOnCore_preserves_objectTypeMetadataConsistent
#check @storeIdleThreadOnCore_objectIndex_length_le
example (ist : SeLe4n.Model.IntermediateState) (c : CoreId) :
    (SeLe4n.Platform.Boot.storeIdleThread ist c).state = storeIdleThreadOnCore ist.state c :=
  SeLe4n.Platform.Boot.storeIdleThread_state ist c
#check @SeLe4n.Platform.Boot.storeIdleThread_scheduler
#check @SeLe4n.Platform.Boot.storeIdleThread_currentOnCore
#check @SeLe4n.Platform.Boot.storeIdleThread_activeDomainOnCore
#check @SeLe4n.Platform.Boot.storeIdleThread_objects_self
#check @SeLe4n.Platform.Boot.storeIdleThread_objects_ne
#check @SeLe4n.Platform.Boot.foldl_storeIdleThread_installs
#check @SeLe4n.Platform.Boot.foldl_storeIdleThread_scheduler
#check @SeLe4n.Platform.Boot.foldl_storeIdleThread_currentOnCore
#check @SeLe4n.Platform.Boot.foldl_storeIdleThread_objects_frame_of_not_idle
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_map_ok
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_rejects_invalid
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_isOk_iff
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_currentAllNone
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_idle_resident
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_preserves_platform_objects
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_scheduler_eq
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_not_mem_runQueueOnCore
-- PR #889 review: the stored idle TCB is the ready form, the boot state is
-- threadStateConsistent, and the checked boot reserves the idle slots.
#check @SeLe4n.Kernel.readyIdleThread
#check @SeLe4n.Kernel.readyIdleThread_threadState
#check @readyIdleThread_ne_createIdleThread
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_idle_threadState
#check @SeLe4n.Platform.Boot.bootFromPlatformChecked_ok_tcb_inactive
#check @SeLe4n.Platform.Boot.bootFromPlatformChecked_ok_threadStateConsistent
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_threadStateConsistent
#check @SeLe4n.Platform.Boot.idleSlotsReserved
#check @SeLe4n.Platform.Boot.idleSlotsReserved_no_idle_references
#check @SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
#check @SeLe4n.Kernel.capTargetsReservedIdleObject
#check @SeLe4n.Kernel.threadInactiveFlagConsistent
#check @SeLe4n.Kernel.threadStateConsistent_implies_threadInactiveFlagConsistent
-- WS-RR RR7.36: the preservation surface for the relation the live decisions
-- read, and the two predicates it is stated over.
#check @SeLe4n.Kernel.threadPlacedOnSomeCore
#check @SeLe4n.Kernel.inferThreadState_eq_inactive_iff
#check @SeLe4n.Kernel.threadPlacedOnSomeCore_eq_true_iff
#check @SeLe4n.Kernel.threadInactiveFlagConsistent_of_frame
#check @SeLe4n.Kernel.threadInactiveFlagConsistent_of_frame_placing
#check @SeLe4n.Kernel.threadInactiveFlagConsistent_congr
#check @SeLe4n.Kernel.threadInactiveFlagConsistent_dispatch
#check @SeLe4n.Kernel.preemptCurrentOnCore_preserves_threadInactiveFlagConsistent
#check @SeLe4n.Kernel.switchToThreadOnCore_preserves_threadInactiveFlagConsistent
-- ... and the identification RR7.36 made definitional: the classification's
-- placement tests ARE the cross-core wake's single-placement tests.
#check @SeLe4n.Kernel.threadRunningOnSomeCore_eq_runningOnSomeCore
#check @SeLe4n.Kernel.threadQueuedOnSomeCore_eq_runnableOnSomeCore
example : @SeLe4n.Kernel.threadRunningOnSomeCore = @SeLe4n.Kernel.runningOnSomeCore := rfl
example : @SeLe4n.Kernel.threadQueuedOnSomeCore = @SeLe4n.Kernel.runnableOnSomeCore := rfl
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_threadInactiveFlagConsistent
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor_allCores
#check @SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid
#check @SeLe4n.Platform.Boot.declaredWitnessesInstalled
#check @SeLe4n.Platform.PlatformBinding.declaredCores
#check @SeLe4n.Platform.PlatformBinding.declaredCores_eq_allCores_of_full
#check @SeLe4n.Platform.Boot.bootFromPlatformChecked_ok_shape
#check @SeLe4n.Platform.Boot.bootFromPlatformChecked_ok_idleSlotsFreshAt
#check @SeLe4n.Kernel.isIdleObjId
-- The preservation theorem takes no freshness hypothesis any more — a
-- signature pin (PR #889 review).
example (config : SeLe4n.Platform.Boot.PlatformConfig)
    (ist ist' : SeLe4n.Model.IntermediateState)
    (hChecked : SeLe4n.Platform.Boot.bootFromPlatformChecked config = .ok ist)
    (h : SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads config = .ok ist')
    (oid : SeLe4n.ObjId) (o : SeLe4n.Model.KernelObject)
    (hPlat : ist.state.objects[oid]? = some o) : ist'.state.objects[oid]? = some o :=
  SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_preserves_platform_objects
    config ist ist' hChecked h oid o hPlat
#check @SeLe4n.Platform.Boot.idleSlotsFreshAt_of_initialObjects_below_base
#check @bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore
#check @bootFromPlatformCheckedWithIdleThreads_scheduleEffectiveOnCore_current_isSome
-- WS-RR RR5.12 (audit): the payoff takes NO hypotheses beyond the boot — a
-- signature pin, so a hypothesis cannot be reintroduced without this line
-- failing to elaborate.
example (config : SeLe4n.Platform.Boot.PlatformConfig) (ist : SeLe4n.Model.IntermediateState)
    (h : SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads config = .ok ist)
    (c : CoreId) : idleDispatchableOnCore ist.state c = true :=
  bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore config ist h c

-- SM5.E.4 core locality:
#check @runQueueAffinityConsistentOnCore
#check @idleTcbResidentOnCore
#check @idleThread_core_locality
#check @idleThread_core_locality_of_store

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

-- SM5.E.6: when idle is dispatchable, a scheduling point leaves a current thread.
example (st st' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hIdle : idleDispatchableOnCore st c = true)
    (h : scheduleEffectiveOnCore st c = .ok st') :
    (st'.scheduler.currentOnCore c).isSome :=
  scheduleEffectiveOnCore_current_isSome hInv hIdle h

-- SM5.E.6: the premise is satisfiable via `storeIdleThreadOnCore`.
example (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hDom : st.scheduler.activeDomainOnCore c = ⟨0⟩) :
    idleDispatchableOnCore (storeIdleThreadOnCore st c) c = true :=
  storeIdleThreadOnCore_idleDispatchableOnCore st c hInv hDom

-- SM5.E.4: affinity-based core locality — idle `c` is never on another core's queue.
-- PR #889 review: the installed idle TCB is the stored form (`.Ready`), which
-- is what the store writes and what the locality theorem reads.
example (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hIdleTcb : idleTcbResidentOnCore st c)
    (hAff : runQueueAffinityConsistentOnCore st c') :
    idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList :=
  idleThread_core_locality st c c' h hIdleTcb hAff

-- SM5.E.3: storing idle preserves the runnable-are-TCBs invariant.
example (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hr : runnableThreadsAreTCBsOnCore st c) :
    runnableThreadsAreTCBsOnCore (storeIdleThreadOnCore st c) c :=
  storeIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore st c c hInv hr

-- SM5.E.3: the store writes no run queue — idle stays off every queue.
example (st : SystemState) (c c' : CoreId) :
    (storeIdleThreadOnCore st c).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' :=
  storeIdleThreadOnCore_runQueueOnCore st c c'

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
-- (`chooseThreadEffectiveOnCore = .ok none`) and the link agreement, every run-queue thread is
-- out-of-domain or out-of-budget — idle preempts no eligible user thread of any
-- priority.
example (st : SystemState) (c : CoreId) (hR : st.runQueueRefinedOnCore c)
    (hChoose : chooseThreadEffectiveOnCore st c = .ok none)
    (tid : SeLe4n.ThreadId) (htid : tid ∈ (st.scheduler.runQueueOnCore c).toList)
    (tcb : TCB) (htcb : st.getTcb? tid = some tcb) :
    ¬(tcb.domain = st.scheduler.activeDomainOnCore c ∧ hasSufficientBudget st tcb = true) :=
  scheduleOrIdleOnCore_idle_starves_no_eligible_thread st c hR hChoose tid htid tcb htcb

-- SM5.E (live-wiring witness, review #4 closure; restated for inert
-- single-domain mode at PR #880 round 4): the folded idle dispatch is
-- reachable on the live per-core domain-tick path — a rotating domain
-- boundary whose post-switch state has nothing budget-eligible adopts the
-- idle thread.  (In single-domain mode the domain tick is deliberately
-- inert — `scheduleDomainOnCore_singleDomain_inert` — and idle adoption
-- rides the wake receiver, the vacate-successor seam and the budget tick's
-- own re-dispatch fallback.)
example (st stMid st'' : SystemState) (c : CoreId)
    (hBoundary : st.scheduler.domainTimeRemainingOnCore c ≤ 1)
    (hSched : st.scheduler.domainSchedule ≠ [])
    (hSwitch : switchDomainOnCore st c = .ok stMid)
    (hChoose : chooseThreadEffectiveOnCore stMid c = .ok none)
    (hDisp : idleDispatchableOnCore (saveOutgoingContextOnCore stMid c) c = true)
    (hStep : scheduleDomainOnCore st c = .ok st'') :
    st''.scheduler.currentOnCore c = some (idleThreadId c) :=
  scheduleDomainOnCore_runs_idle st c stMid st'' hBoundary hSched hSwitch hChoose hDisp hStep

-- PR #880 round 4: single-domain mode is inert — the domain tick provably
-- cannot perturb scheduling on the RPi5 v1.0.0 default configuration.
example (st : SystemState) (c : CoreId)
    (hSched : st.scheduler.domainSchedule = []) :
    scheduleDomainOnCore st c = .ok st :=
  scheduleDomainOnCore_singleDomain_inert st c hSched

-- ============================================================================
-- §3  Runtime assertions (Tier-2): concrete `storeIdleThreadOnCore` + selection
-- ============================================================================

/-- Minimal user TCB at `tid`, priority `prio`, scheduling domain `dom`.

`threadState := .Ready` rather than the field's `.Inactive` default (WS-RR
RR7.36): every fixture below immediately enqueues this TCB, and a queued thread
whose stored flag reads `.Inactive` violates `threadInactiveFlagConsistent` —
the relation every live suspend/resume/cancel decision consults — so the default
would have built a state the kernel's own dispatch premise refuses.  The `.Inactive` spelling is
kept as the deliberate negative in §3.12. -/
private def mkUserTcb (tid : Nat) (prio : Nat) (dom : Nat) : TCB :=
  { tid := ThreadId.ofNat tid, priority := ⟨prio⟩, domain := ⟨dom⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf (ObjId.ofNat 0) (ObjId.ofNat 0),
    ipcBuffer := SeLe4n.VAddr.ofNat 0, threadState := .Ready }

/-- Core 1 — a non-boot core, used for the cross-core locality scenarios. -/
private def core1 : CoreId := ⟨1, by decide⟩
private def tidUser : SeLe4n.ThreadId := ThreadId.ofNat 100

/-- Empty boot state: no objects, empty run queues, active domain `⟨0⟩`. -/
private def stEmpty : SystemState := BootstrapBuilder.empty.build

/-- The empty boot state with the **boot core's** idle thread stored. -/
private def stEmptyIdle : SystemState := storeIdleThreadOnCore stEmpty bootCoreId

/-- A boot state whose boot-core run queue holds a higher-priority (10) user
thread. -/
private def stUser : SystemState :=
  ((BootstrapBuilder.empty.withObject tidUser.toObjId (.tcb (mkUserTcb 100 10 0))).withRunnable
    [tidUser]).build

/-- `stUser` with the boot core's idle thread *also* stored. -/
private def stUserIdle : SystemState := storeIdleThreadOnCore stUser bootCoreId

/-- The empty boot state with **core 1's** idle thread stored. -/
private def stCore1Idle : SystemState := storeIdleThreadOnCore stEmpty core1

/-- The current thread after the per-core idle-aware dispatcher runs. -/
private def dispatchedCurrent (st : SystemState) (c : CoreId) : Option SeLe4n.ThreadId :=
  match SeLe4n.Kernel.scheduleOrIdleOnCore st c with
  | .ok s => s.scheduler.currentOnCore c
  | .error _ => none

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

/-- §3.2: SM5.E.6 — the store queues nothing; an empty core's scheduling point
runs its idle thread from the selection fallback. -/
private def runNoStallChecks : IO Unit := do
  IO.println "--- §3.2 SM5.E.6 no core stalls: idle runs from the selection fallback ---"
  assertBool "empty boot-core run queue ⇒ idle-fallback signal (.ok none)"
    (idleFallbackByLinks stEmpty bootCoreId)
  assertBool "after the store: the idle thread is on NO run queue (seL4: idle is never queued)"
    (decide (stEmptyIdle.runQueueWalk bootCoreId = []))
  assertBool "after the store: idle resolves to a TCB in the object store"
    (decide (stEmptyIdle.getTcb? (idleThreadId bootCoreId)).isSome)
  assertBool "after the store: selection is still the idle-fallback signal"
    (idleFallbackByLinks stEmptyIdle bootCoreId)
  assertBool "after the store: idle is dispatchable"
    (decide (idleDispatchableOnCore stEmptyIdle bootCoreId = true))
  assertBool "after the store: the scheduling point runs the idle thread"
    (decide (dispatchedCurrent stEmptyIdle bootCoreId = some (idleThreadId bootCoreId)))

/-- §3.3: SM5.E.5 — idle never runs while an eligible thread is queued. -/
private def runNoStarvationChecks : IO Unit := do
  IO.println "--- §3.3 SM5.E.5 idle never starves a runnable user thread ---"
  assertBool "the user thread is selected"
    (selectsByLinks stUserIdle bootCoreId tidUser)
  assertBool "the scheduling point dispatches the user thread, not idle"
    (decide (dispatchedCurrent stUserIdle bootCoreId = some tidUser))
  assertBool "the run queue holds the user thread only (idle is not queued)"
    (decide (stUserIdle.runQueueWalk bootCoreId = [tidUser]))

/-- §3.4: SM5.E.4 — per-core idle locality (frame + affinity + cross-core). -/
private def runLocalityChecks : IO Unit := do
  IO.println "--- §3.4 SM5.E.4 idle_core_locality ---"
  -- Frame: storing the boot core's idle thread does NOT add it to core 1's queue.
  assertBool "boot-core idle thread is NOT on core 1's run queue (frame locality)"
    (!decide (idleThreadId bootCoreId ∈ (stEmptyIdle.runQueueWalk core1)))
  -- Affinity: idle bootCore is admitted on bootCore but not on core 1.
  assertBool "idle bootCore is admitted on its own core"
    (decide (affinityAdmitsCore (createIdleThread bootCoreId) bootCoreId = true))
  assertBool "idle bootCore is NOT admitted on core 1 (affinity = some bootCoreId)"
    (decide (affinityAdmitsCore (createIdleThread bootCoreId) core1 = false))
  -- Cross-core symmetry: core 1's own idle thread is dispatched by core 1's
  -- scheduling point and is not dispatchable on the boot core.
  assertBool "core 1 runs its OWN idle thread"
    (decide (dispatchedCurrent stCore1Idle core1 = some (idleThreadId core1)))
  assertBool "core 1's idle thread is NOT on the boot core's run queue"
    (!decide (idleThreadId core1 ∈ (stCore1Idle.runQueueWalk bootCoreId)))
  assertBool "the boot core (no idle stored) has no idle to dispatch"
    (decide (idleDispatchableOnCore stCore1Idle bootCoreId = false))

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
  -- The live scheduling point folds the idle dispatch in, so it agrees with the
  -- idle-aware dispatcher.  (The single-core reference `schedule`, which left
  -- current = none here, is proof-only since WS-ZA ZA4.5.)
  assertBool "live schedule runs the idle thread too (folded idle dispatch)"
    (decide ((match bootSchedule stIdleInstalled with
              | .ok (_, s) => s.scheduler.currentOnCore bootCoreId
              | .error _ => none) = some (idleThreadId bootCoreId)))
  -- Without an idle thread installed the dispatcher falls back to current = none.
  assertBool "dispatcher falls back to current = none when no idle thread is installed"
    (decide (dispatchedCurrent stEmpty bootCoreId = none))
  -- Dequeue-on-dispatch: the dispatched idle thread is not in the run queue.
  assertBool "dispatched idle is absent from the run queue (dequeue-on-dispatch)"
    (match SeLe4n.Kernel.scheduleOrIdleOnCore stIdleInstalled bootCoreId with
     | .ok s => !(s.runQueueWalk bootCoreId).any (· == idleThreadId bootCoreId)
     | .error _ => false)

/-- §3.7: the SM5.E.3 `storeIdleThreadOnCore` lock-set witnesses. -/
private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.7 SM5.E.3 storeIdleThreadOnCore lock-set ---"
  assertBool "idle-store footprint is the object-store lock alone (length 1)"
    (decide ((storeIdleThreadOnCoreLockSet bootCoreId).length = 1))
  assertBool "idle-store footprint is write-only"
    (decide ((storeIdleThreadOnCoreLockSet bootCoreId).all (fun p => p.2 == AccessMode.write)))
  assertBool "idle-store footprint contains the object-store write lock"
    (decide ((LockKey.objStore, AccessMode.write)
              ∈ storeIdleThreadOnCoreLockSet bootCoreId))
  assertBool "idle-store footprint takes no run-queue lock"
    (!(storeIdleThreadOnCoreLockSet bootCoreId).any (fun p => p.1 == LockKey.runQueue bootCoreId))

private def runInventoryChecks : IO Unit := do
  IO.println "--- §3.8 SM5.E theorem inventory ---"
  assertBool "inventory has 59 entries"
    (decide (perCoreIdleTheorems.length = 59))
  assertBool "field category has 6 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .field)).length = 6))
  assertBool "store category has 12 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .store)).length = 12))
  assertBool "preservation category has 5 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .preservation)).length = 5))
  assertBool "lockSet category has 5 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .lockSet)).length = 5))
  assertBool "noStall category has 6 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .noStall)).length = 6))
  assertBool "locality category has 6 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .locality)).length = 6))
  assertBool "dispatch category has 19 entries"
    (decide ((perCoreIdleTheorems.filter (fun t => t.category == .dispatch)).length = 19))
  assertBool "inventory identifiers are duplicate-free"
    (decide (perCoreIdleTheorems.map (·.identifier)).Nodup)

/-- **WS-RR RR5.12** (runtime): the *production* boot state discharges the
no-stall premise on every core, and the entry it replaced does not.

The negative half is the point of the test.  `bootFromPlatformChecked` — the
entry `Platform.FFI.bootAndInitialiseFromPlatform` ran until RR5.14 — installs
no idle TCB, so `idleDispatchableOnCore` was false on every core and
`schedulerNoStall_smp`'s `hIdle` had no reachable discharge. -/
private def runBootIdleChecks : IO Unit := do
  IO.println "--- WS-RR RR5.12: the production boot state discharges the no-stall premise ---"
  let cfg : SeLe4n.Platform.Boot.PlatformConfig := { irqTable := [], initialObjects := [] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads cfg with
  | .error e =>
      assertBool s!"the minimally well-formed config must boot (got: {e})" false
  | .ok ist =>
      for c in allCores do
        assertBool s!"core {c.val}: its idle thread resolves to THIS core's idle TCB"
          (match ist.state.getTcb? (idleThreadId c) with
           | some tcb =>
               decide (tcb.tid = idleThreadId c) && decide (tcb.domain = ⟨0⟩) &&
                 decide (tcb.cpuAffinity = some c) && decide (tcb.priority = ⟨0⟩)
           | none => false)
        -- PR #889 review: the STORED thread state is the one the classification
        -- infers — `.Ready` for an idle thread its core is not running.  The
        -- dispatched form (`createIdleThread`, `.Running`) would fail this on
        -- every core.
        assertBool s!"core {c.val}: its stored idle thread state is what the classification infers"
          (match ist.state.getTcb? (idleThreadId c) with
           | some tcb =>
               decide (tcb.threadState = ThreadState.Ready) &&
                 decide (tcb.threadState = inferThreadState ist.state (idleThreadId c) tcb)
           | none => false)
        assertBool s!"NEGATIVE core {c.val}: the dispatched idle form would NOT be consistent here"
          (decide ((createIdleThread c).threadState ≠
            inferThreadState ist.state (idleThreadId c) (createIdleThread c)))
        assertBool s!"core {c.val}: idle is in the core's active domain"
          (decide ((createIdleThread c).domain = ist.state.scheduler.activeDomainOnCore c))
        assertBool s!"core {c.val}: nothing is dispatched yet"
          (decide (ist.state.scheduler.currentOnCore c = none))
        -- seL4's posture: the idle thread is on NO run queue, this core's or any
        -- other's — the runtime face of
        -- `bootFromPlatformCheckedWithIdleThreads_not_mem_runQueueOnCore`.
        for c' in allCores do
          assertBool s!"core {c.val}: its idle thread is NOT on core {c'.val}'s queue"
            (decide (idleThreadId c ∉ (ist.state.runQueueWalk c')))
        assertBool s!"core {c.val}: its run queue is empty"
          (decide ((ist.state.runQueueWalk c) = []))
        -- ...so the core's first scheduling point runs its idle thread from the
        -- selection fallback (`bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore`).
        assertBool s!"core {c.val}: its idle thread is dispatchable"
          (decide (idleDispatchableOnCore ist.state c = true))
        assertBool s!"core {c.val}: its first scheduling point runs its own idle thread"
          (decide (dispatchedCurrent ist.state c = some (idleThreadId c)))
  match SeLe4n.Platform.Boot.bootFromPlatformChecked cfg with
  | .error e =>
      assertBool s!"the plain checked boot must also accept the config (got: {e})" false
  | .ok plain =>
      for c in allCores do
        assertBool
          s!"NEGATIVE core {c.val}: the pre-RR5.14 entry installs no idle TCB"
          (plain.state.getTcb? (idleThreadId c)).isNone
        assertBool
          s!"NEGATIVE core {c.val}: so its idle thread is not dispatchable"
          (decide (idleDispatchableOnCore plain.state c = false))

/-- PR #889 review round 2: the diagnostic the checked boot answers a config
that occupies or references a reserved idle slot with. -/
private def idleSlotDiagnostic : String :=
  SeLe4n.Platform.Boot.idleSlotReservationBootError

/-- PR #889 review rounds 7 and 8: the diagnostic the checked boot refuses a
config whose TCB, SchedContext or Reply entry is stored under an id other than
the one it carries with. -/
private def tcbIdentityDiagnostic : String :=
  SeLe4n.Platform.Boot.embeddedIdentityBootError

/-- **WS-RR RR5.13** (runtime): the idle entry adds no validation of its own —
it accepts and rejects exactly what `bootFromPlatformChecked` does. -/
private def runBootValidationParityChecks : IO Unit := do
  IO.println "--- WS-RR RR5.13: one validation path, not two ---"
  let malformed : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [ { irq := ⟨1⟩, handler := ⟨42⟩ }, { irq := ⟨1⟩, handler := ⟨43⟩ } ],
      initialObjects := [] }
  match SeLe4n.Platform.Boot.bootFromPlatformChecked malformed,
        SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads malformed with
  | .error ePlain, .error eIdle =>
      assertBool "a duplicate-IRQ config is refused with the SAME error by both entries"
        (ePlain == eIdle)
  | _, _ =>
      assertBool "a duplicate-IRQ config must be refused by both entries" false
  -- PR #889 review: a config that occupies an idle slot is refused on the one
  -- validation path — before, the checked boot accepted it and the idle fold
  -- silently overwrote the object.  The object is otherwise boot-safe (an
  -- idle notification), so the reservation is the only thing refusing it.
  let squatter : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := (idleThreadId ⟨0, by decide⟩).toObjId,
                            obj := .notification { state := .idle, 
                                                   hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero },
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  assertBool "NEGATIVE: an object at an idle slot fails the config validator"
    (SeLe4n.Platform.Boot.PlatformConfig.wellFormed squatter == false)
  assertBool "NEGATIVE: ...and specifically the idle-slot reservation"
    (SeLe4n.Platform.Boot.idleSlotsReserved squatter == false)
  match SeLe4n.Platform.Boot.bootFromPlatformChecked squatter,
        SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads squatter with
  | .error ePlain, .error eIdle =>
      assertBool "NEGATIVE: an idle-slot squatter is refused by both entries, with the same error"
        (ePlain == eIdle)
      -- PR #889 review round 2: the refusal names the reservation.  Before, the
      -- third `wellFormed` conjunct fell through to the duplicate-object
      -- diagnostic, which names a fault the config does not have.
      assertBool "NEGATIVE: ...and the diagnostic names the reservation, not a duplicate id"
        (ePlain == idleSlotDiagnostic)
  | _, _ =>
      assertBool "NEGATIVE: an idle-slot squatter must be refused by both entries" false
  -- PR #889 review round 2: a config that merely REFERENCES an idle slot is
  -- refused too — here a boot-safe TCB whose CSpace root is idle 0's object id.
  -- The idle fold would have materialised that dangling reference as the
  -- kernel's own idle TCB.  The same TCB naming a non-idle (and equally absent)
  -- root is accepted, so the refusal is the reservation and nothing else.
  let idle0Obj : SeLe4n.ObjId := (idleThreadId ⟨0, by decide⟩).toObjId
  let referrer (root : SeLe4n.ObjId) : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := ⟨5⟩,
                            obj := .tcb { tid := ⟨5⟩, priority := ⟨10⟩, domain := ⟨0⟩,
                                          spaceCells := SeLe4n.Model.TCB.spaceCellsOf root ⟨0⟩,
                                          ipcBuffer := SeLe4n.VAddr.ofNat 0,
                                          threadState := .Inactive },
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  assertBool "NEGATIVE: a TCB whose CSpace root is an idle slot fails the reservation"
    (SeLe4n.Platform.Boot.idleSlotsReserved (referrer idle0Obj) == false)
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads (referrer idle0Obj) with
  | .error e =>
      assertBool "NEGATIVE: ...and the checked boot refuses it with the reservation diagnostic"
        (e == idleSlotDiagnostic)
  | .ok _ =>
      assertBool "NEGATIVE: a config referencing an idle slot must be refused" false
  assertBool "the same TCB naming a non-idle root is accepted"
    (SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads (referrer ⟨9⟩)).toOption.isSome
  -- The reference predicate on the object kinds that hold authority: a CNode
  -- carrying a capability to an idle object references the slot; the same
  -- CNode carrying a capability to an ordinary object does not; and the
  -- capability predicate itself decides by target.
  let cnodeWith (target : SeLe4n.ObjId) : KernelObject :=
    .cnode (CNode.ofList 4 0 0 4 [ (SeLe4n.Slot.ofNat 0,
                  { target := .object target, rights := AccessRightSet.ofList [.write] }) ])
  assertBool "NEGATIVE: a boot CNode holding a capability to an idle TCB references the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (cnodeWith idle0Obj) == true)
  assertBool "a boot CNode holding a capability to an ordinary object does not"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (cnodeWith ⟨9⟩) == false)
  -- PR #889 review round 4: a boot notification pre-bound to an idle thread
  -- references the slot; bound to an ordinary thread it does not.
  let ntfnBoundTo (t : SeLe4n.ThreadId) : KernelObject :=
    .notification { state := .idle, 
                    hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero, boundTCBCode := SeLe4n.ThreadId.optCode (some t) }
  assertBool "NEGATIVE: a boot notification bound to an idle thread references the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
        (ntfnBoundTo (idleThreadId ⟨0, by decide⟩)) == true)
  assertBool "a boot notification bound to an ordinary thread does not"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (ntfnBoundTo ⟨9⟩) == false)
  let boundNtfnCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := ⟨6⟩, obj := ntfnBoundTo (idleThreadId ⟨0, by decide⟩),
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads boundNtfnCfg with
  | .error e =>
      assertBool "NEGATIVE: ...and the checked boot refuses it with the reservation diagnostic"
        (e == idleSlotDiagnostic)
  | .ok _ =>
      assertBool "NEGATIVE: a notification bound to an idle thread must be refused" false
  -- PR #889 review round 6: a boot untyped whose allocation record names an
  -- idle slot as a child, or whose ancestry names one as its parent,
  -- references the slot; ordinary records do not.
  let untypedWith (child : Option SeLe4n.ObjId) (parent : Option SeLe4n.ObjId) : KernelObject :=
    .untyped { regionBase := SeLe4n.PAddr.ofNat 0x1000_0000, regionSize := 0x1000,
               children := (child.map (fun c => ({ objId := c, offset := 0, size := 0x100 } :
                 UntypedChild))).toList,
               parent := parent }
  assertBool "NEGATIVE: a boot untyped recording an idle slot as a child references the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (untypedWith (some idle0Obj) none) == true)
  assertBool "NEGATIVE: a boot untyped recording an idle slot as its parent references the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (untypedWith none (some idle0Obj)) == true)
  assertBool "a boot untyped with ordinary records does not"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (untypedWith (some ⟨9⟩) (some ⟨8⟩)) == false)
  let untypedChildCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := ⟨7⟩, obj := untypedWith (some idle0Obj) none,
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads untypedChildCfg with
  | .error e =>
      assertBool "NEGATIVE: ...and the checked boot refuses it with the reservation diagnostic"
        (e == idleSlotDiagnostic)
  | .ok _ =>
      assertBool "NEGATIVE: an untyped recording an idle child must be refused" false
  -- PR #889 review round 7: a boot TCB's OWN identity.  Stored at an ordinary
  -- id with an idle thread's tid it references the slot through the one field
  -- the lifecycle paths read back (a retype of that object would dequeue the
  -- real idle thread); stored under any id but its own thread id it is refused
  -- for the identity relation itself; stored under its own id it is accepted.
  let tcbWithTid (t : SeLe4n.ThreadId) : TCB :=
    { tid := t, priority := ⟨10⟩, domain := ⟨0⟩, spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩,
      ipcBuffer := SeLe4n.VAddr.ofNat 0, threadState := .Inactive }
  let entryAt (id : Nat) (tcb : TCB) : SeLe4n.Platform.Boot.ObjectEntry :=
    { id := ⟨id⟩, obj := .tcb tcb,
      hSlots := fun _ h => KernelObject.noConfusion h,
      hMappings := fun _ h => KernelObject.noConfusion h }
  let idle0Tid : SeLe4n.ThreadId := idleThreadId ⟨0, by decide⟩
  assertBool "NEGATIVE: a boot TCB whose own tid is an idle thread's references the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (.tcb (tcbWithTid idle0Tid)) == true)
  let idleTidCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [entryAt 9 (tcbWithTid idle0Tid)] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads idleTidCfg with
  | .error e =>
      assertBool "NEGATIVE: ...and the checked boot refuses it with the reservation diagnostic"
        (e == idleSlotDiagnostic)
  | .ok _ =>
      assertBool "NEGATIVE: a TCB carrying an idle thread id at an ordinary slot must be refused" false
  let aliasCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [entryAt 9 (tcbWithTid ⟨7⟩)] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads aliasCfg with
  | .error e =>
      assertBool "NEGATIVE: a TCB stored under another thread's id is refused for the identity relation"
        (e == tcbIdentityDiagnostic)
  | .ok _ =>
      assertBool "NEGATIVE: a TCB whose tid is not its own slot must be refused" false
  let ownIdCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [entryAt 9 (tcbWithTid ⟨9⟩)] }
  assertBool "a TCB stored under its own thread id is accepted"
    (SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads ownIdCfg).toOption.isSome
  assertBool "tcbIdentitiesMatchSlots decides the identity relation entry by entry"
    (SeLe4n.Platform.Boot.tcbIdentitiesMatchSlots aliasCfg == false &&
     SeLe4n.Platform.Boot.tcbIdentitiesMatchSlots idleTidCfg == false &&
     SeLe4n.Platform.Boot.tcbIdentitiesMatchSlots ownIdCfg == true)
  -- PR #889 review round 15: a configured thread pinned to a core the BINDING
  -- does not declare.  The checked boot is binding-agnostic and cannot see it;
  -- `determineTargetCore` reads the affinity on the first resume or wake and
  -- enqueues the thread on a PE that does not exist.
  let pinnedTo (c : SeLe4n.Kernel.Concurrency.CoreId) : TCB :=
    { tcbWithTid ⟨9⟩ with cpuAffinity := some c }
  let core0 : SeLe4n.Kernel.Concurrency.CoreId := ⟨0, by decide⟩
  let core2 : SeLe4n.Kernel.Concurrency.CoreId := ⟨2, by decide⟩
  let pinnedCfg (c : SeLe4n.Kernel.Concurrency.CoreId) : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [entryAt 9 (pinnedTo c)] }
  assertBool "the affinity check reads the declared list, not the model's cores"
    (SeLe4n.Platform.Boot.bootAffinitiesDeclared [core0] (pinnedCfg core2) == false &&
     SeLe4n.Platform.Boot.bootAffinitiesDeclared [core0] (pinnedCfg core0) == true &&
     SeLe4n.Platform.Boot.bootAffinitiesDeclared [core0] ownIdCfg == true)
  assertBool "on the model's full core list every affinity is declared"
    (SeLe4n.Platform.Boot.bootAffinitiesDeclared SeLe4n.Kernel.Concurrency.allCores
      (pinnedCfg core2) == true)
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor [core0]
      (pinnedCfg core2) with
  | .error e =>
      assertBool "NEGATIVE: a single-core binding refuses a thread pinned to core 2"
        (e == SeLe4n.Platform.Boot.undeclaredAffinityBootError)
  | .ok _ =>
      assertBool "NEGATIVE: a thread pinned to an undeclared core must not boot" false
  assertBool "the same thread pinned to the declared core boots"
    (SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor [core0]
      (pinnedCfg core0)).toOption.isSome
  assertBool "an unpinned thread boots on a single-core binding"
    (SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor [core0]
      ownIdCfg).toOption.isSome
  assertBool "the all-cores production boot is unchanged by the affinity check"
    (SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads
      (pinnedCfg core2)).toOption.isSome
  -- PR #889 review round 8: the THIRD queue link.  `queuePPrev = some (.tcbNext t)`
  -- names thread `t`; the projection-based arm never read it, so a boot TCB
  -- carrying an idle thread there passed both the reservation and the
  -- boot-safety check.  The reservation now reads the payload, and the
  -- boot-safety check requires all three links empty.
  let linkedTo (t : SeLe4n.ThreadId) : TCB :=
    { tcbWithTid ⟨9⟩ with queuePPrevCode := QueuePPrev.optCode (some (.tcbNext t)) }
  assertBool "NEGATIVE: a boot TCB whose queuePPrev names an idle thread references the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (.tcb (linkedTo idle0Tid)) == true)
  assertBool "a queuePPrev naming an ordinary thread does not reference the slot"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot (.tcb (linkedTo ⟨7⟩)) == false &&
     SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.tcb { tcbWithTid ⟨9⟩ with queuePPrevCode := 1 }) == false)
  assertBool "NEGATIVE: ...but a boot TCB with ANY queuePPrev fails the boot-safety check"
    (SeLe4n.Platform.Boot.bootSafeObjectCheck (.tcb (linkedTo ⟨7⟩)) == false &&
     SeLe4n.Platform.Boot.bootSafeObjectCheck
       (.tcb { tcbWithTid ⟨9⟩ with queuePPrevCode := 1 }) == false &&
     SeLe4n.Platform.Boot.bootSafeObjectCheck (.tcb (tcbWithTid ⟨9⟩)) == true)
  -- WS-ZA ZA4.5: run-queue membership lives in the TCB, so a boot TCB naming a
  -- core claims a queue place the queue never gave it.
  assertBool "NEGATIVE: a boot TCB on a run queue fails the boot-safety check"
    (SeLe4n.Platform.Boot.bootSafeObjectCheck
       (.tcb { tcbWithTid ⟨9⟩ with runCoreCode := 1 }) == false)
  -- WS-ZA ZA4.5: a core list naming a core twice is refused before any idle
  -- thread is placed.
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor [core0, core0]
      ownIdCfg with
  | .error e =>
      assertBool "NEGATIVE: a core list naming a core twice is refused"
        (e == SeLe4n.Platform.Boot.duplicateBootCoreError)
  | .ok _ =>
      assertBool "NEGATIVE: a core list naming a core twice must not boot" false
  let idleLinkCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [entryAt 9 (linkedTo idle0Tid)] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads idleLinkCfg with
  | .error e =>
      assertBool "NEGATIVE: ...and the checked boot refuses it with the reservation diagnostic"
        (e == idleSlotDiagnostic)
  | .ok _ =>
      assertBool "NEGATIVE: a TCB whose queuePPrev names an idle thread must be refused" false
  -- Round 8 sweep (the arity pin): the fields the hand-written arms had never
  -- read — a TCB's reply references, a Reply's own id and `prev` link, a
  -- SchedContext's own id.  (A TCB's `pendingMessage` names no object: a
  -- message holds no capabilities.)
  let idleReplyId : SeLe4n.ReplyId := SeLe4n.ReplyId.ofNat idle0Obj.toNat
  assertBool "NEGATIVE: a boot TCB's reply references are read"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.tcb { tcbWithTid ⟨9⟩ with replyObjectCode := SeLe4n.ReplyId.optCode (some idleReplyId) }) == true &&
     SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.tcb { tcbWithTid ⟨9⟩ with pendingReceiveReplyCode := SeLe4n.ReplyId.optCode (some idleReplyId) }) == true)
  assertBool "NEGATIVE: a boot Reply's own id and its prev link are read"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.reply { replyId := idleReplyId }) == true &&
     SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.reply { replyId := ⟨9⟩, prev := some idleReplyId }) == true &&
     SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.reply { replyId := ⟨9⟩ }) == false)
  assertBool "NEGATIVE: a boot SchedContext's own id is read"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.schedContext (SchedContext.empty (SeLe4n.SchedContextId.ofNat idle0Obj.toNat))) == true &&
     SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.schedContext (SchedContext.empty ⟨9⟩)) == false)
  -- WS-OD OD2.1: `SchedContext.scReply` is a Reply **object id**, so the
  -- reservation reads it too; and a boot SchedContext may head no reply stack
  -- at all, because every admissible boot Reply is inert (`bootSafeReplyCheck`
  -- requires `Reply.isFree`: no caller and no stack link in either direction),
  -- so a config-supplied head could only dangle —
  -- a `donationChainWellFormed` violation installed before the first
  -- instruction runs.
  assertBool "NEGATIVE: a boot SchedContext's reply-stack head is read"
    (SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.schedContext { SchedContext.empty ⟨9⟩ with scReply := some idleReplyId }) == true &&
     SeLe4n.Platform.Boot.bootObjectReferencesReservedIdleSlot
       (.schedContext { SchedContext.empty ⟨9⟩ with scReply := some ⟨9⟩ }) == false)
  assertBool "NEGATIVE: ...and a boot SchedContext heading ANY reply stack fails boot safety"
    (SeLe4n.Platform.Boot.bootSafeObjectCheck
       (.schedContext { SchedContext.empty ⟨9⟩ with scReply := some ⟨9⟩ }) == false &&
     SeLe4n.Platform.Boot.bootSafeObjectCheck
       (.schedContext (SchedContext.empty ⟨9⟩)) == true)
  let stackHeadCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects :=
        [ { id := ⟨9⟩,
            obj := .schedContext { SchedContext.empty ⟨9⟩ with scReply := some ⟨9⟩ },
            hSlots := fun _ h => KernelObject.noConfusion h,
            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  assertBool "NEGATIVE: ...so the checked boot refuses a config SchedContext that heads a stack"
    ((SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads stackHeadCfg).toOption.isNone)
  -- Round 8: the identity relation covers every object that carries its own id.
  let scAliasCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := ⟨9⟩, obj := .schedContext (SchedContext.empty ⟨12⟩),
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  let replyAliasCfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := ⟨9⟩, obj := .reply { replyId := ⟨12⟩ },
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads scAliasCfg,
        SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads replyAliasCfg with
  | .error eSc, .error eReply =>
      assertBool "NEGATIVE: a SchedContext or a Reply stored under another id is refused for the identity relation"
        (eSc == tcbIdentityDiagnostic && eReply == tcbIdentityDiagnostic)
  | _, _ =>
      assertBool "NEGATIVE: a SchedContext or Reply whose id is not its own slot must be refused" false
  assertBool "embeddedIdentitiesMatchSlots decides the relation for all three kinds"
    (SeLe4n.Platform.Boot.embeddedIdentitiesMatchSlots scAliasCfg == false &&
     SeLe4n.Platform.Boot.schedContextIdentitiesMatchSlots scAliasCfg == false &&
     SeLe4n.Platform.Boot.embeddedIdentitiesMatchSlots replyAliasCfg == false &&
     SeLe4n.Platform.Boot.replyIdentitiesMatchSlots replyAliasCfg == false &&
     SeLe4n.Platform.Boot.embeddedIdentitiesMatchSlots ownIdCfg == true)
  assertBool "capTargetsReservedIdleObject decides by the capability's target"
    (SeLe4n.Kernel.capTargetsReservedIdleObject
        { target := .object idle0Obj, rights := AccessRightSet.ofList [.write] } == true &&
     SeLe4n.Kernel.capTargetsReservedIdleObject
        { target := .cnodeSlot idle0Obj (SeLe4n.Slot.ofNat 0), rights := AccessRightSet.ofList [.write] } == true &&
     SeLe4n.Kernel.capTargetsReservedIdleObject
        { target := .object ⟨9⟩, rights := AccessRightSet.ofList [.write] } == false)
  -- The same object one slot below the idle range is accepted: the refusal is
  -- the reservation, not the object.
  let neighbour : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [],
      initialObjects := [ { id := SeLe4n.ObjId.ofNat (idleThreadIdBase - 1),
                            obj := .notification { state := .idle, 
                                                   hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero },
                            hSlots := fun _ h => KernelObject.noConfusion h,
                            hMappings := fun _ h => KernelObject.noConfusion h } ] }
  assertBool "the same object just below the idle range is accepted"
    (SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads neighbour).toOption.isSome

/-- §**PR #889 review round 23**: a configuration must declare at least one PE.

Round 22's `declaredCoresOfConfig` clamped the count from above and said nothing
about zero, where the derivation yields the **empty** core list: no idle thread
is installed on any core, `bootAffinitiesDeclared []` is satisfied by any config
whose TCBs are unpinned, and the boot returns `.ok` with nowhere to run.  These
assert the refusal, its diagnostic, and — in both directions — that a legitimate
narrow count is still accepted. -/
private def runDeclaredCoreCountChecks : IO Unit := do
  IO.println "--- PR #889 round 23: a config must declare 1..numCores PEs ---"
  let withCount (n : Nat) : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := { SeLe4n.defaultMachineConfig with declaredCoreCount := n } }
  assertBool "a zero declared-core config is not well-formed"
    ((withCount 0).wellFormed == false)
  assertBool "...and its refusal names the declared-core count, not another conjunct"
    (SeLe4n.Platform.Boot.wellFormedDiagnostic (withCount 0) ==
      SeLe4n.Platform.Boot.declaredCoreCountBootError)
  assertBool "a zero declared-core config is refused by the checked boot"
    ((SeLe4n.Platform.Boot.bootFromPlatformChecked (withCount 0)).isOk == false)
  -- The bound is narrow: one PE is a legitimate deployment, and the full width
  -- is what every existing fixture declares.
  assertBool "a single-PE config is well-formed"
    ((withCount 1).wellFormed == true)
  assertBool "a full-width config is well-formed"
    ((withCount SeLe4n.Kernel.Concurrency.numCores).wellFormed == true)
  -- ...and a count above the model is refused rather than silently widened.
  assertBool "a config declaring more PEs than the model has is refused"
    ((withCount (SeLe4n.Kernel.Concurrency.numCores + 1)).wellFormed == false)

/-- **WS-BP BP7.1 (`v0.36.13`)**: every configured address space owns a table
page of the binding's pool.  Each refusal names its own conjunct, and the
control — two roots on two pool pages — is accepted, so the refusals are about
the pages and not about configuring a root at all. -/
private def poolRootEntry (id asid : Nat) (base : Option SeLe4n.PAddr) :
    SeLe4n.Platform.Boot.ObjectEntry :=
  { id := ⟨id⟩
    obj := .vspaceRoot { asid := ⟨asid⟩, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16,
                         tableBase := base }
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => by
      cases h; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega) }

private def runBootTablePoolChecks : IO Unit := do
  IO.println "--- WS-BP BP7.1: every configured address space owns a pool page ---"
  let page (i : Nat) : SeLe4n.PAddr := SeLe4n.PAddr.ofNat (0x0FFF_0000 + i * 4096)
  let mc : SeLe4n.MachineConfig :=
    { SeLe4n.defaultMachineConfig with
      kernelReserved := [{ base := SeLe4n.PAddr.ofNat 0, size := 0x1000_0000, kind := .reserved }]
      bootTablePool := [page 0, page 1] }
  let withRoots (mc : SeLe4n.MachineConfig) (a b : Option SeLe4n.PAddr) :
      SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], machineConfig := mc,
      initialObjects := [poolRootEntry 100 1 a, poolRootEntry 101 2 b] }
  let refusedHere (c : SeLe4n.Platform.Boot.PlatformConfig) : Bool :=
    c.wellFormed == false &&
      SeLe4n.Platform.Boot.wellFormedDiagnostic c == SeLe4n.Platform.Boot.bootRootTablesBootError
  assertBool "CONTROL: two roots on two pool pages are well-formed"
    ((withRoots mc (some (page 0)) (some (page 1))).wellFormed == true)
  assertBool "a root with no table page is refused, naming the pool"
    (refusedHere (withRoots mc (some (page 0)) none))
  assertBool "two roots sharing one page are refused, naming the pool"
    (refusedHere (withRoots mc (some (page 0)) (some (page 0))))
  assertBool "a page outside the pool is refused, naming the pool"
    (refusedHere (withRoots mc (some (page 0)) (some (page 2))))
  assertBool "a pool page outside the kernel's reserved extent is refused, naming the pool"
    (refusedHere (withRoots { mc with bootTablePool := [page 0, SeLe4n.PAddr.ofNat 0x2000_0000] }
      (some (page 0)) (some (SeLe4n.PAddr.ofNat 0x2000_0000))))
  assertBool "an unaligned pool page is refused, naming the pool"
    (refusedHere (withRoots { mc with bootTablePool := [page 0, SeLe4n.PAddr.ofNat 0x0FFF_1008] }
      (some (page 0)) (some (SeLe4n.PAddr.ofNat 0x0FFF_1008))))
  assertBool "the refused config is refused by the checked boot"
    ((SeLe4n.Platform.Boot.bootFromPlatformChecked (withRoots mc (some (page 0)) none)).isOk == false)

/-- **WS-ZA ZA5.4 part 13**: each boot untyped is named by at most one
capability.  The free index is in the capability, so two capabilities to one
untyped would be two carvers over the same memory; the boot refuses the
configuration, naming its own conjunct, and the control — one capability — is
accepted, so the refusal is about the duplicate and not about configuring a
capability to an untyped at all. -/
private def runBootUntypedCapabilityChecks : IO Unit := do
  IO.println "--- WS-ZA ZA5.4 part 13: one capability per boot untyped ---"
  let mc : SeLe4n.MachineConfig :=
    { SeLe4n.defaultMachineConfig with
      memoryMap := [{ base := SeLe4n.PAddr.ofNat 0x1000_0000, size := 0x10_0000, kind := .ram }]
      kernelReserved := [] }
  let utId : SeLe4n.ObjId := ⟨110⟩
  let utCap : Capability :=
    { target := .object utId, rights := AccessRightSet.ofList [.read, .write, .retype] }
  let utEntry : SeLe4n.Platform.Boot.ObjectEntry :=
    { id := utId
      obj := .untyped { regionBase := SeLe4n.PAddr.ofNat 0x1000_0000, regionSize := 0x1000 }
      hSlots := fun _ h => nomatch h
      hMappings := fun _ h => nomatch h }
  let cnEntry (slots : List (SeLe4n.Slot × Capability)) : SeLe4n.Platform.Boot.ObjectEntry :=
    { id := ⟨111⟩
      obj := .cnode (SeLe4n.Model.CNode.ofSlots 4 0 0 4 (SeLe4n.UniqueSlotMap.ofListWF slots))
      hSlots := fun _ h => by cases h; exact SeLe4n.Model.CNode.slotsUnique_holds _
      hMappings := fun _ h => nomatch h }
  let withSlots (slots : List (SeLe4n.Slot × Capability)) : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], machineConfig := mc, initialObjects := [utEntry, cnEntry slots] }
  let one := withSlots [(SeLe4n.Slot.ofNat 0, utCap)]
  let two := withSlots [(SeLe4n.Slot.ofNat 0, utCap), (SeLe4n.Slot.ofNat 1, utCap)]
  assertBool "CONTROL: one capability to a boot untyped is well-formed"
    (one.wellFormed == true)
  assertBool "NEGATIVE: two capabilities to one boot untyped are refused"
    (two.wellFormed == false && SeLe4n.Platform.Boot.untypedCapabilitiesUnique two == false)
  assertBool "...and the refusal names the duplicate, not another conjunct"
    (SeLe4n.Platform.Boot.wellFormedDiagnostic two ==
      SeLe4n.Platform.Boot.untypedCapabilityDuplicateBootError)
  assertBool "the duplicate config is refused by the checked boot"
    ((SeLe4n.Platform.Boot.bootFromPlatformChecked two).isOk == false)

/-- PR #889 review round 18: a successful boot must leave the object index
    inside `maxObjects`.  Nothing bounded the count before: the checked boot
    did not, and the idle fold adds one entry per core on top of it, so a
    config sized to fit exactly would boot to `maxObjects + numCores - 1`. -/
private def runObjectBudgetChecks : IO Unit := do
  let cap := SeLe4n.Model.maxObjects
  let cores := SeLe4n.Kernel.Concurrency.numCores
  -- A config filled to the old ceiling: every other conjunct holds, and the
  -- boot root plus the idle threads would take it past the cap.
  let filler (n : Nat) : List SeLe4n.Platform.Boot.ObjectEntry :=
    (List.range n).map fun i =>
      { id := ⟨SeLe4n.Kernel.idleThreadIdBase + SeLe4n.Kernel.Concurrency.numCores + i⟩,
        obj := .notification { state := .idle, 
                               hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero },
        hSlots := fun _ h => KernelObject.noConfusion h,
        hMappings := fun _ h => KernelObject.noConfusion h }
  let atCap : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := filler cap }
  assertBool "NEGATIVE: a config filling the object index to maxObjects is refused"
    (SeLe4n.Platform.Boot.PlatformConfig.wellFormed atCap == false)
  assertBool "NEGATIVE: ...and specifically by the object budget"
    (SeLe4n.Platform.Boot.objectBudgetRespected atCap == false)
  -- One object short of the reserved headroom is still refused: the boot root
  -- and every core's idle thread must fit.
  let justOver : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := filler (cap - cores) }
  assertBool "NEGATIVE: a config leaving no room for the boot root is refused"
    (SeLe4n.Platform.Boot.objectBudgetRespected justOver == false)
  -- The largest config that boots: the cap less the root and the idle threads.
  let atBudget : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := [], initialObjects := filler (cap - cores - 1) }
  assertBool "the largest config that leaves room for the root and the idle threads is accepted"
    (SeLe4n.Platform.Boot.objectBudgetRespected atBudget == true)
  -- ...and the boot really lands inside the cap, idle threads included.
  match SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads atBudget with
  | .ok ist =>
      assertBool "the boot state's object index is within maxObjects"
        (ist.state.objectIndex.length <= cap)
      assertBool "...and it carries the config's objects plus one idle thread per core"
        (ist.state.objectIndex.length == cap - 1)
  | .error e =>
      assertBool s!"the budget-respecting config must boot (got: {e})" false
  -- PR #889 review round 19: the budget has its own diagnostic.  Round 18 added
  -- the conjunct without a branch in the error cascade, so a config whose only
  -- fault was its size was reported as an embedded-identity mismatch — naming a
  -- fault it does not have.  `atCap` carries no id-bearing objects at all.
  assertBool "the over-budget config's identities are in fact all valid"
    (SeLe4n.Platform.Boot.embeddedIdentitiesMatchSlots atCap == true)
  match SeLe4n.Platform.Boot.bootFromPlatformChecked atCap with
  | .error e =>
      assertBool "NEGATIVE: ...and the refusal names the budget, not an identity mismatch"
        (e == SeLe4n.Platform.Boot.objectBudgetBootError)
  | .ok _ =>
      assertBool "NEGATIVE: an over-budget config must be refused" false
  -- PR #889 review round 19 (maintainer follow-up): the diagnostic is derived
  -- from one conjunct list, so each conjunct's refusal names that conjunct and
  -- no other.  Every entry of the list is exercised here, which is what stops
  -- the list and `wellFormed` from drifting the way the old cascade did.
  assertBool "the conjunct list and wellFormed enumerate the same conjuncts"
    (SeLe4n.Platform.Boot.PlatformConfig.wellFormed atCap ==
      ((SeLe4n.Platform.Boot.wellFormedConjuncts atCap).all (·.1)))
  assertBool "each failing conjunct is reported in its own words"
    (SeLe4n.Platform.Boot.wellFormedDiagnostic atCap ==
      SeLe4n.Platform.Boot.objectBudgetBootError)
  -- The ordinary fixtures are unaffected: the budget is about size alone.
  let small : SeLe4n.Platform.Boot.PlatformConfig := { irqTable := [], initialObjects := [] }
  assertBool "an ordinary small config respects the budget"
    (SeLe4n.Platform.Boot.objectBudgetRespected small == true)


/-- §3.12 (WS-RR RR7.36): the *live* thread-state relation and its preservation
across a per-core context switch.

Register §7 finding 42 — `inferThreadState` / `syncThreadStates` /
`threadStateConsistent` boot-core-pinned — closed with RR5.10's lift, which
`inferThreadState_running_of_currentOnCore` and the boot-state theorems above
already pin.  What RR5.10 left is the *consumer* side: the runtime surface syncs
before it checks, so it could not report drift, and nothing in the tree checked
the narrower relation the live decisions read.  These checks run it on unsynced
states, either side of a real dispatch, and pin the two premises the preservation
theorem takes by exhibiting a state that violates each. -/
private def runInactiveFlagChecks : IO Unit := do
  IO.println "--- §3.12 WS-RR RR7.36 live thread-state (inactive flag) relation ---"
  -- A queued, `.Ready`-flagged user thread: the flag says "not inactive" and the
  -- observable state agrees (it is placed).
  assertBool "the queued-user state satisfies the live relation"
    (SeLe4n.Testing.threadInactiveFlagConsistentBool stUserIdle)
  -- ... and it survives the dispatch that makes the full classification false.
  let switched := SeLe4n.Kernel.switchToThreadOnCore stUserIdle bootCoreId tidUser
  assertBool "the per-core context switch succeeds on that state"
    (match switched with | .ok _ => true | .error _ => false)
  assertBool "the live relation survives the context switch (RR7.36)"
    (match switched with
     | .ok st => SeLe4n.Testing.threadInactiveFlagConsistentBool st
     | .error _ => false)
  -- The full classification is exactly what does NOT survive it, which is why
  -- the narrow relation had to be stated separately rather than strengthened.
  assertBool "the full classification does NOT survive it (the reason for the split)"
    (match switched with
     | .ok st =>
         !((SeLe4n.Testing.stateInvariantChecksFor st.objectIndex st).all
             (fun p => p.2))
     | .error _ => false)
  -- The dispatch premise, exhibited: a run-queue entry whose stored flag says
  -- `.Inactive` already violates the relation before any switch, which is what
  -- `hActive` refuses.
  -- The flag is rewritten in place, so the thread keeps its run-queue links.
  let stInactiveQueued : SystemState :=
    stUserIdle.updateTcb tidUser (fun t => { t with threadState := .Inactive })
  assertBool "a queued thread flagged .Inactive violates the live relation"
    (!SeLe4n.Testing.threadInactiveFlagConsistentBool stInactiveQueued)
  -- The runtime entry points exist and are called: the quiescent boot-shaped
  -- state goes through the no-sync surface, the post-dispatch state through the
  -- live one.  Both had zero callers before this row.
  SeLe4n.Testing.assertStateInvariantsWithoutSync
    "RR7.36 quiescent state, no sync" stUserIdle.objectIndex
    (SeLe4n.Kernel.syncThreadStates stUserIdle)
  match switched with
  | .ok st => SeLe4n.Testing.assertLiveThreadStateInvariants "RR7.36 post-dispatch" st
  | .error _ => throw <| IO.userError "RR7.36: the context switch did not succeed"

def runSmpIdleChecks : IO Unit := do
  IO.println "WS-SM SM5.E — Per-core idle thread suite"
  IO.println "===================================="
  runFieldChecks
  runNoStallChecks
  runNoStarvationChecks
  runLocalityChecks
  runDispatcherChecks
  runLockSetChecks
  runInventoryChecks
  runBootIdleChecks
  runBootValidationParityChecks
  runObjectBudgetChecks
  runDeclaredCoreCountChecks
  runBootTablePoolChecks
  runBootUntypedCapabilityChecks
  runInactiveFlagChecks
  IO.println "===================================="
  IO.println "All SM5.E per-core idle thread checks PASS."

end SeLe4n.Testing.SmpIdle

def main : IO Unit :=
  SeLe4n.Testing.SmpIdle.runSmpIdleChecks

