-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.IdleStore
import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Platform.Boot

/-!
# WS-SM SM5.E — Per-core idle threads

Each core has a dedicated idle TCB — the thread it runs when nothing else is
eligible — bound to its own core and never migrating.  As in seL4, **an idle
thread is never queued**: the boot stores it (`storeIdleThreadOnCore`,
`Operations/IdleStore.lean`), a preemption never requeues it
(`runEnqueueAdmits`), and a core's scheduling point makes it current exactly
when the core's queue holds nothing eligible (`idleFallbackOnCore`).

The idle thread's identities and TCB (`idleThreadId`, `createIdleThread`,
`readyIdleThread` and their field lemmas) live in
`SeLe4n.Kernel.Scheduler.IdleThread`; the store and its Model-level frames live
in the production module `Operations/IdleStore`, because the boot runs it.  This
module adds the scheduler-level idle properties:

* **the per-core invariant surface** — the store keeps the SM4.C per-core
  invariants (`runnableThreadsAreTCBsOnCore`, `currentThreadValidOnCore`,
  `queueCurrentConsistentOnCore`, `currentThreadInActiveDomainOnCore`), and its
  declared lock footprint;
* **no core stalls** (`scheduleEffectiveOnCore_current_isSome`) — a scheduling
  point on a core whose idle thread is dispatchable always leaves the core a
  current thread, and the production boot makes every core's idle thread
  dispatchable;
* **idle runs only when nothing is eligible**
  (`scheduleEffectiveOnCore_idle_only_when_none`) — the seL4 posture that
  replaces the priority-`0` queue member this module used to reason about;
* **SM5.E.4 locality** — core `c`'s idle thread is on no other core's queue.

This module is staged (`Platform.Staged`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId allCores
  LockKey)

-- ============================================================================
-- §1  Per-core scheduler-invariant preservation
-- ============================================================================

/-- The store keeps "every queued thread resolves to a TCB": the queue is
unchanged, the idle thread resolves after the store, and every other thread's
resolution is framed. -/
theorem storeIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore (st : SystemState)
    (c c' : CoreId) (hInv : st.objects.invExt) (hRunnable : runnableThreadsAreTCBsOnCore st c') :
    runnableThreadsAreTCBsOnCore (storeIdleThreadOnCore st c) c' := by
  intro tid htid
  rw [storeIdleThreadOnCore_runQueueOnCore] at htid
  by_cases hEq : tid = idleThreadId c
  · subst hEq
    exact ⟨_, storeIdleThreadOnCore_getTcb?_self st c hInv⟩
  · rw [storeIdleThreadOnCore_getTcb?_ne st c tid hInv hEq]
    exact hRunnable tid htid

/-- The store keeps core `c'`'s current thread valid: the idle thread resolves
after the store, and every other thread's resolution is framed. -/
theorem storeIdleThreadOnCore_preserves_currentThreadValidOnCore (st : SystemState)
    (c c' : CoreId) (hInv : st.objects.invExt) (hVal : currentThreadValidOnCore st c') :
    currentThreadValidOnCore (storeIdleThreadOnCore st c) c' := by
  unfold currentThreadValidOnCore at *
  rw [storeIdleThreadOnCore_currentOnCore]
  cases hcur : st.scheduler.currentOnCore c' with
  | none => trivial
  | some t =>
    rw [hcur] at hVal
    simp only at hVal ⊢
    by_cases hEq : t = idleThreadId c
    · subst hEq
      exact ⟨_, storeIdleThreadOnCore_getTcb?_self st c hInv⟩
    · rw [storeIdleThreadOnCore_getTcb?_ne st c t hInv hEq]
      exact hVal

/-- The store writes no scheduler field, so dequeue-on-dispatch consistency is
kept on every core. -/
theorem storeIdleThreadOnCore_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (c c' : CoreId) (hQC : queueCurrentConsistentOnCore st.scheduler c') :
    queueCurrentConsistentOnCore (storeIdleThreadOnCore st c).scheduler c' := by
  rw [storeIdleThreadOnCore_scheduler]; exact hQC

/-- The store keeps current-in-active-domain provided the idle thread it
rewrites is not the running thread: every other thread's TCB and every core's
active domain are framed. -/
theorem storeIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore (st : SystemState)
    (c c' : CoreId) (hInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore c' ≠ some (idleThreadId c))
    (hDom : currentThreadInActiveDomainOnCore st c') :
    currentThreadInActiveDomainOnCore (storeIdleThreadOnCore st c) c' := by
  unfold currentThreadInActiveDomainOnCore at *
  rw [storeIdleThreadOnCore_currentOnCore, storeIdleThreadOnCore_activeDomainOnCore]
  cases hcur : st.scheduler.currentOnCore c' with
  | none => trivial
  | some t =>
    rw [hcur] at hDom hNotCur
    have hNe : t ≠ idleThreadId c := fun heq => hNotCur (congrArg some heq)
    dsimp only at hDom ⊢
    rw [storeIdleThreadOnCore_getTcb?_ne st c t hInv hNe]
    exact hDom

-- ============================================================================
-- §2  No core stalls: the scheduling point always leaves a current thread
-- ============================================================================

/-- The outgoing-context save writes registers alone, so it keeps whether core
`c`'s idle thread is dispatchable. -/
theorem idleDispatchableOnCore_saveOutgoingContextOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    idleDispatchableOnCore (saveOutgoingContextOnCore st c) c = idleDispatchableOnCore st c := by
  unfold saveOutgoingContextOnCore
  split
  · rfl
  · rename_i t _
    unfold idleDispatchableOnCore
    rw [SystemState.updateTcb_scheduler]
    by_cases hy : idleThreadId c = t
    · subst hy
      rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv]
      cases st.getTcb? (idleThreadId c) <;> rfl
    · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _
        (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)]

/-- **No core stalls** (the SM5.E.6 keystone in seL4's shape): a scheduling
point on a core whose idle thread is dispatchable leaves the core a current
thread — the selected thread when something is eligible, the idle thread
otherwise. -/
theorem scheduleEffectiveOnCore_current_isSome {st st' : SystemState} {c : CoreId}
    (hInv : st.objects.invExt) (hIdle : idleDispatchableOnCore st c = true)
    (h : scheduleEffectiveOnCore st c = .ok st') :
    (st'.scheduler.currentOnCore c).isSome := by
  unfold scheduleEffectiveOnCore at h
  split at h
  · cases h
  · cases h
    unfold idleFallbackOnCore
    rw [if_pos (by rw [idleDispatchableOnCore_saveOutgoingContextOnCore st c hInv]; exact hIdle)]
    simp
  · split at h
    · split at h
      · cases h; simp
      · cases h
    · cases h

/-- **Idle runs only when nothing is eligible**: a scheduling point that leaves
core `c`'s idle thread current selected nothing, because the idle thread is on
no queue. -/
theorem scheduleEffectiveOnCore_idle_only_when_none {st st' : SystemState} {c : CoreId}
    (hR : st.runQueueRefinedOnCore c) (hOff : st.queuedOn c (idleThreadId c) = false)
    (h : scheduleEffectiveOnCore st c = .ok st')
    (hIdle : st'.scheduler.currentOnCore c = some (idleThreadId c)) :
    chooseThreadEffectiveOnCore st c = .ok none := by
  unfold scheduleEffectiveOnCore at h
  split at h
  · cases h
  · rename_i hC; exact hC
  · rename_i tid hC
    split at h
    · split at h
      · cases h
        simp at hIdle
        subst hIdle
        have hMem := chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c _ hR hC
        rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_iff_contains, ← hR.queuedOn] at hMem
        rw [hOff] at hMem; cases hMem
      · cases h
    · cases h

/-- On a boot-domain state the store makes core `c`'s idle thread dispatchable:
it resolves to the ready idle TCB, which is in domain `⟨0⟩` and pinned to `c`. -/
theorem storeIdleThreadOnCore_idleDispatchableOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hDom : st.scheduler.activeDomainOnCore c = ⟨0⟩) :
    idleDispatchableOnCore (storeIdleThreadOnCore st c) c = true := by
  unfold idleDispatchableOnCore
  rw [storeIdleThreadOnCore_getTcb?_self st c hInv, storeIdleThreadOnCore_activeDomainOnCore, hDom]
  simp only
  rw [affinityAdmitsCore_some _ c c (readyIdleThread_cpuAffinity c)]
  simp

/-- **The production boot makes every core's idle thread dispatchable**, so no
core stalls from its first scheduling point onward. -/
theorem bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore
    (config : SeLe4n.Platform.Boot.PlatformConfig)
    (ist : SeLe4n.Model.IntermediateState)
    (h : SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads config = .ok ist)
    (c : CoreId) :
    idleDispatchableOnCore ist.state c = true := by
  obtain ⟨hObj, hDom⟩ :=
    SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads_idle_resident config ist h c
  unfold idleDispatchableOnCore
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hObj, hDom]
  simp only
  rw [affinityAdmitsCore_some _ c c (readyIdleThread_cpuAffinity c)]
  simp

/-- **No core stalls on the production boot state**: every core's first
scheduling point leaves it a current thread. -/
theorem bootFromPlatformCheckedWithIdleThreads_scheduleEffectiveOnCore_current_isSome
    (config : SeLe4n.Platform.Boot.PlatformConfig)
    (ist : SeLe4n.Model.IntermediateState)
    (h : SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads config = .ok ist)
    (c : CoreId) {st' : SystemState} (hS : scheduleEffectiveOnCore ist.state c = .ok st') :
    (st'.scheduler.currentOnCore c).isSome :=
  scheduleEffectiveOnCore_current_isSome ist.hAllTables.objects.1
    (bootFromPlatformCheckedWithIdleThreads_idleDispatchableOnCore config ist h c) hS

-- ============================================================================
-- §3  `idleThread_core_locality` (SM5.E.4)
-- ============================================================================

/-- Core `c`'s idle slot holds the idle TCB, up to its run-queue links. -/
def idleTcbResidentOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∃ t, st.getTcb? (idleThreadId c) = some t ∧
    t.withoutRunLinks = (readyIdleThread c).withoutRunLinks

/-- After the store, core `c`'s idle TCB is resident. -/
theorem storeIdleThreadOnCore_idleTcbResidentOnCore (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : idleTcbResidentOnCore (storeIdleThreadOnCore st c) c :=
  ⟨_, storeIdleThreadOnCore_getTcb?_self st c hInv, rfl⟩

/-- WS-SM SM5.E.4: core `c`'s run queue is *affinity-consistent* — every thread
it holds resolves to a TCB admitted on core `c` (`affinityAdmitsCore`).
`idleThread_core_locality` consumes it to rule core `c`'s idle thread out of any
*other* core's queue. -/
def runQueueAffinityConsistentOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
    st.getTcb? tid = some tcb → affinityAdmitsCore tcb c = true

/-- WS-SM SM5.E.4 (`idleThread_core_locality`): core `c`'s idle thread never
appears on a *different* core `c' ≠ c`'s run queue — it is pinned to `c`
(`readyIdleThread_cpuAffinity`), so an affinity-consistent queue on `c'` cannot
hold it. -/
theorem idleThread_core_locality (st : SystemState) (c c' : CoreId) (h : c ≠ c')
    (hIdleTcb : idleTcbResidentOnCore st c)
    (hAff : runQueueAffinityConsistentOnCore st c') :
    idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList := by
  intro hMem
  obtain ⟨t, ht, hw⟩ := hIdleTcb
  have hAdmit : affinityAdmitsCore t c' = true := hAff (idleThreadId c) hMem t ht
  rw [affinityAdmitsCore_some t c' c (by
    rw [TCB.proj_eq_of_withoutRunLinks_eq TCB.cpuAffinity hw]
    exact readyIdleThread_cpuAffinity c)] at hAdmit
  exact h (beq_iff_eq.mp hAdmit)

/-- The store writes no queue, so it puts the idle thread on none. -/
theorem idleThread_core_locality_of_store (st : SystemState) (c c' : CoreId)
    (hAbsent : idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList) :
    idleThreadId c ∉ ((storeIdleThreadOnCore st c).scheduler.runQueueOnCore c').toList := by
  rw [storeIdleThreadOnCore_runQueueOnCore st c c']
  exact hAbsent

/-- The store keeps core `c`'s run queue affinity-consistent: the rewritten idle
TCB is pinned to `c`, and every other member's resolution is framed. -/
theorem storeIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self
    (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hAff : runQueueAffinityConsistentOnCore st c) :
    runQueueAffinityConsistentOnCore (storeIdleThreadOnCore st c) c := by
  intro tid htid tcb htcb
  rw [storeIdleThreadOnCore_runQueueOnCore] at htid
  by_cases hEq : tid = idleThreadId c
  · subst hEq
    rw [storeIdleThreadOnCore_getTcb?_self st c hInv] at htcb
    cases htcb
    rw [affinityAdmitsCore_some _ c c (readyIdleThread_cpuAffinity c)]
    simp
  · rw [storeIdleThreadOnCore_getTcb?_ne st c tid hInv hEq] at htcb
    exact hAff tid htid tcb htcb

/-- WS-SM SM5.E.4 (`∀ c` aggregate): core `c`'s idle thread is absent from every
other core's run queue, simultaneously. -/
theorem idleThread_core_locality_forall (st : SystemState)
    (hIdle : ∀ c, idleTcbResidentOnCore st c)
    (hAff : ∀ c, runQueueAffinityConsistentOnCore st c) :
    ∀ c c', c ≠ c' → idleThreadId c ∉ (st.scheduler.runQueueOnCore c').toList :=
  fun c c' h => idleThread_core_locality st c c' h (hIdle c) (hAff c')

/-- The store leaves every other core's selection inputs — its run queue and its
active domain — unchanged. -/
theorem storeIdleThreadOnCore_selection_inputs_framed
    (st : SystemState) (c c' : CoreId) :
    (storeIdleThreadOnCore st c).scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c' ∧
    (storeIdleThreadOnCore st c).scheduler.activeDomainOnCore c'
        = st.scheduler.activeDomainOnCore c' :=
  ⟨storeIdleThreadOnCore_runQueueOnCore st c c',
   storeIdleThreadOnCore_activeDomainOnCore st c c'⟩

-- ============================================================================
-- §4  Lock-set footprint (`storeIdleThreadOnCoreLockSet`)
-- ============================================================================

/-- The lock footprint of `storeIdleThreadOnCore`: it WRITES the object store
(the idle TCB store) and nothing else — no run queue, since the idle thread is
never queued. -/
def storeIdleThreadOnCoreLockSet (_c : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  [ (LockKey.objStore, .write) ]

@[simp] theorem storeIdleThreadOnCoreLockSet_length (c : CoreId) :
    (storeIdleThreadOnCoreLockSet c).length = 1 := rfl

/-- Every lock in the idle-store footprint is **write** mode. -/
theorem storeIdleThreadOnCoreLockSet_write_only (c : CoreId) :
    ∀ p ∈ storeIdleThreadOnCoreLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [storeIdleThreadOnCoreLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp; rfl

/-- The object-store write lock is in the idle-store footprint. -/
theorem storeIdleThreadOnCoreLockSet_contains_objStore_write (c : CoreId) :
    (LockKey.objStore, Concurrency.AccessMode.write)
      ∈ storeIdleThreadOnCoreLockSet c := by
  simp [storeIdleThreadOnCoreLockSet]

/-- The footprint's keys form a `LockKey`-ascending acquisition sequence, so the
canonical `withLockSet` acquisition is the list itself. -/
theorem storeIdleThreadOnCoreLockSet_pairwise_le (c : CoreId) :
    ((storeIdleThreadOnCoreLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  simp [storeIdleThreadOnCoreLockSet]

end SeLe4n.Kernel
