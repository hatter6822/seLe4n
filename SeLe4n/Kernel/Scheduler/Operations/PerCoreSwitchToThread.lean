-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Scheduler.Operations.Core

/-!
# WS-SM SM5.B — Per-core `switchToThread` (lock-set, switch theorems, decidability)

This module is the SM5.B deliverable of the WS-SM Phase 5 per-core scheduler
(plan `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.2, §5).  The per-core
context-switch transition `switchToThreadOnCore` itself (with `preemptCurrentOnCore`
and the `affinityAdmitsCore` gate) lives in the production module
`Scheduler.Operations.Selection`, alongside the other switch primitives
(`saveOutgoingContext` / `restoreIncomingContext`); this module collects the
*forward-looking* SM5.B theorems — the cross-domain lock-set declaration, the
switch-semantics theorems (sets-current, preempts-previous, rejects-remote,
run-queue-excludes-current), the cross-core-independence frame, and the
totality + decidability witnesses — staged until SM5.C wires
`switchToThreadOnCore` into the cross-core wake / SGI dispatch loop and the
runtime `withLockSet` acquisition over `switchToThreadOnCoreLockSet`.

## What this module proves

* **SM5.B.2** `switchToThreadOnCoreLockSet` — the *complete* two-domain
  cross-domain footprint over SM5.A's `SchedLockId`: the object-store **write**
  lock (`schedObjStoreLockId`, guarding the `getTcb?` resolutions *and* the
  preempted thread's register-context save) plus the per-core run-queue
  **write** lock (guarding the re-enqueue / dequeue / current-set).  The
  cross-domain order (object lock before run-queue lock, plan §4.4) is
  `switchToThreadOnCoreLockSet_object_before_runQueue`.  The write modes (vs
  `chooseThreadOnCoreLockSet`'s read modes) reflect that switching *mutates*
  both domains.
* **SM5.B.1 / Theorem 3.2.1** `switchToThreadOnCore_sets_current` — on success
  the new current thread of core `c` is `tid`.
* **SM5.B.3 / Theorem 3.2.2** `switchToThreadOnCore_preempts_previous` — the
  evicted previous current thread is re-enqueued into the *same* core's run
  queue (preempted, not lost).
* **SM5.B.4 / Theorem 3.2.3** `switchToThreadOnCore_rejects_remote` — a switch
  onto a core other than the thread's `cpuAffinity` is rejected with
  `KernelError.threadOnDifferentCore`; the dual
  `switchToThreadOnCore_ok_of_admits` shows an admitted thread succeeds.
* **SM5.B.5** `switchToThreadOnCore_runQueueOnCore_excludes_current` — after the
  switch the new current thread is *not* simultaneously in the run queue
  (dequeue-on-dispatch).
* **SM5.B.6** `switchToThreadOnCore_independent_of_other_core` — switching on
  core `c` leaves every other core's `current` and `runQueue` slots untouched
  (the cross-core lock-set protection / per-core independence frame).
* **SM5.B.8** `switchToThreadOnCore_total` + the decidable predicates
  `switchToThreadOnCoreSucceeds` / `switchToThreadOnCoreRejectsRemote`.

Axiom-clean: every theorem depends only on the standard foundational axioms
(`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores)

-- ============================================================================
-- §1  SM5.B.2 — Cross-domain lock-set footprint of `switchToThreadOnCore`
-- ============================================================================

/-- WS-SM SM5.B.2 (cross-domain, plan §3.2 / §4.4): the **complete** lock-set
footprint of `switchToThreadOnCore c tid`, over SM5.A's unified `SchedLockId`.

`switchToThreadOnCore` touches *both* lock domains, and — unlike the read-only
`chooseThreadOnCore` — it **mutates** both:

* the RobinHood **object store** (write): it resolves `tid`'s TCB via
  `getTcb?` *and* writes the preempted thread's saved register context back via
  `objects.insert` (`preemptCurrentOnCore`).  Per SM3.A.10 the store is guarded
  by the single table-level lock at the top of the SM0.I hierarchy
  (`schedObjStoreLockId`), here taken in **write** mode; and
* core `c`'s per-core **run-queue** slot (write): it re-enqueues the preempted
  thread, dequeues `tid`, and sets the current thread.

So the footprint is the two-lock set in plan §4.4 ascending order (object lock
first):
`[(SchedLockId.object schedObjStoreLockId, .write), (SchedLockId.runQueue ⟨c⟩, .write)]`.

**Why the table lock rather than `(LockId.tcb tid, .write)` (plan §3.2's
sketch).** The switch writes *two* TCBs — `tid` (read for affinity + context
restore) and the dynamically-discovered *previous current* thread (written: its
register context is saved on preemption).  A static lock-set naming only `tid`
would under-lock the preempted thread — exactly the cross-domain under-locking
class SM5.A's audit (PR #804) closed for `chooseThreadOnCore`.  Holding the
object-store *table* write lock subsumes both TCB accesses (and any future
PIP-chain writes) under one lock, the faithful SM3.A.10 discipline.  The runtime
`withLockSet` acquisition over this footprint is SM5.C work. -/
def switchToThreadOnCoreLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.runQueue ⟨c⟩, .write) ]

/-- SM5.B.2: the footprint is the two-lock object-store + run-queue set. -/
@[simp] theorem switchToThreadOnCoreLockSet_length (c : CoreId) :
    (switchToThreadOnCoreLockSet c).length = 2 := rfl

/-- SM5.B.2: every lock in the `switchToThreadOnCore` footprint is acquired in
**write** mode — the switch mutates both the object store and the run queue
(contrast `chooseThreadOnCoreLockSet`, a pure read). -/
theorem switchToThreadOnCoreLockSet_write_only (c : CoreId) :
    ∀ p ∈ switchToThreadOnCoreLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [switchToThreadOnCoreLockSet, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM5.B.2: the object-store **write** lock is in the footprint — it guards
both the `getTcb?` resolutions *and* the preempted thread's register-context
save (the write a `LockId.tcb tid`-only set would miss). -/
theorem switchToThreadOnCoreLockSet_contains_objStore_write (c : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ switchToThreadOnCoreLockSet c := by
  simp [switchToThreadOnCoreLockSet]

/-- SM5.B.2: the per-core run-queue **write** lock is in the footprint — it
guards the re-enqueue / dequeue / current-set on core `c`. -/
theorem switchToThreadOnCoreLockSet_contains_runQueue_write (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ switchToThreadOnCoreLockSet c := by
  simp [switchToThreadOnCoreLockSet]

/-- SM5.B.2 (plan §4.4): inside the footprint the object-store lock is acquired
*before* the run-queue lock — the cross-domain ascending order that, with the
SM0.I within-domain order, gives the SM3.D deadlock-freedom argument. -/
theorem switchToThreadOnCoreLockSet_object_before_runQueue (c : CoreId) :
    SchedLockId.object schedObjStoreLockId
      < SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
  SchedLockId.object_lt_runQueue _ _

/-- SM5.B.2: the footprint's projected keys are duplicate-free (object lock vs
run-queue lock are distinct constructors), mirroring SM3.B's
`LockSet.hUniqueKeys`. -/
theorem switchToThreadOnCoreLockSet_keys_nodup (c : CoreId) :
    ((switchToThreadOnCoreLockSet c).map (·.1)).Nodup := by
  simp [switchToThreadOnCoreLockSet]

-- ============================================================================
-- §2  `preemptCurrentOnCore` frame lemmas (per-core write footprint)
-- ============================================================================

/-- WS-SM SM5.B.3 (frame): `preemptCurrentOnCore` never writes any core's
`current` slot — it only saves the outgoing thread's context (objects) and
re-enqueues it into core `c`'s run queue (scheduler).  So *every* core's
current thread is preserved. -/
theorem preemptCurrentOnCore_currentOnCore (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (c' : CoreId) :
    (preemptCurrentOnCore st c incoming).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  unfold preemptCurrentOnCore
  split
  · rfl
  · split
    · rfl
    · split
      · simp
      · rfl

/-- WS-SM SM5.B.3 (frame): `preemptCurrentOnCore` writes only core `c`'s
run-queue slot, so any *other* core's run queue (`c' ≠ c`) is preserved.  This
is half of the cross-core-independence frame (SM5.B.6). -/
theorem preemptCurrentOnCore_runQueueOnCore_ne (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (c' : CoreId) (h : c ≠ c') :
    (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  unfold preemptCurrentOnCore
  split
  · rfl
  · split
    · rfl
    · split
      · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne st.scheduler c c' _ h
      · rfl

/-- WS-SM SM5.B.3: the active (re-enqueue) value of `preemptCurrentOnCore` on
core `c`'s own run queue — when core `c` has a current thread `prevTid` that is
distinct from `incoming` and resolves to a TCB, the preempted thread is
inserted at its effective priority.  This is the substantive content behind
`switchToThreadOnCore_preempts_previous`. -/
theorem preemptCurrentOnCore_runQueueOnCore_self_active (st : SystemState) (c : CoreId)
    (incoming prevTid : SeLe4n.ThreadId) (prevTcb : TCB)
    (hCur : st.scheduler.currentOnCore c = some prevTid)
    (hNe : (prevTid == incoming) = false)
    (hTcb : st.getTcb? prevTid = some prevTcb) :
    (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c
      = (st.scheduler.runQueueOnCore c).insert prevTid (effectiveRunQueuePriority prevTcb) := by
  unfold preemptCurrentOnCore
  simp [hCur, hNe, hTcb]

-- ============================================================================
-- §3  SM5.B.1/.3/.4/.5/.6 — Switch-semantics theorems
-- ============================================================================

/-- WS-SM SM5.B.4 (plan §3.2, Theorem 3.2.3): reject-remote.  A switch onto a
core other than the thread's CPU affinity is rejected with
`KernelError.threadOnDifferentCore` — a context switch never implicitly
migrates a bound thread between cores. -/
theorem switchToThreadOnCore_rejects_remote (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (tidTcb : TCB)
    (hTcb : st.getTcb? tid = some tidTcb)
    (hAff : tidTcb.cpuAffinity = some c')
    (hNe : c' ≠ c) :
    switchToThreadOnCore st c tid = .error .threadOnDifferentCore := by
  have hAdmit : affinityAdmitsCore tidTcb c = false := by
    rw [affinityAdmitsCore_some tidTcb c c' hAff]
    exact beq_eq_false_iff_ne.mpr hNe
  unfold switchToThreadOnCore
  simp [hTcb, hAdmit]

/-- WS-SM SM5.B.4 (dual): when `tid` resolves to a TCB whose affinity *admits*
core `c`, the switch succeeds.  Together with `switchToThreadOnCore_rejects_remote`
this characterises the affinity gate exactly. -/
theorem switchToThreadOnCore_ok_of_admits (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tidTcb : TCB)
    (hTcb : st.getTcb? tid = some tidTcb)
    (hAff : affinityAdmitsCore tidTcb c = true) :
    ∃ st', switchToThreadOnCore st c tid = .ok st' := by
  unfold switchToThreadOnCore
  simp only [hTcb]
  rw [if_pos hAff]
  exact ⟨_, rfl⟩

/-- WS-SM SM5.B.1 (plan §3.2, Theorem 3.2.1): on success the new current thread
of core `c` is `tid`. -/
theorem switchToThreadOnCore_sets_current (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.currentOnCore c = some tid := by
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      simp
    · rw [if_neg hAff] at h; simp at h

/-- WS-SM SM5.B.5 (plan §3.2): dequeue-on-dispatch — after the switch the new
current thread of core `c` is *not* simultaneously in core `c`'s run queue. -/
theorem switchToThreadOnCore_runQueueOnCore_excludes_current (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (h : switchToThreadOnCore st c tid = .ok st') :
    tid ∉ (st'.scheduler.runQueueOnCore c).toList := by
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
        restoreIncomingContext_scheduler,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      exact RunQueue.not_mem_remove_toList _ tid
    · rw [if_neg hAff] at h; simp at h

/-- WS-SM SM5.B.3 (plan §3.2, Theorem 3.2.2): preempts-previous — when core `c`
had a current thread `prevTid` distinct from `tid` (resolving to a TCB), the
evicted `prevTid` is re-enqueued into the *same* core's run queue (preempted,
not lost). -/
theorem switchToThreadOnCore_preempts_previous (st : SystemState) (c : CoreId)
    (tid prevTid : SeLe4n.ThreadId) (prevTcb : TCB) (st' : SystemState)
    (hCur : st.scheduler.currentOnCore c = some prevTid)
    (hNe : prevTid ≠ tid)
    (hPrevTcb : st.getTcb? prevTid = some prevTcb)
    (h : switchToThreadOnCore st c tid = .ok st') :
    prevTid ∈ (st'.scheduler.runQueueOnCore c).toList := by
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      have hBeq : (prevTid == tid) = false := beq_eq_false_iff_ne.mpr hNe
      have hPreempt := preemptCurrentOnCore_runQueueOnCore_self_active st c tid
        prevTid prevTcb hCur hBeq hPrevTcb
      simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
        restoreIncomingContext_scheduler,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_self, hPreempt]
      rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_remove]
      exact ⟨(RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl), hNe⟩
    · rw [if_neg hAff] at h; simp at h

/-- WS-SM SM5.B.6 (cross-core lock-set protection / per-core independence): a
switch on core `c` leaves *every other* core's `current` and `runQueue` slots
untouched.  This is the scheduler-state frame that makes the per-core switch
safe under SMP — it writes only core `c`'s slots (plus the object store), so a
concurrent switch on a sibling core cannot observe a change to its own
scheduler state.  Matches the run-queue write lock of
`switchToThreadOnCoreLockSet` covering only core `c`. -/
theorem switchToThreadOnCore_independent_of_other_core (st : SystemState)
    (c c' : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hcc : c ≠ c')
    (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
      ∧ st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      refine ⟨?_, ?_⟩
      · simp only [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc,
          restoreIncomingContext_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore,
          preemptCurrentOnCore_currentOnCore]
      · simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
          restoreIncomingContext_scheduler,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc,
          preemptCurrentOnCore_runQueueOnCore_ne _ _ _ _ hcc]
    · rw [if_neg hAff] at h; simp at h

-- ============================================================================
-- §4  SM5.B.8 — Totality + decidability
-- ============================================================================

/-- WS-SM SM5.B.8: `switchToThreadOnCore` is a total function — it always
returns (no fuel, no partiality); the only question is `.ok` vs `.error`,
characterised by `switchToThreadOnCore_ok_of_admits` /
`switchToThreadOnCore_rejects_remote`. -/
theorem switchToThreadOnCore_total (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    ∃ r, switchToThreadOnCore st c tid = r := ⟨_, rfl⟩

/-- WS-SM SM5.B.8: "core `c` can switch to `tid`" — the decidable proposition
the SM5.B unit tests discharge by `decide` on concrete states.  Like SM5.A's
`chooseThreadOnCoreSelects`, the `Decidable` instance is given explicitly by a
structural case analysis on the (fully-evaluated) `Except` result, since Lean
core does not derive `DecidableEq (Except _ SystemState)`. -/
def switchToThreadOnCoreSucceeds (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Prop :=
  ∃ st', switchToThreadOnCore st c tid = .ok st'

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Decidable (switchToThreadOnCoreSucceeds st c tid) :=
  match h : switchToThreadOnCore st c tid with
  | .ok st' => .isTrue ⟨st', h⟩
  | .error _ => .isFalse (by simp [switchToThreadOnCoreSucceeds, h])

/-- WS-SM SM5.B.8 / SM5.B.4: "core `c` rejects switching to `tid` because the
thread is bound to a different core" — the decidable reject-remote predicate. -/
def switchToThreadOnCoreRejectsRemote (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Prop :=
  switchToThreadOnCore st c tid = .error .threadOnDifferentCore

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Decidable (switchToThreadOnCoreRejectsRemote st c tid) :=
  match h : switchToThreadOnCore st c tid with
  | .ok _ => .isFalse (by simp [switchToThreadOnCoreRejectsRemote, h])
  | .error e =>
    if he : e = .threadOnDifferentCore then
      .isTrue (by simp [switchToThreadOnCoreRejectsRemote, h, he])
    else
      .isFalse (by simp [switchToThreadOnCoreRejectsRemote, h, he])

end SeLe4n.Kernel
