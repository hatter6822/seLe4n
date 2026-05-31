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
* **SM5.B.5** `switchToThreadOnCore_establishes_queueCurrentConsistentOnCore` +
  `switchToThreadOnCore_establishes_currentThreadValidOnCore` — a successful
  switch *establishes* both SM4.C current-thread conjuncts on core `c`: its new
  current thread is dequeued from the run queue **and** resolves to a TCB.  The
  latter routes through the typed-accessor frame
  `preemptCurrentOnCore_getTcb?_incoming` (the `.get?`-method form, AK7-clean).
* **SM5.B.6** `switchToThreadOnCore_independent_of_other_core` — switching on
  core `c` leaves every other core's `current` and `runQueue` slots untouched
  (the cross-core lock-set protection / per-core independence frame).
* **SM5.B.8** `switchToThreadOnCore_ok_iff` (the substantive totality form:
  succeeds **iff** `tid` resolves to a TCB whose affinity admits `c`) + the
  decidable predicates `switchToThreadOnCoreSucceeds` /
  `switchToThreadOnCoreRejectsRemote`.

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
register context is saved on preemption via `objects.insert`).  A static
lock-set naming only `tid` would under-lock the preempted thread — exactly the
cross-domain under-locking class SM5.A's audit (PR #804) closed for
`chooseThreadOnCore`.

Crucially, the save is an `RHTable.insert`, and **SM3.A.10 guards the RobinHood
object store's structural concurrency-safety at *table* granularity, not
per-object** (`SystemState.objStoreLock` = `LockKind.objStore`, level 0): a
concurrent insert can relocate slots along the probe sequence, so per-object
TCB locks would not protect the table structure.  The object-store **table**
write lock is therefore the *sound* discipline (and it subsumes the dynamic
preempted-TCB write that a static `LockId.tcb tid`-only set would miss).

**Trade-off (honest).** A table-level *write* lock means cross-core switches
that mutate the object store **serialize** on it — a known SMP-scalability
limitation inherited from SM3.A.10's table-granularity object-store locking,
*not* a careless over-locking.  Finer per-object switch locking is sound only
once per-slot RHTable concurrency is established (an in-place update of an
existing key does not relocate); that is a tracked **post-SM5 optimization**,
not an SM5.B regression.  The per-core *run-queue* lock, by contrast, is
genuinely per-core, so switches on distinct cores never contend on it.  The
runtime `withLockSet` acquisition over this footprint — in the ascending
`SchedLockId` order certified by `switchToThreadOnCoreLockSet_pairwise_le` — is
SM5.C work. -/
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

-- ── §2b  preempt preservation + unreachability of the non-TCB fallback ──

/-- WS-SM SM5.B.3 (preservation): `preemptCurrentOnCore` preserves the RobinHood
object-store invariant.  The only object-store mutation is the in-place save of
the outgoing thread's TCB (an `insert` at an existing key), which preserves
`invExt`; every other branch is the identity on `objects`. -/
theorem preemptCurrentOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (preemptCurrentOnCore st c incoming).objects.invExt := by
  unfold preemptCurrentOnCore
  split
  · exact hInv
  · split
    · exact hInv
    · split
      · exact RHTable_insert_preserves_invExt st.objects _ _ hInv
      · exact hInv

/-- WS-SM SM5.B.3 (preservation): `preemptCurrentOnCore` preserves core `c`'s
run-queue well-formedness — the only run-queue mutation is the re-enqueue
(`insert`), which preserves `RunQueue.wellFormed`; every other branch leaves the
run queue unchanged. -/
theorem preemptCurrentOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c : CoreId) (incoming : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c).wellFormed := by
  unfold preemptCurrentOnCore
  split
  · exact hwf
  · split
    · exact hwf
    · split
      · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.insert_preserves_wellFormed _ hwf _ _
      · exact hwf

/-- WS-SM SM5.B.3 (defense-in-depth, the SM5.B.4 audit closure): under
`currentThreadValidOnCore` — core `c`'s current thread resolves to a TCB — the
"previous current isn't a TCB" fallback of `preemptCurrentOnCore` is
**unreachable**.  When core `c` has a current thread `prevTid` distinct from
`incoming`, the preempt genuinely takes its active branch: `prevTid` resolves to
a TCB and is re-enqueued.  Mirrors the `saveOutgoingContext_always_succeeds_under_currentThreadValid`
discipline (`Scheduler/Operations/Selection.lean`) for the per-core preempt. -/
theorem preemptCurrentOnCore_active_under_valid (st : SystemState) (c : CoreId)
    (incoming prevTid : SeLe4n.ThreadId)
    (hValid : currentThreadValidOnCore st c)
    (hCur : st.scheduler.currentOnCore c = some prevTid)
    (hNe : (prevTid == incoming) = false) :
    ∃ prevTcb, st.getTcb? prevTid = some prevTcb ∧
      (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c
        = (st.scheduler.runQueueOnCore c).insert prevTid (effectiveRunQueuePriority prevTcb) := by
  unfold currentThreadValidOnCore at hValid
  simp only [hCur] at hValid
  obtain ⟨prevTcb, hPrevTcb⟩ := hValid
  exact ⟨prevTcb, hPrevTcb,
    preemptCurrentOnCore_runQueueOnCore_self_active st c incoming prevTid prevTcb hCur hNe hPrevTcb⟩

/-- WS-SM SM5.B.3 (typed-accessor frame): `preemptCurrentOnCore` leaves the
incoming thread's `getTcb?` lookup unchanged.  The preempt's only object-store
write is the *previous* current thread's register-context save, at key
`prevTid.toObjId` with `prevTid ≠ incoming` (the `prevTid == incoming` no-op
branch already discharged the equal case); so the lookup at `incoming` is
framed out.  Proved through the typed `getTcb?` accessor + the `.get?`-method
form of `RHTable.getElem?_insert_ne` (no raw object-store `[·]?` bracket in the
proof source), so it composes the `currentThreadValidOnCore` establishment
below without growing the AK7 `RAW_LOOKUP_TID` metric. -/
theorem preemptCurrentOnCore_getTcb?_incoming (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (preemptCurrentOnCore st c incoming).getTcb? incoming = st.getTcb? incoming := by
  unfold preemptCurrentOnCore
  split
  · rfl
  · next prevTid _ =>
    split
    · rfl
    · next hBeq =>
      split
      · next prevTcb _ =>
        have hNeT : prevTid ≠ incoming := by
          intro he; subst he; simp at hBeq
        have hNeO : ¬ (prevTid.toObjId == incoming.toObjId) = true := fun he =>
          hNeT (ThreadId.toObjId_injective _ _ (by simpa using he))
        simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects prevTid.toObjId
          incoming.toObjId _ hNeO hInv]
      · rfl

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
-- §3b  Invariant preservation (structural foundations for SM5.I.8)
-- ============================================================================
--
-- `switchToThreadOnCore` is a genuine state mutation, so — unlike the read-only
-- `chooseThreadOnCore` — it carries preservation obligations.  The structural
-- invariants a sound transition must preserve (the RobinHood object-store
-- invariant + core `c`'s run-queue well-formedness) are proved here, together
-- with the two SM4.C current-thread conjuncts the switch *establishes* on core
-- `c` (queue/current-consistency AND current-thread-validity).  The full
-- aggregate `schedulerInvariant_perCore` preservation (all 10 conjuncts) is
-- SM5.I.8 ("preservation by every transition") per the plan; these are the
-- foundations it composes.

/-- WS-SM SM5.B (preservation): `switchToThreadOnCore` preserves the RobinHood
object-store invariant.  Its only object-store write is the preempted thread's
register-context save (`preemptCurrentOnCore`); the dequeue / restore /
set-current steps leave `objects` untouched. -/
theorem switchToThreadOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (h : switchToThreadOnCore st c tid = .ok st') :
    st'.objects.invExt := by
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      simp only [restoreIncomingContext_objects]
      exact preemptCurrentOnCore_preserves_objects_invExt st c tid hInv
    · rw [if_neg hAff] at h; simp at h

/-- WS-SM SM5.B (preservation): `switchToThreadOnCore` preserves core `c`'s
run-queue well-formedness.  The post-state run queue is
`(preempt-re-enqueue).remove tid` — `insert` and `remove` both preserve
`RunQueue.wellFormed`, and the restore / set-current steps don't touch the run
queue. -/
theorem switchToThreadOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : switchToThreadOnCore st c tid = .ok st') :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
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
      exact RunQueue.remove_preserves_wellFormed _
        (preemptCurrentOnCore_preserves_runQueueOnCore_wellFormed st c tid hwf) tid
    · rw [if_neg hAff] at h; simp at h

/-- WS-SM SM5.B.5 (invariant established): after a successful switch, core `c`
satisfies `queueCurrentConsistentOnCore` — its current thread (`= tid`) is not
in its run queue.  This is the SM4.C invariant form of the SM5.B.5
dequeue-on-dispatch postcondition (combining `_sets_current` and
`_runQueueOnCore_excludes_current`), so the switch doesn't merely preserve but
*establishes* queue/current consistency on core `c`. -/
theorem switchToThreadOnCore_establishes_queueCurrentConsistentOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (h : switchToThreadOnCore st c tid = .ok st') :
    queueCurrentConsistentOnCore st'.scheduler c := by
  unfold queueCurrentConsistentOnCore
  rw [switchToThreadOnCore_sets_current st c tid st' h]
  exact switchToThreadOnCore_runQueueOnCore_excludes_current st c tid st' h

/-- WS-SM SM5.B (object frame): the switch's entire object-store footprint is
the preempt's — `st'.objects = (preemptCurrentOnCore st c tid).objects` — because
the dequeue / restore / set-current steps don't touch `objects`.  Combined with
`preemptCurrentOnCore`'s definition (its only object write is the preempted
thread's register-context save), this pins the switch's object write set to *at
most one* TCB (the preempted thread), the cross-core-frame complement to
`switchToThreadOnCore_independent_of_other_core` on the scheduler side. -/
theorem switchToThreadOnCore_objects_eq_preempt (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (h : switchToThreadOnCore st c tid = .ok st') :
    st'.objects = (preemptCurrentOnCore st c tid).objects := by
  unfold switchToThreadOnCore at h
  cases hTcb : st.getTcb? tid with
  | none => simp [hTcb] at h
  | some tidTcb =>
    simp only [hTcb] at h
    by_cases hAff : affinityAdmitsCore tidTcb c = true
    · rw [if_pos hAff, Except.ok.injEq] at h
      subst h
      simp only [restoreIncomingContext_objects]
    · rw [if_neg hAff] at h; simp at h

/-- WS-SM SM5.B.5 (invariant established): after a successful switch, core `c`
satisfies `currentThreadValidOnCore` — its new current thread (`= tid`) resolves
to a TCB in the object store.  The switch requires `tid` to resolve to a TCB up
front (the `.ok` precondition), and its *only* object-store write is the
*previous* current thread's register-context save at a *different* key
(`preemptCurrentOnCore_getTcb?_incoming`), so the lookup at `tid` is unchanged
across the transition.

This is the symmetric sibling of
`switchToThreadOnCore_establishes_queueCurrentConsistentOnCore`: together they
establish the two SM4.C current-thread conjuncts a successful switch must
discharge.  The proof routes entirely through the typed `getTcb?` accessor and
the `.get?`-method-form frame `preemptCurrentOnCore_getTcb?_incoming` (no raw
object-store `[·]?` bracket in the proof source), so it adds nothing to the AK7
`RAW_LOOKUP_TID` metric.  SM5.I.8 ("preservation by every transition") composes
this with `_establishes_queueCurrentConsistentOnCore`,
`_preserves_runQueueOnCore_wellFormed`, and `_preserves_objects_invExt` into the
full `schedulerInvariant_perCore` preservation. -/
theorem switchToThreadOnCore_establishes_currentThreadValidOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hInv : st.objects.invExt)
    (h : switchToThreadOnCore st c tid = .ok st') :
    currentThreadValidOnCore st' c := by
  unfold currentThreadValidOnCore
  rw [switchToThreadOnCore_sets_current st c tid st' h]
  -- Goal: `∃ tcb, st'.getTcb? tid = some tcb`.
  -- A successful switch requires `tid` to resolve to a TCB in the pre-state
  -- (the `getTcb? tid = none` arm is the `.error .schedulerInvariantViolation`
  -- branch).  Extract that witness from `h` by inverting the definition.
  have hPre : ∃ tidTcb, st.getTcb? tid = some tidTcb := by
    cases hTcb : st.getTcb? tid with
    | none => simp [switchToThreadOnCore, hTcb] at h
    | some t => exact ⟨t, rfl⟩
  obtain ⟨tidTcb, hTcb⟩ := hPre
  refine ⟨tidTcb, ?_⟩
  -- `st'.objects = (preempt).objects` (the switch writes only via the preempt),
  -- and `getTcb?` reads only `objects`, so the lookup at `tid` is the preempt's,
  -- and the preempt frames `tid` out (its write is at the *previous* current's
  -- key).  No raw `[·]?` bracket appears — AK7-clean.
  have hobj : st'.objects = (preemptCurrentOnCore st c tid).objects :=
    switchToThreadOnCore_objects_eq_preempt st c tid st' h
  have heq : st'.getTcb? tid = (preemptCurrentOnCore st c tid).getTcb? tid := by
    simp only [SystemState.getTcb?, hobj]
  rw [heq, preemptCurrentOnCore_getTcb?_incoming st c tid hInv, hTcb]

-- ============================================================================
-- §3c  Acquisition-order completeness (SM5.B.2, plan §4.4)
-- ============================================================================

/-- WS-SM SM5.B.2 (plan §4.4): the lock-set's projected keys form a
**`SchedLockId`-ascending acquisition sequence** — they are `Pairwise (· ≤ ·)`.
The `withLockSet` discipline (SM3.C) acquires a lock-set in ascending lock order;
this theorem certifies `switchToThreadOnCoreLockSet` is already in that order
(object lock before run-queue lock), so its canonical acquisition sequence is the
list itself.  Combined with the SchedLockId total order (SM5.A) and SM3.D's
ladder argument, this is the per-core switch's contribution to cross-core
deadlock-freedom.  (The two-element list needs no runtime sort; the dynamic
acquisition over a `SchedLockId` `LockSet` is wired by SM5.C's dispatch loop.) -/
theorem switchToThreadOnCoreLockSet_pairwise_le (c : CoreId) :
    ((switchToThreadOnCoreLockSet c).map (·.1)).Pairwise (· ≤ ·) := by
  have hle : SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
    (SchedLockId.object_lt_runQueue _ _).1
  simp only [switchToThreadOnCoreLockSet, List.map_cons, List.map_nil]
  exact List.Pairwise.cons
    (fun a ha => by rcases List.mem_singleton.mp ha with rfl; exact hle)
    (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil)

-- ============================================================================
-- §4  SM5.B.8 — Totality + decidability
-- ============================================================================

/-- WS-SM SM5.B.8: complete success classification — `switchToThreadOnCore`
succeeds **iff** `tid` resolves to a TCB whose CPU affinity admits core `c`.
Combined with `switchToThreadOnCore_rejects_remote` (the `affinity = some c'`,
`c' ≠ c` error) and the `getTcb? = none → schedulerInvariantViolation` arm, this
pins the operation's total input→outcome behaviour exactly: every input maps to
a determined `.ok`/`.error`, and the `.ok` set is characterised structurally
(this is the substantive form of "totality" — it replaces the vacuous
`∃ r, … = r`).  The forward direction reuses the `ok`-inversion case analysis;
the reverse is `switchToThreadOnCore_ok_of_admits`. -/
theorem switchToThreadOnCore_ok_iff (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    (∃ st', switchToThreadOnCore st c tid = .ok st')
      ↔ (∃ tidTcb, st.getTcb? tid = some tidTcb ∧ affinityAdmitsCore tidTcb c = true) := by
  constructor
  · rintro ⟨st', h⟩
    unfold switchToThreadOnCore at h
    cases hTcb : st.getTcb? tid with
    | none => simp [hTcb] at h
    | some t =>
      -- `cases hTcb` rewrites `st.getTcb? tid` to `some t` in the goal, so the
      -- witness equation is `rfl`.
      by_cases hAff : affinityAdmitsCore t c = true
      · exact ⟨t, rfl, hAff⟩
      · simp only [hTcb] at h
        rw [if_neg hAff] at h; simp at h
  · rintro ⟨tidTcb, hTcb, hAff⟩
    exact switchToThreadOnCore_ok_of_admits st c tid tidTcb hTcb hAff

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
