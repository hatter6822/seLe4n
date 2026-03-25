/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# Scheduler Invariant Definitions

This module contains invariant definitions for the scheduler subsystem: queue
uniqueness, current-thread validity, and queue/current consistency.

## Proof scope qualification (F-16)

**Structural theorems** (high assurance):
- `schedulerWellFormed_iff_queueCurrentConsistent`
- `queueCurrentConsistent_when_no_current`

Scheduler *preservation* theorems (e.g. `chooseThread_preserves_*`,
`schedule_preserves_*`, `handleYield_preserves_*`) live in the IPC and Capability
invariant modules where they compose with cross-subsystem bundles. This module
provides only the invariant definitions and basic structural lemmas.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-H12b/H-04: Dequeue-on-dispatch queue/current consistency.

seL4 semantics: the running thread is **removed** from the ready queue at
dispatch time and re-enqueued only on preemption, yield, or blocking.
When `current = some tid`, `tid` must **not** appear in the runnable queue.

This inverts the pre-H12b "strict" policy (`tid ∈ runnable`) to match seL4's
`switchToThread` which calls `tcbSchedDequeue` before setting `ksCurThread`. -/
def queueCurrentConsistent (s : SchedulerState) : Prop :=
  match s.current with
  | none => True
  | some tid => tid ∉ s.runnable

/-- Minimal scheduling well-formedness condition.

Alias for `queueCurrentConsistent` (dequeue-on-dispatch semantics since WS-H12b). -/
abbrev schedulerWellFormed (s : SchedulerState) : Prop :=
  queueCurrentConsistent s

/-- Scheduler invariant component #1 (M1 bundle v1): runnable queue has no duplicate TIDs. -/
def runQueueUnique (s : SchedulerState) : Prop :=
  s.runnable.Nodup

/-- Scheduler invariant component #2 (M1 bundle v1): the selected current thread, if any,
resolves to a TCB in the object store. -/
def currentThreadValid (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some tid => ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb)

/-- M-05/WS-E6: The currently scheduled thread (if any) belongs to the
active scheduling domain. This is the basic temporal partitioning guarantee:
the scheduler only runs threads in the current domain. -/
def currentThreadInActiveDomain (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.domain = st.scheduler.activeDomain
      | _ => True

/-- Scheduler Invariant Bundle v1 entrypoint used by composed IPC/architecture bundles.

The base triad used by cross-subsystem composition surfaces. -/
def schedulerInvariantBundle (st : SystemState) : Prop :=
  queueCurrentConsistent st.scheduler ∧ runQueueUnique st.scheduler ∧ currentThreadValid st

theorem schedulerWellFormed_iff_queueCurrentConsistent (s : SchedulerState) :
    schedulerWellFormed s ↔ queueCurrentConsistent s := by
  simp [schedulerWellFormed, queueCurrentConsistent]

theorem queueCurrentConsistent_when_no_current
    (s : SchedulerState)
    (hNone : s.current = none) :
    queueCurrentConsistent s := by
  simp [queueCurrentConsistent, hNone]

-- ============================================================================
-- M-04/WS-E6: Time-slice positivity invariant
-- ============================================================================

/-- M-04/WS-E6: All runnable threads have a positive time-slice remaining.
This ensures `timerTick` can always decrement without underflow, and that
preemption only occurs when a thread has exhausted its quantum. -/
def timeSlicePositive (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runnable →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.timeSlice > 0
    | _ => True

/-- WS-H12b: The current thread (if any) has a positive time-slice remaining.

Under dequeue-on-dispatch semantics, the current thread is removed from the
run queue at dispatch time, so `timeSlicePositive` (which quantifies over
runnable threads) no longer covers it. This companion predicate closes the gap
and is included in `schedulerInvariantBundleFull`. -/
def currentTimeSlicePositive (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some tid =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => tcb.timeSlice > 0
    | _ => True

-- ============================================================================
-- M-03/WS-E6: EDF scheduling invariant
-- ============================================================================

/-- M-03/WS-E6/WS-H6: The currently scheduled thread has the earliest deadline
among all runnable threads **in the same scheduling domain** at the same
priority level. This captures the domain-partitioned EDF policy: within equal
priority and equal domain, the thread with the most urgent deadline is selected.

**WS-H6 fix:** The original definition quantified over all runnable threads
regardless of domain, which was unprovable for a domain-aware scheduler that
only selects among same-domain candidates. Adding the domain constraint
aligns the invariant with `chooseBestRunnableInDomain` semantics. -/
def edfCurrentHasEarliestDeadline (st : SystemState) : Prop :=
  match st.scheduler.current with
  | none => True
  | some curTid =>
      match st.objects[curTid.toObjId]? with
      | some (.tcb curTcb) =>
          ∀ tid, tid ∈ st.scheduler.runnable →
            match st.objects[tid.toObjId]? with
            | some (.tcb tcb) =>
                tcb.domain = curTcb.domain →
                tcb.priority = curTcb.priority →
                curTcb.deadline.toNat = 0 ∨
                (tcb.deadline.toNat = 0 ∨ curTcb.deadline.toNat ≤ tcb.deadline.toNat)
            | _ => True
      | _ => True

-- ============================================================================
-- WS-H12c/H-03: Per-TCB register context invariant
-- ============================================================================

/-- WS-H12c/H-03: When a thread is current, the machine's register file
matches that thread's saved register context. This is established atomically
by the inline context restore step in `schedule`.

When `current = none` (idle), the invariant is vacuously satisfied.
When the current thread's object is not a TCB (impossible under
`currentThreadValid`), the invariant is vacuously satisfied. -/
def contextMatchesCurrent (st : SystemState) : Prop :=
  match st.scheduler.current with
  | some tid =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => st.machine.regs = tcb.registerContext
      | _ => True
  | none => True

-- ============================================================================
-- WS-H16/A-19: RunQueue threadPriority consistency predicate
-- ============================================================================

/-- WS-H16/A-19: Every thread in the RunQueue's membership set has a
corresponding entry in the `threadPriority` mapping, and vice versa.

This formalizes the structural invariant documented in `RunQueue` (lines 26-32)
which is maintained by `insert` (adds both) and `remove` (erases both), but
was previously only verified at runtime via `InvariantChecks.runQueueThreadPriorityConsistentB`.

The forward direction ensures no "priority-orphaned" thread can escape bucket
routing during scheduling. The reverse direction prevents stale priority entries
from accumulating after thread removal. -/
def runQueueThreadPriorityConsistent (st : SystemState) : Prop :=
  (∀ tid, tid ∈ st.scheduler.runQueue →
    st.scheduler.runQueue.threadPriority[tid]? ≠ none) ∧
  (∀ tid, st.scheduler.runQueue.threadPriority[tid]? ≠ none →
    tid ∈ st.scheduler.runQueue)

/-- WS-H16/A-19: `runQueueThreadPriorityConsistent` holds for the empty
default scheduler state. -/
theorem runQueueThreadPriorityConsistent_default :
    runQueueThreadPriorityConsistent default := by
  constructor
  · intro tid hMem
    exact absurd hMem (RunQueue.not_mem_empty tid)
  · intro tid hPrio
    exfalso; apply hPrio
    have : (∅ : SeLe4n.Kernel.RobinHood.RHTable ThreadId Priority).get? tid = none :=
      RHTable_get?_empty 16 (by omega)
    simp only [default, Inhabited.default, SeLe4n.Kernel.RunQueue.empty,
               RHTable_getElem?_eq_get?, EmptyCollection.emptyCollection] at this ⊢
    exact this

-- ============================================================================
-- WS-H6: Full scheduler invariant bundle
-- ============================================================================

-- Full Scheduler Invariant Bundle — extends the structural triad with
-- `timeSlicePositive`, `currentTimeSlicePositive`,
-- `edfCurrentHasEarliestDeadline`, `contextMatchesCurrent`, and
-- `runnableThreadsAreTCBs` (WS-F6/D3 6-tuple extension).

-- ============================================================================
-- WS-F6/D3: Runnable threads type-safety invariant
-- ============================================================================

/-- WS-F6/D3/MED-06: Every thread ID in the scheduler's runnable queue
corresponds to a valid TCB in the object store.

This is a type-safety backstop for the scheduler: without it, a lifecycle
`retypeObject` that overwrites a TCB with a non-TCB object while leaving the
thread ID in the run queue could cause `chooseThread` to read TCB fields from
a non-TCB object. `currentThreadValid` only covers the *current* thread;
this predicate covers *all* runnable threads. -/
def runnableThreadsAreTCBs (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runnable →
    ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb)

/-- WS-F6/D3: Default state has empty run queue, so the predicate is vacuously true. -/
theorem default_runnableThreadsAreTCBs :
    runnableThreadsAreTCBs (default : SystemState) := by
  intro tid hMem
  have : (default : SystemState).scheduler.runnable = [] := by native_decide
  rw [this] at hMem; simp at hMem

/-- WS-F6/D3: runnableThreadsAreTCBs is preserved when objects are unchanged. -/
theorem runnableThreadsAreTCBs_of_scheduler_objects_eq
    (st st' : SystemState)
    (hInv : runnableThreadsAreTCBs st)
    (hSchedEq : st'.scheduler = st.scheduler)
    (hObjEq : st'.objects = st.objects) :
    runnableThreadsAreTCBs st' := by
  intro tid hMem; rw [hSchedEq] at hMem; rw [hObjEq]; exact hInv tid hMem

-- ============================================================================
-- WS-H6: RunQueue priority-match predicate
-- ============================================================================

/-- WS-H6: The RunQueue's recorded `threadPriority` mapping matches the actual
TCB priority for every run-queue member.

This is an external-consistency predicate bridging the RunQueue's internal
`threadPriority` field to the authoritative TCB priority in the object store.
Together with `RunQueue.wellFormed`, it enables the bucket-first scheduling
proof: if a thread has the same priority as the selected candidate, it must
reside in the same priority bucket. -/
def schedulerPriorityMatch (st : SystemState) : Prop :=
  ∀ tid, tid ∈ st.scheduler.runQueue →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
        st.scheduler.runQueue.threadPriority[tid]? = some tcb.priority
    | _ => True

/-- R6-D/L-12: Extended full scheduler invariant bundle.
    7-tuple: base triad + timeSlice + EDF + context + runnableAreTCBs + priorityMatch.
    `schedulerPriorityMatch` ensures the RunQueue's priority index stays in sync
    with the authoritative TCB priority in the object store. -/
def schedulerInvariantBundleFull (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ timeSlicePositive st ∧
  currentTimeSlicePositive st ∧ edfCurrentHasEarliestDeadline st ∧
  contextMatchesCurrent st ∧ runnableThreadsAreTCBs st ∧
  schedulerPriorityMatch st

/-- Project the structural triad from the full bundle. -/
theorem schedulerInvariantBundleFull_to_base {st : SystemState}
    (h : schedulerInvariantBundleFull st) : schedulerInvariantBundle st :=
  h.1

/-- WS-H12e: Project `contextMatchesCurrent` from the full scheduler bundle. -/
theorem schedulerInvariantBundleFull_to_contextMatchesCurrent {st : SystemState}
    (h : schedulerInvariantBundleFull st) : contextMatchesCurrent st :=
  h.2.2.2.2.1

/-- R6-D: Project `schedulerPriorityMatch` from the full scheduler bundle. -/
theorem schedulerInvariantBundleFull_to_priorityMatch {st : SystemState}
    (h : schedulerInvariantBundleFull st) : schedulerPriorityMatch st :=
  h.2.2.2.2.2.2

/-- R6-D: schedulerPriorityMatch is preserved when both runQueue and objects
    are unchanged. -/
theorem schedulerPriorityMatch_of_runQueue_objects_eq
    (st st' : SystemState)
    (hInv : schedulerPriorityMatch st)
    (hRQEq : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hObjEq : st'.objects = st.objects) :
    schedulerPriorityMatch st' := by
  intro tid hMem; rw [hRQEq] at hMem; rw [hRQEq, hObjEq]; exact hInv tid hMem

/-- R6-D: schedulerPriorityMatch after inserting the current thread at its priority.
    If the current thread has a TCB at its ObjId with the given priority,
    inserting it at that priority preserves the priority match. -/
theorem schedulerPriorityMatch_insert
    (st : SystemState) (curTid : ThreadId) (curTcb : TCB)
    (hPM : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hCur : st.scheduler.current = some curTid)
    (hObj : st.objects[curTid.toObjId]? = some (.tcb curTcb)) :
    ∀ tid, tid ∈ st.scheduler.runQueue.insert curTid curTcb.priority →
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) =>
        (st.scheduler.runQueue.insert curTid curTcb.priority).threadPriority[tid]? = some tcb.priority
      | _ => True := by
  intro tid hMem
  have hNotMem : curTid ∉ st.scheduler.runQueue := by
    simp [queueCurrentConsistent, hCur] at hQCC
    intro h; exact hQCC ((RunQueue.mem_toList_iff_mem _ _).2 h)
  have hContF : st.scheduler.runQueue.contains curTid = false := by
    cases h : st.scheduler.runQueue.contains curTid; rfl; exact absurd h hNotMem
  rw [RunQueue.mem_insert] at hMem
  rw [RunQueue.insert_threadPriority]; simp only [hContF, Bool.false_eq_true, ↓reduceIte]
  cases hMem with
  | inl hOld =>
    have hNeq : curTid ≠ tid := fun h => hNotMem (h ▸ hOld)
    have hBEq : (curTid == tid) = false := by
      cases h : (curTid == tid) <;> simp_all
    -- The goal has `if curTid == tid = true then ... else ...`
    -- After insert_threadPriority, ite on BEq
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExt]
    simp only [hBEq, Bool.false_eq_true, ↓reduceIte]
    have := hPM tid hOld
    simp only [RHTable_getElem?_eq_get?] at this; exact this
  | inr hEq =>
    subst hEq
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExt]
    simp only [beq_self_eq_true, ↓reduceIte]
    simp only [RHTable_getElem?_eq_get?] at hObj; rw [hObj]

-- ============================================================================
-- T5-M (M-SCH-3): threadPriority ↔ membership consistency
-- ============================================================================

/-- T5-M (M-SCH-3): The `threadPriority` and `membership` fields of the RunQueue
    are bidirectionally consistent: a thread has a `threadPriority` entry if and
    only if it appears in the `membership` set.

    This was previously an implicit invariant (RunQueue.lean lines 46-52)
    maintained structurally by `insert` (which adds to both) and `remove`
    (which erases from both), but not formally proven. This definition makes
    the invariant explicit and verifiable. -/
def threadPriority_membership_consistent (rq : RunQueue) : Prop :=
  (∀ tid, rq.threadPriority[tid]? ≠ none → rq.membership.contains tid = true) ∧
  (∀ tid, rq.membership.contains tid = true → rq.threadPriority[tid]? ≠ none)

/-- T5-M: The empty RunQueue satisfies threadPriority/membership consistency. -/
theorem threadPriority_membership_consistent_empty :
    threadPriority_membership_consistent RunQueue.empty := by
  constructor
  · intro tid h
    exfalso; apply h
    have : (∅ : SeLe4n.Kernel.RobinHood.RHTable ThreadId Priority).get? tid = none :=
      RHTable_get?_empty 16 (by omega)
    simp only [RunQueue.empty, RHTable_getElem?_eq_get?, EmptyCollection.emptyCollection] at this ⊢
    exact this
  · intro tid h
    exact absurd (show tid ∈ (RunQueue.empty : RunQueue) from h) (RunQueue.not_mem_empty tid)

/-- T5-M: `runQueueThreadPriorityConsistent` can be derived from
    `threadPriority_membership_consistent`.

    The `RunQueue.Membership` instance defines `tid ∈ rq` as
    `rq.membership.contains tid = true`, so the proof directly connects
    membership-set presence with `threadPriority` presence.

    This closes the M-SCH-3 gap: the `threadPriority`/`membership` relationship
    is no longer an external hypothesis — it follows from the formalized predicate. -/
theorem runQueueThreadPriorityConsistent_of_tpmc
    (st : SystemState)
    (hTPMC : threadPriority_membership_consistent st.scheduler.runQueue) :
    runQueueThreadPriorityConsistent st := by
  constructor
  · intro tid hMem
    -- tid ∈ runQueue ↔ membership.contains tid = true
    exact hTPMC.2 tid hMem
  · intro tid hPrio
    -- threadPriority[tid]? ≠ none → membership.contains tid = true
    exact hTPMC.1 tid hPrio

/-- T5-M: `RunQueue.insert` preserves `threadPriority_membership_consistent`.
    Insert adds tid to both `membership` and `threadPriority` atomically,
    maintaining bidirectional consistency. When tid is already present,
    insert is a no-op and the invariant trivially holds. -/
theorem threadPriority_membership_consistent_insert
    (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (hTPMC : threadPriority_membership_consistent rq) :
    threadPriority_membership_consistent (rq.insert tid prio) := by
  unfold threadPriority_membership_consistent
  by_cases hContains : rq.contains tid
  · -- tid already in queue: insert returns rq unchanged
    have : rq.insert tid prio = rq := by unfold RunQueue.insert; simp [hContains]
    rw [this]; exact hTPMC
  · -- tid not in queue: both membership and threadPriority updated
    have hTPEq : (rq.insert tid prio).threadPriority = rq.threadPriority.insert tid prio := by
      rw [RunQueue.insert_threadPriority]; simp [hContains]
    have hMemEq : (rq.insert tid prio).membership = rq.membership.insert tid := by
      unfold RunQueue.insert; simp [hContains]
    constructor
    · intro tid' hTP
      rw [hMemEq]
      rw [RHTable_getElem?_eq_get?, hTPEq] at hTP
      by_cases hEq : (tid == tid') = true
      · have hEqV := eq_of_beq hEq; subst hEqV
        exact RobinHood.RHSet.contains_insert_self rq.membership tid rq.mem_invExt
      · have hTP' : rq.threadPriority.get? tid' ≠ none := by
          rwa [RobinHood.RHTable.getElem?_insert_ne rq.threadPriority tid tid' prio hEq
              rq.threadPrio_invExt] at hTP
        rw [RobinHood.RHSet.contains_insert_ne rq.membership tid tid' hEq rq.mem_invExt]
        exact hTPMC.1 tid' (by rwa [RHTable_getElem?_eq_get?])
    · intro tid' hMem
      rw [hMemEq] at hMem
      rw [RHTable_getElem?_eq_get?, hTPEq]
      by_cases hEq : (tid == tid') = true
      · have hEqV := eq_of_beq hEq; subst hEqV
        rw [RobinHood.RHTable.getElem?_insert_self rq.threadPriority tid prio rq.threadPrio_invExt]
        simp
      · rw [RobinHood.RHTable.getElem?_insert_ne rq.threadPriority tid tid' prio hEq
            rq.threadPrio_invExt, ← RHTable_getElem?_eq_get?]
        rw [RobinHood.RHSet.contains_insert_ne rq.membership tid tid' hEq rq.mem_invExt] at hMem
        exact hTPMC.2 tid' hMem

/-- T5-M: `RunQueue.remove` preserves `threadPriority_membership_consistent`.
    Remove erases tid from both `membership` and `threadPriority` atomically,
    maintaining bidirectional consistency. -/
theorem threadPriority_membership_consistent_remove
    (rq : RunQueue) (tid : ThreadId)
    (hTPMC : threadPriority_membership_consistent rq) :
    threadPriority_membership_consistent (rq.remove tid) := by
  unfold threadPriority_membership_consistent
  have hTP : (rq.remove tid).threadPriority = rq.threadPriority.erase tid := by
    unfold RunQueue.remove; rfl
  have hMem : (rq.remove tid).membership = rq.membership.erase tid := by
    unfold RunQueue.remove; rfl
  constructor
  · intro tid' hTP'
    simp only [RHTable_getElem?_eq_get?, hTP] at hTP'
    by_cases hEq : (tid == tid') = true
    · -- tid == tid': erase_self yields none, contradiction
      have hEqV := eq_of_beq hEq; subst hEqV
      rw [RobinHood.RHTable.getElem?_erase_self rq.threadPriority tid rq.threadPrio_invExt] at hTP'
      exact absurd rfl hTP'
    · rw [RobinHood.RHTable.getElem?_erase_ne rq.threadPriority tid tid' hEq
          rq.threadPrio_invExt rq.threadPrio_sizeOk] at hTP'
      rw [hMem, RobinHood.RHSet.contains_erase_ne rq.membership tid tid' hEq rq.mem_invExt
          rq.mem_sizeOk]
      have : rq.threadPriority[tid']? ≠ none := by
        rw [RHTable_getElem?_eq_get?]; exact hTP'
      exact hTPMC.1 tid' this
  · intro tid' hMem'
    rw [hMem] at hMem'
    by_cases hEq : (tid == tid') = true
    · have hEqV := eq_of_beq hEq
      subst hEqV
      rw [RobinHood.RHSet.contains_erase_self rq.membership tid rq.mem_invExt] at hMem'
      exact absurd hMem' (by simp)
    · rw [RobinHood.RHSet.contains_erase_ne rq.membership tid tid' hEq rq.mem_invExt
          rq.mem_sizeOk] at hMem'
      simp only [RHTable_getElem?_eq_get?, hTP]
      rw [RobinHood.RHTable.getElem?_erase_ne rq.threadPriority tid tid' hEq
          rq.threadPrio_invExt rq.threadPrio_sizeOk, ← RHTable_getElem?_eq_get?]
      exact hTPMC.2 tid' hMem'

end SeLe4n.Kernel
