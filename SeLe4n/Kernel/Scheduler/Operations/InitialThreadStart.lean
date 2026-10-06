-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.IntermediateState
import SeLe4n.Kernel.Scheduler.Operations.Core

/-!
# WS-BP BP7.11 — starting a configured initial thread

The boot installs a deployment's threads `.Inactive`: `bootSafeTcbCheck`
requires it, since a configuration describing a thread mid flight would describe
state no boot built.  A thread the deployment **designates** as an initial
thread is then *started* by this operation — marked `.Ready` and placed on its
home core's run queue — after the idle enqueue, so each core's first scheduling
point dispatches it ahead of that core's idle thread by priority.

**One body, the kernel model's.**  The start is `enqueueRunnableOnCore` — the
step every wake and resume ends in — preceded by the one field it does not
write, the thread-state flag.  A queued thread whose flag still read `.Inactive`
would falsify `threadInactiveFlagConsistent` on the first state the kernel runs.
It is the boot's counterpart of `enqueueIdleThreadOnCore` and lives in the
kernel model for the same reason (`v0.35.68`): a second body in the boot would
be a second answer to "what does it mean to make a thread runnable".

**What it does not do is resume.**  `resumeThreadOnCore` ends in a scheduling
point, which at boot would dispatch the thread on the boot core and leave a
current slot set before any core has entered the kernel — the state
`bootFromPlatformCheckedWithIdleThreads_currentAllNone` exists to rule out.
Every current slot stays `none`; dispatch is each core's own first scheduling
point.

§1 is the operation and its admissibility, §2 what it writes when admissible,
§3 the four `IntermediateState` witnesses (in every branch, admissible or not),
§4 the run-queue facts the boot's bundle theorem reads.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- §1  The operation
-- ============================================================================

/-- **WS-BP BP7.11**: the TCB a started thread is stored as — `.Ready`, and
`ipcState := .ready` because that is what the enqueue writes (a configured
thread already carries it, `bootSafeTcbCheck`). -/
def startedThread (tcb : TCB) : TCB :=
  { tcb with threadState := .Ready, ipcState := .ready }

/-- **WS-BP BP7.11**: may the boot start `tid`?  It is a stored thread, still
`.Inactive`, carrying no inherited boost (so its run-queue key is its own base
priority), with a positive time slice, and placed on no core.

Fail-closed at the caller: a thread the boot cannot start refuses the boot
rather than being skipped, and a thread named twice is refused at its second
occurrence, by which point it is `.Ready` and queued. -/
def initialThreadStartable (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some tcb =>
      (tcb.threadState == .Inactive) && tcb.pipBoost.isNone &&
      decide (0 < tcb.timeSlice) &&
      !runnableOnSomeCore st tid && !runningOnSomeCore st tid
  | none => false

/-- **WS-BP BP7.11**: start `tid` — mark it `.Ready`, then the kernel model's
own enqueue on its home core. -/
def startInitialThreadOnCore (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  enqueueRunnableOnCore (st.updateTcb tid fun t => { t with threadState := .Ready })
    (determineTargetCore st tid) tid

/-- **WS-BP BP7.11**: what `initialThreadStartable` says, as facts. -/
theorem initialThreadStartable_spec {st : SystemState} {tid : SeLe4n.ThreadId}
    (h : initialThreadStartable st tid = true) :
    ∃ tcb, st.getTcb? tid = some tcb ∧ tcb.threadState = .Inactive ∧
      tcb.pipBoost = none ∧ 0 < tcb.timeSlice ∧
      runnableOnSomeCore st tid = false ∧ runningOnSomeCore st tid = false := by
  unfold initialThreadStartable at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨tcb, rfl, h1, h2, h3, h4, h5⟩

-- ============================================================================
-- §2  What the start writes
-- ============================================================================

/-- **WS-BP BP7.11** (the decomposition): on a thread that resolves and is
queued nowhere, the start is two writes at the thread's key — the flag, then
the enqueue's `.ready` — and one run-queue insert on its home core at its
boosted priority, with the home core's reschedule-pending flag raised by the
enqueue (the KSC-1 accumulator).  Everything the other lemmas say is read off
this. -/
theorem startInitialThreadOnCore_eq {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hT : st.getTcb? tid = some tcb) (hNR : runnableOnSomeCore st tid = false)
    (hInv : st.objects.invExt) :
    startInitialThreadOnCore st tid =
      { st with
        objects := (st.objects.insert tid.toObjId
            (.tcb { tcb with threadState := .Ready })).insert tid.toObjId
            (.tcb (startedThread tcb))
        scheduler := (st.scheduler.setRunQueueOnCore (determineTargetCore st tid)
          ((st.scheduler.runQueueOnCore (determineTargetCore st tid)).insert tid
            tcb.boostedPriority)).markReschedulePendingOnCore (determineTargetCore st tid) } := by
  unfold startInitialThreadOnCore
  rw [SystemState.updateTcb_eq_of_some hT]
  have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
        some { tcb with threadState := .Ready } := by
    rw [SystemState.getTcb?_eq_some_iff]
    exact RHTable.getElem?_insert_self st.objects _ _ hInv
  unfold enqueueRunnableOnCore
  rw [SystemState.getTcbWitnessed?_eq_some hT1]
  have hNR1 : runnableOnSomeCore ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState) tid = false := hNR
  simp only [hNR1, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **WS-BP BP7.11**: on a thread that resolves to nothing the start is the
identity — both steps look the thread up and find nothing. -/
theorem startInitialThreadOnCore_eq_of_none {st : SystemState} {tid : SeLe4n.ThreadId}
    (hT : st.getTcb? tid = none) : startInitialThreadOnCore st tid = st := by
  unfold startInitialThreadOnCore
  rw [SystemState.updateTcb_eq_self_of_none hT]
  unfold enqueueRunnableOnCore
  rw [SystemState.getTcbWitnessed?_eq_none hT]

/-- **WS-BP BP7.11**: on a thread already queued the start writes the flag and
nothing else — the enqueue declines a queued thread.  (`initialThreadStartable`
refuses that case; stated so every witness below is total.) -/
theorem startInitialThreadOnCore_eq_of_runnable {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : runnableOnSomeCore st tid = true)
    (hInv : st.objects.invExt) :
    startInitialThreadOnCore st tid =
      { st with objects := (st.objects.insert tid.toObjId
          (.tcb { tcb with threadState := .Ready })) } := by
  unfold startInitialThreadOnCore
  rw [SystemState.updateTcb_eq_of_some hT]
  have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
        some { tcb with threadState := .Ready } := by
    rw [SystemState.getTcb?_eq_some_iff]
    exact RHTable.getElem?_insert_self st.objects _ _ hInv
  unfold enqueueRunnableOnCore
  rw [SystemState.getTcbWitnessed?_eq_some hT1]
  have hNR1 : runnableOnSomeCore ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState) tid = true := hNR
  simp only [hNR1, ↓reduceIte]

/-- **WS-BP BP7.11**: the started thread's key holds `startedThread tcb`. -/
theorem startInitialThreadOnCore_objects_self {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : runnableOnSomeCore st tid = false)
    (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).objects[tid.toObjId]? =
      some (.tcb (startedThread tcb)) := by
  rw [startInitialThreadOnCore_eq hT hNR hInv]
  exact RHTable.getElem?_insert_self _ _ _ (RHTable_insert_preserves_invExt _ _ _ hInv)

/-- **WS-BP BP7.11** (frame): every other key is untouched. -/
theorem startInitialThreadOnCore_objects_ne {st : SystemState} {tid : SeLe4n.ThreadId}
    (k : SeLe4n.ObjId) (hNe : tid.toObjId ≠ k) (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).objects[k]? = st.objects[k]? := by
  have hNeB : ¬(tid.toObjId == k) = true := fun h => hNe (eq_of_beq h)
  cases hT : st.getTcb? tid with
  | none =>
    unfold startInitialThreadOnCore
    rw [SystemState.updateTcb_eq_self_of_none hT]
    unfold enqueueRunnableOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hT]
  | some tcb =>
    cases hNR : runnableOnSomeCore st tid with
    | false =>
      rw [startInitialThreadOnCore_eq hT hNR hInv]
      show ((st.objects.insert _ _).insert _ _).get? k = st.objects.get? k
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeB (RHTable_insert_preserves_invExt _ _ _ hInv),
        RHTable.getElem?_insert_ne _ _ _ _ hNeB hInv]
    | true =>
      unfold startInitialThreadOnCore
      rw [SystemState.updateTcb_eq_of_some hT]
      have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
          (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
            some { tcb with threadState := .Ready } := by
        rw [SystemState.getTcb?_eq_some_iff]
        exact RHTable.getElem?_insert_self st.objects _ _ hInv
      unfold enqueueRunnableOnCore
      rw [SystemState.getTcbWitnessed?_eq_some hT1]
      have hNR1 : runnableOnSomeCore ({ st with objects := (st.objects.insert tid.toObjId
          (.tcb { tcb with threadState := .Ready })) } : SystemState) tid = true := hNR
      simp only [hNR1, ↓reduceIte]
      show (st.objects.insert _ _).get? k = st.objects.get? k
      exact RHTable.getElem?_insert_ne _ _ _ _ hNeB hInv

/-- **WS-BP BP7.11**: the start writes the run queue and the reschedule-pending
flags (the KSC-1 accumulator the enqueue raises), and no other scheduler
field. -/
theorem startInitialThreadOnCore_scheduler_runQueueOnly (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    ∃ rq rp, (startInitialThreadOnCore st tid).scheduler =
      { st.scheduler with runQueue := rq, reschedulePending := rp } := by
  unfold startInitialThreadOnCore enqueueRunnableOnCore
  split
  · split
    · exact ⟨st.scheduler.runQueue, st.scheduler.reschedulePending,
        by rw [SystemState.updateTcb_scheduler]⟩
    · exact ⟨_, _, by rw [SystemState.updateTcb_scheduler]; rfl⟩
  · exact ⟨st.scheduler.runQueue, st.scheduler.reschedulePending,
      by rw [SystemState.updateTcb_scheduler]⟩

/-- **WS-BP BP7.11**: the start writes no current slot on any core — it does
not dispatch. -/
theorem startInitialThreadOnCore_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (startInitialThreadOnCore st tid).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  obtain ⟨rq, rp, hrq⟩ := startInitialThreadOnCore_scheduler_runQueueOnly st tid
  rw [hrq]; rfl

/-- **WS-BP BP7.11**: the home core's run queue gains the thread at its
boosted priority. -/
theorem startInitialThreadOnCore_runQueueOnCore_self {st : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hT : st.getTcb? tid = some tcb)
    (hNR : runnableOnSomeCore st tid = false) (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).scheduler.runQueueOnCore (determineTargetCore st tid) =
      (st.scheduler.runQueueOnCore (determineTargetCore st tid)).insert tid
        tcb.boostedPriority := by
  rw [startInitialThreadOnCore_eq hT hNR hInv]
  show ((_ : SchedulerState).markReschedulePendingOnCore _).runQueueOnCore _ = _
  rw [SchedulerState.markReschedulePendingOnCore_runQueueOnCore]
  exact SchedulerState.setRunQueueOnCore_runQueueOnCore_self _ _ _

/-- **WS-BP BP7.11**: where the start writes nothing to the scheduler — the
thread resolves to nothing, or is already queued — every core's queue is as
before. -/
theorem startInitialThreadOnCore_runQueueOnCore_ne' (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : st.getTcb? tid = none ∨ runnableOnSomeCore st tid = true) (c : CoreId) :
    (startInitialThreadOnCore st tid).scheduler.runQueueOnCore c =
      st.scheduler.runQueueOnCore c := by
  rcases h with hT | hNR
  · rw [startInitialThreadOnCore_eq_of_none hT]
  · cases hT : st.getTcb? tid with
    | none => rw [startInitialThreadOnCore_eq_of_none hT]
    | some tcb => rw [startInitialThreadOnCore_eq_of_runnable hT hNR hInv]

/-- **WS-BP BP7.11** (cross-core frame): every other core's run queue is
untouched. -/
theorem startInitialThreadOnCore_runQueueOnCore_ne (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (hc : determineTargetCore st tid ≠ c)
    (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).scheduler.runQueueOnCore c =
      st.scheduler.runQueueOnCore c := by
  cases hT : st.getTcb? tid with
  | none =>
    unfold startInitialThreadOnCore
    rw [SystemState.updateTcb_eq_self_of_none hT]
    unfold enqueueRunnableOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hT]
  | some tcb =>
    cases hNR : runnableOnSomeCore st tid with
    | false =>
      rw [startInitialThreadOnCore_eq hT hNR hInv]
      show ((_ : SchedulerState).markReschedulePendingOnCore _).runQueueOnCore _ = _
      rw [SchedulerState.markReschedulePendingOnCore_runQueueOnCore]
      exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc
    | true =>
      unfold startInitialThreadOnCore enqueueRunnableOnCore
      split
      · split
        · rw [SystemState.updateTcb_scheduler]
        · rename_i hRun
          have : runnableOnSomeCore (st.updateTcb tid fun t => { t with threadState := .Ready }) tid =
              runnableOnSomeCore st tid := by
            unfold runnableOnSomeCore; rw [SystemState.updateTcb_scheduler]
          rw [this, hNR] at hRun
          exact absurd rfl hRun
      · rw [SystemState.updateTcb_scheduler]

-- ============================================================================
-- §3  The `IntermediateState` witnesses
-- ============================================================================

/-- An object-store insert beside any scheduler write keeps `allTablesInvExtK`:
the three run-queue conjuncts are fields of whatever `RunQueue` the boot core
ends up with, and every other table is untouched. -/
private theorem allTablesInvExtK_objects_insert (st : SystemState) (k : SeLe4n.ObjId)
    (v : KernelObject) (sch : SchedulerState) (h : st.allTablesInvExtK) :
    ({ st with objects := st.objects.insert k v, scheduler := sch } : SystemState).allTablesInvExtK := by
  unfold SystemState.allTablesInvExtK at h ⊢
  exact ⟨RHTable.insert_preserves_invExtK _ _ _ h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    RunQueue.byPrio_invExtK _, RunQueue.threadPrio_invExtK _,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, RunQueue.mem_invExtK _,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The two steps of the start as a chain of `{ _ with objects := insert … }`
writes (or none), with the scheduler replaced — the shape every witness reads. -/
private theorem startInitialThreadOnCore_cases (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    startInitialThreadOnCore st tid = st ∨
    (∃ t, startInitialThreadOnCore st tid =
      { st with objects := st.objects.insert tid.toObjId (.tcb t) }) ∨
    (∃ t₁ t₂ sch, startInitialThreadOnCore st tid =
      { st with objects := (st.objects.insert tid.toObjId (.tcb t₁)).insert tid.toObjId (.tcb t₂),
                scheduler := sch }) := by
  cases hT : st.getTcb? tid with
  | none =>
    left
    unfold startInitialThreadOnCore
    rw [SystemState.updateTcb_eq_self_of_none hT]
    unfold enqueueRunnableOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hT]
  | some tcb =>
    cases hNR : runnableOnSomeCore st tid with
    | false =>
      right; right
      exact ⟨_, _, _, startInitialThreadOnCore_eq hT hNR hInv⟩
    | true =>
      right; left
      refine ⟨{ tcb with threadState := .Ready }, ?_⟩
      unfold startInitialThreadOnCore
      rw [SystemState.updateTcb_eq_of_some hT]
      have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
          (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
            some { tcb with threadState := .Ready } := by
        rw [SystemState.getTcb?_eq_some_iff]
        exact RHTable.getElem?_insert_self st.objects _ _ hInv
      unfold enqueueRunnableOnCore
      rw [SystemState.getTcbWitnessed?_eq_some hT1]
      have hNR1 : runnableOnSomeCore ({ st with objects := (st.objects.insert tid.toObjId
          (.tcb { tcb with threadState := .Ready })) } : SystemState) tid = true := hNR
      simp only [hNR1, ↓reduceIte]

/-- **WS-BP BP7.11**: the start preserves `allTablesInvExtK`. -/
theorem startInitialThreadOnCore_preserves_allTablesInvExtK (st : SystemState)
    (tid : SeLe4n.ThreadId) (h : st.allTablesInvExtK) :
    (startInitialThreadOnCore st tid).allTablesInvExtK := by
  rcases startInitialThreadOnCore_cases st tid h.1.1 with hE | ⟨t, hE⟩ | ⟨t₁, t₂, sch, hE⟩
  · rw [hE]; exact h
  · rw [hE]; exact allTablesInvExtK_objects_insert st _ (.tcb t) st.scheduler h
  · rw [hE]
    have h1 := allTablesInvExtK_objects_insert st tid.toObjId (.tcb t₁) st.scheduler h
    exact allTablesInvExtK_objects_insert
      ({ st with objects := st.objects.insert tid.toObjId (.tcb t₁), scheduler := st.scheduler } :
        SystemState) tid.toObjId (.tcb t₂) sch h1

/-- **WS-BP BP7.11**: **what the start can leave at a key** — the pre-state's
object, or, where the pre-state held a TCB, that TCB with its flag set `.Ready`
and (on the branch that enqueues) its IPC state `.ready`.  Every object-level
witness the boot needs is read off this. -/
theorem startInitialThreadOnCore_objects_cases (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObj : (startInitialThreadOnCore st tid).objects[k]? = some obj) :
    st.objects[k]? = some obj ∨
    ∃ t, st.objects[k]? = some (.tcb t) ∧
      (obj = .tcb { t with threadState := .Ready } ∨ obj = .tcb (startedThread t)) := by
  by_cases hEq : tid.toObjId = k
  · subst hEq
    cases hT : st.getTcb? tid with
    | none =>
      left; rw [startInitialThreadOnCore_eq_of_none hT] at hObj; exact hObj
    | some tcb =>
      right
      refine ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT, ?_⟩
      cases hNR : runnableOnSomeCore st tid with
      | false =>
        rw [startInitialThreadOnCore_objects_self hT hNR hInv] at hObj
        cases hObj; exact Or.inr rfl
      | true =>
        rw [startInitialThreadOnCore_eq_of_runnable hT hNR hInv] at hObj
        change (st.objects.insert _ _).get? _ = _ at hObj
        rw [RHTable.getElem?_insert_self _ _ _ hInv] at hObj
        cases hObj; exact Or.inl rfl
  · left
    rw [← startInitialThreadOnCore_objects_ne k hEq hInv]
    exact hObj

/-- **WS-BP BP7.11** (the converse frame): an object that is not a TCB is where
it was — the start writes only at a key that held one. -/
theorem startInitialThreadOnCore_objects_of_nonTcb (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (obj : KernelObject) (hNot : ∀ t, obj ≠ .tcb t)
    (hObj : st.objects[k]? = some obj) :
    (startInitialThreadOnCore st tid).objects[k]? = some obj := by
  by_cases hEq : tid.toObjId = k
  · subst hEq
    cases hT : st.getTcb? tid with
    | none => rw [startInitialThreadOnCore_eq_of_none hT]; exact hObj
    | some tcb =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT] at hObj
      cases hObj; exact absurd rfl (hNot tcb)
  · rw [startInitialThreadOnCore_objects_ne k hEq hInv]; exact hObj

/-- **WS-BP BP7.11**: a thread that resolved still resolves. -/
theorem startInitialThreadOnCore_getTcb?_isSome (st : SystemState)
    (tid t : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : (st.getTcb? t).isSome = true) :
    ((startInitialThreadOnCore st tid).getTcb? t).isSome = true := by
  obtain ⟨tcb, hT⟩ := Option.isSome_iff_exists.mp h
  have hObj := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  by_cases hEq : tid.toObjId = t.toObjId
  · have hTid : tid = t := ThreadId.toObjId_injective _ _ hEq
    subst hTid
    cases hNR : runnableOnSomeCore st tid with
    | false =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
        (startInitialThreadOnCore_objects_self hT hNR hInv)]; rfl
    | true =>
      have : (startInitialThreadOnCore st tid).getTcb? tid =
          some { tcb with threadState := .Ready } := by
        rw [SystemState.getTcb?_eq_some_iff, startInitialThreadOnCore_eq_of_runnable hT hNR hInv]
        exact RHTable.getElem?_insert_self st.objects _ _ hInv
      rw [this]; rfl
  · have : (startInitialThreadOnCore st tid).getTcb? t = some tcb := by
      rw [SystemState.getTcb?_eq_some_iff, startInitialThreadOnCore_objects_ne _ hEq hInv]
      exact hObj
    rw [this]; rfl

/-- **WS-BP BP7.11** (field frame): the start writes the object store and the
scheduler, and no other field of the state. -/
theorem startInitialThreadOnCore_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    startInitialThreadOnCore st tid =
      { st with objects := (startInitialThreadOnCore st tid).objects,
                scheduler := (startInitialThreadOnCore st tid).scheduler } := by
  cases hT : st.getTcb? tid with
  | none => rw [startInitialThreadOnCore_eq_of_none hT]
  | some tcb =>
    cases hNR : runnableOnSomeCore st tid with
    | false => rw [startInitialThreadOnCore_eq hT hNR hInv]
    | true => rw [startInitialThreadOnCore_eq_of_runnable hT hNR hInv]

/-- **WS-BP BP7.11**: the start preserves the object store's `invExt`. -/
theorem startInitialThreadOnCore_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).objects.invExt := by
  rcases startInitialThreadOnCore_cases st tid hInv with hE | ⟨t, hE⟩ | ⟨t₁, t₂, sch, hE⟩
  · rw [hE]; exact hInv
  · rw [hE]; exact RHTable_insert_preserves_invExt _ _ _ hInv
  · rw [hE]
    exact RHTable_insert_preserves_invExt _ _ _ (RHTable_insert_preserves_invExt _ _ _ hInv)

/-- **WS-BP BP7.11**: the start preserves the per-object CNode-slot invariant —
it writes a TCB, and every CNode it holds is the pre-state's. -/
theorem startInitialThreadOnCore_preserves_perObjectSlotsInvariant (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (h : perObjectSlotsInvariant st) :
    perObjectSlotsInvariant (startInitialThreadOnCore st tid) := by
  intro oid cn hObj
  rcases startInitialThreadOnCore_objects_cases st tid hInv oid _ hObj with
    hB | ⟨_, _, hT | hT⟩
  · exact h oid cn hB
  all_goals cases hT

/-- **WS-BP BP7.11**: the start preserves the per-object VSpace-mapping
invariant, for the same reason. -/
theorem startInitialThreadOnCore_preserves_perObjectMappingsInvariant (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (h : perObjectMappingsInvariant st) :
    perObjectMappingsInvariant (startInitialThreadOnCore st tid) := by
  intro oid vs hObj
  rcases startInitialThreadOnCore_objects_cases st tid hInv oid _ hObj with
    hB | ⟨_, _, hT | hT⟩
  · exact h oid vs hB
  all_goals cases hT

/-- **WS-BP BP7.11**: the start preserves the lifecycle metadata's consistency
with the object store — the flag write is `updateTcb`'s own theorem, and the
enqueue's is `rewriteObject`'s, beside a scheduler write neither reads. -/
theorem startInitialThreadOnCore_preserves_objectTypeMetadataConsistent (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hC : SystemState.objectTypeMetadataConsistent st) :
    SystemState.objectTypeMetadataConsistent (startInitialThreadOnCore st tid) := by
  have h1 := SystemState.updateTcb_preserves_objectTypeMetadataConsistent st tid
    (fun t => { t with threadState := .Ready }) hInv hC
  have hInv1 := SystemState.updateTcb_preserves_objects_invExt st tid
    (fun t => { t with threadState := .Ready }) hInv
  unfold startInitialThreadOnCore enqueueRunnableOnCore
  split
  · split
    · exact h1
    · exact SystemState.rewriteObject_preserves_objectTypeMetadataConsistent _ _ _
        (SystemState.rewriteAdmissible_tcb (by assumption) _) hInv1 h1
  · exact h1

-- ============================================================================
-- §4  Placement, classification, and the run-queue facts the boot reads
-- ============================================================================

/-- A thread queued on no core is not a member of any core's run queue. -/
theorem not_mem_runQueueOnCore_of_runnableOnSomeCore_false {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : runnableOnSomeCore st tid = false) (c : CoreId) :
    tid ∉ st.scheduler.runQueueOnCore c := by
  intro hMem
  unfold runnableOnSomeCore at h
  rw [List.any_eq_false] at h
  exact h c (mem_allCores c) hMem

/-- **WS-BP BP7.11** (placement frame): every other thread keeps its placement
— the start inserts one thread into one queue and writes no current slot. -/
theorem startInitialThreadOnCore_runnableOnSomeCore_ne (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (hNe : tid' ≠ tid) (hInv : st.objects.invExt) :
    runnableOnSomeCore (startInitialThreadOnCore st tid) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  congr 1; funext c
  by_cases hc : determineTargetCore st tid = c
  · subst hc
    cases hT : st.getTcb? tid with
    | none =>
      rw [startInitialThreadOnCore_runQueueOnCore_ne' st tid hInv (Or.inl hT)]
    | some tcb =>
      cases hNR : runnableOnSomeCore st tid with
      | true =>
        rw [startInitialThreadOnCore_runQueueOnCore_ne' st tid hInv (Or.inr hNR)]
      | false =>
        rw [startInitialThreadOnCore_runQueueOnCore_self hT hNR hInv]
        have := RunQueue.mem_insert
          (st.scheduler.runQueueOnCore (determineTargetCore st tid)) tid tcb.boostedPriority tid'
        simp only [RunQueue.mem_iff_contains] at this
        cases h1 : ((st.scheduler.runQueueOnCore (determineTargetCore st tid)).insert tid
            tcb.boostedPriority).contains tid' <;>
          cases h2 : (st.scheduler.runQueueOnCore (determineTargetCore st tid)).contains tid' <;>
          simp_all
  · rw [startInitialThreadOnCore_runQueueOnCore_ne st tid c hc hInv]

/-- **WS-BP BP7.11**: the same, for the running test — no current slot moves. -/
theorem startInitialThreadOnCore_runningOnSomeCore (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) :
    runningOnSomeCore (startInitialThreadOnCore st tid) tid' = runningOnSomeCore st tid' := by
  unfold runningOnSomeCore
  congr 1; funext c
  rw [startInitialThreadOnCore_currentOnCore]

/-- **WS-BP BP7.11**: the started thread is queued — on its home core. -/
theorem startInitialThreadOnCore_mem_self {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : runnableOnSomeCore st tid = false)
    (hInv : st.objects.invExt) :
    tid ∈ (startInitialThreadOnCore st tid).scheduler.runQueueOnCore
      (determineTargetCore st tid) := by
  rw [startInitialThreadOnCore_runQueueOnCore_self hT hNR hInv]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- **WS-BP BP7.11**: ...so it is placed on some core. -/
theorem startInitialThreadOnCore_runnableOnSomeCore_self {st : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hT : st.getTcb? tid = some tcb)
    (hNR : runnableOnSomeCore st tid = false) (hInv : st.objects.invExt) :
    runnableOnSomeCore (startInitialThreadOnCore st tid) tid = true := by
  unfold runnableOnSomeCore
  rw [List.any_eq_true]
  exact ⟨_, mem_allCores _, startInitialThreadOnCore_mem_self hT hNR hInv⟩

/-- **WS-BP BP7.11**: **the start keeps the full thread-state classification.**
The started thread is stored `.Ready` and is queued on no current slot, which is
what `inferThreadState` calls `.Ready`; every other thread keeps its record and
its placement.  So the boot state's `threadStateConsistent` — and with it the
inactive-flag relation the live decisions read — survives every start. -/
theorem startInitialThreadOnCore_preserves_threadStateConsistent {st : SystemState}
    {tid : SeLe4n.ThreadId} (hStart : initialThreadStartable st tid = true)
    (hInv : st.objects.invExt) (h : threadStateConsistent st) :
    threadStateConsistent (startInitialThreadOnCore st tid) := by
  obtain ⟨tcb, hT, _, _, _, hNR, hNRun⟩ := initialThreadStartable_spec hStart
  intro oid t hObj
  by_cases hEq : tid.toObjId = oid
  · subst hEq
    rw [startInitialThreadOnCore_objects_self hT hNR hInv] at hObj
    cases hObj
    show ThreadState.Ready = inferThreadState _ tid (startedThread tcb)
    unfold inferThreadState threadRunningOnSomeCore threadQueuedOnSomeCore
    rw [startInitialThreadOnCore_runningOnSomeCore, hNRun,
      startInitialThreadOnCore_runnableOnSomeCore_self hT hNR hInv]
    rfl
  · rw [startInitialThreadOnCore_objects_ne oid hEq hInv] at hObj
    rw [h oid t hObj]
    have hNe : (⟨oid.toNat⟩ : SeLe4n.ThreadId) ≠ tid := by
      intro hc; apply hEq; rw [← hc]; rfl
    unfold inferThreadState threadRunningOnSomeCore threadQueuedOnSomeCore
    rw [startInitialThreadOnCore_runningOnSomeCore,
      startInitialThreadOnCore_runnableOnSomeCore_ne st tid _ hNe hInv]

/-- **WS-BP BP7.11**: what the boot's bundle theorem reads of a core's run
queue — its members are distinct, and each is a stored TCB with a positive time
slice and no inherited boost, bucketed at its own base priority. -/
def runQueueBootSound (st : SystemState) (c : CoreId) : Prop :=
  (st.scheduler.runQueueOnCore c).toList.Nodup ∧
  ∀ tid, tid ∈ st.scheduler.runQueueOnCore c →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ 0 < tcb.timeSlice ∧
      tcb.pipBoost = none ∧
      (st.scheduler.runQueueOnCore c).threadPriority[tid]? = some tcb.priority

/-- **WS-BP BP7.11**: **the start keeps every core's run queue boot-sound.**
The started thread enters one queue at its boosted priority, which with no
boost is its base priority; every thread already queued is another thread,
whose record and bucket the start leaves alone. -/
theorem startInitialThreadOnCore_preserves_runQueueBootSound {st : SystemState}
    {tid : SeLe4n.ThreadId} (hStart : initialThreadStartable st tid = true)
    (hInv : st.objects.invExt) (c : CoreId) (h : runQueueBootSound st c) :
    runQueueBootSound (startInitialThreadOnCore st tid) c := by
  obtain ⟨tcb, hT, _, hBoost, hSlice, hNR, _⟩ := initialThreadStartable_spec hStart
  obtain ⟨hNodup, hMem⟩ := h
  unfold runQueueBootSound
  have hNotMem := not_mem_runQueueOnCore_of_runnableOnSomeCore_false hNR
  -- A thread already queued on `c` is not the started one, so its record is framed.
  have hOld : ∀ tid', tid' ∈ st.scheduler.runQueueOnCore c →
      (startInitialThreadOnCore st tid).objects[tid'.toObjId]? = st.objects[tid'.toObjId]? := by
    intro tid' hm
    apply startInitialThreadOnCore_objects_ne _ _ hInv
    intro hk
    have : tid = tid' := ThreadId.toObjId_injective _ _ hk
    subst this; exact hNotMem c hm
  by_cases hc : determineTargetCore st tid = c
  · subst hc
    rw [startInitialThreadOnCore_runQueueOnCore_self hT hNR hInv]
    refine ⟨RunQueue.insert_preserves_toList_nodup _ _ _ hNodup, ?_⟩
    intro tid' hm
    have hTP := RunQueue.insert_threadPriority
      (st.scheduler.runQueueOnCore (determineTargetCore st tid)) tid tcb.boostedPriority
    have hContains : (st.scheduler.runQueueOnCore (determineTargetCore st tid)).contains tid =
        false := RunQueue.contains_false_of_not_mem (hNotMem _)
    rw [hContains] at hTP
    simp only [Bool.false_eq_true, ↓reduceIte] at hTP
    have hExt := (st.scheduler.runQueueOnCore (determineTargetCore st tid)).threadPrio_invExtK.1
    rcases (RunQueue.mem_insert _ _ _ _).mp hm with hm | hEqT
    · obtain ⟨t, hObj, hPos, hB, hPrio⟩ := hMem tid' hm
      refine ⟨t, by rw [hOld tid' hm]; exact hObj, hPos, hB, ?_⟩
      have hNe : ¬(tid == tid') = true := by
        intro hb; have := eq_of_beq hb; subst this; exact hNotMem _ hm
      show (RunQueue.threadPriority _).get? tid' = _
      rw [hTP, RHTable.getElem?_insert_ne _ _ _ _ hNe hExt]
      exact hPrio
    · rw [hEqT]
      refine ⟨startedThread tcb, startInitialThreadOnCore_objects_self hT hNR hInv, hSlice,
        hBoost, ?_⟩
      show (RunQueue.threadPriority _).get? tid = _
      rw [hTP, RHTable.getElem?_insert_self _ _ _ hExt]
      show some (tcb.priority.raisedBy tcb.pipBoost) = some tcb.priority
      rw [hBoost]; rfl
  · rw [startInitialThreadOnCore_runQueueOnCore_ne st tid c hc hInv]
    refine ⟨hNodup, ?_⟩
    intro tid' hm
    rw [hOld tid' hm]
    exact hMem tid' hm

/-- **WS-BP BP7.11**: what it means for a thread to have been started — it is
queued on some core and stored `.Ready`. -/
def threadStarted (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  runnableOnSomeCore st tid = true ∧ ∃ t, st.getTcb? tid = some t ∧ t.threadState = .Ready

/-- **WS-BP BP7.11**: the start starts its thread. -/
theorem startInitialThreadOnCore_threadStarted {st : SystemState} {tid : SeLe4n.ThreadId}
    (hStart : initialThreadStartable st tid = true) (hInv : st.objects.invExt) :
    threadStarted (startInitialThreadOnCore st tid) tid := by
  obtain ⟨tcb, hT, _, _, _, hNR, _⟩ := initialThreadStartable_spec hStart
  exact ⟨startInitialThreadOnCore_runnableOnSomeCore_self hT hNR hInv, startedThread tcb,
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (startInitialThreadOnCore_objects_self hT hNR hInv),
    rfl⟩

/-- **WS-BP BP7.11**: a start leaves an already-started thread started — the
thread it admits is unqueued and `.Inactive`, so it is not that one. -/
theorem startInitialThreadOnCore_preserves_threadStarted {st : SystemState}
    {tid tid' : SeLe4n.ThreadId} (hStart : initialThreadStartable st tid = true)
    (hInv : st.objects.invExt) (h : threadStarted st tid') :
    threadStarted (startInitialThreadOnCore st tid) tid' := by
  obtain ⟨_, _, _, _, _, hNR, _⟩ := initialThreadStartable_spec hStart
  obtain ⟨hRun, t, hT, hReady⟩ := h
  have hNe : tid' ≠ tid := by
    intro hEq; subst hEq; rw [hRun] at hNR; cases hNR
  refine ⟨by rw [startInitialThreadOnCore_runnableOnSomeCore_ne st tid tid' hNe hInv]; exact hRun,
    t, ?_, hReady⟩
  have hNeO : tid.toObjId ≠ tid'.toObjId := fun hk => hNe (ThreadId.toObjId_injective _ _ hk).symm
  rw [SystemState.getTcb?_eq_some_iff, startInitialThreadOnCore_objects_ne _ hNeO hInv]
  exact (SystemState.getTcb?_eq_some_iff _ _ _).mp hT

/-- **WS-BP BP7.11**: a thread startable before a start of **another** thread is
startable after it — the start writes only its own thread's record, inserts
only its own thread into a queue, and sets no current slot. -/
theorem initialThreadStartable_of_start_ne {st : SystemState} {tid tid' : SeLe4n.ThreadId}
    (hNe : tid' ≠ tid) (hInv : st.objects.invExt)
    (h : initialThreadStartable st tid' = true) :
    initialThreadStartable (startInitialThreadOnCore st tid) tid' = true := by
  have hNeO : tid.toObjId ≠ tid'.toObjId := fun hk => hNe (ThreadId.toObjId_injective _ _ hk).symm
  have hT : (startInitialThreadOnCore st tid).getTcb? tid' = st.getTcb? tid' := by
    cases hT0 : st.getTcb? tid' with
    | none =>
      cases hT1 : (startInitialThreadOnCore st tid).getTcb? tid' with
      | none => rfl
      | some t =>
        rw [SystemState.getTcb?_eq_some_iff, startInitialThreadOnCore_objects_ne _ hNeO hInv,
          ← SystemState.getTcb?_eq_some_iff, hT0] at hT1
        cases hT1
    | some t =>
      rw [SystemState.getTcb?_eq_some_iff, startInitialThreadOnCore_objects_ne _ hNeO hInv]
      exact (SystemState.getTcb?_eq_some_iff _ _ _).mp hT0
  unfold initialThreadStartable at h ⊢
  rw [hT, startInitialThreadOnCore_runnableOnSomeCore_ne st tid tid' hNe hInv,
    startInitialThreadOnCore_runningOnSomeCore]
  exact h

end SeLe4n.Kernel
