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
priority), with a positive time slice, and placed on no core.  An idle thread is
never started: it runs only when its core has nothing queued, and never joins a
queue.

Fail-closed at the caller: a thread the boot cannot start refuses the boot
rather than being skipped, and a thread named twice is refused at its second
occurrence, by which point it is `.Ready` and queued. -/
def initialThreadStartable (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  !isIdleThreadId tid &&
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
  replace h := ((Bool.and_eq_true _ _).mp h).2
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨tcb, rfl, h1, h2, h3, h4, h5⟩

/-- A startable thread is no idle thread. -/
theorem initialThreadStartable_not_idle {st : SystemState} {tid : SeLe4n.ThreadId}
    (h : initialThreadStartable st tid = true) : isIdleThreadId tid = false := by
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  cases hI : isIdleThreadId tid
  · rfl
  · rw [hI] at h1; cases h1

/-- WS-ZA ZA4.5: does the start's enqueue place the thread?  It does when the
thread is queued on no core and its run-queue links admit its home core
(`runEnqueueAdmits`); otherwise the enqueue declines and the start writes only
the flag.  `startFresh_of_startable` derives it for a startable thread from the
link agreement. -/
def startFresh (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  !runnableOnSomeCore st tid && st.runEnqueueAdmits (determineTargetCore st tid) tid

/-- The flag write keeps both halves of `startFresh`: it moves no queue and no
run-queue link. -/
theorem startFresh_ready {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hT : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    (runnableOnSomeCore ({ st with objects := (st.objects.insert tid.toObjId
        (.tcb { tcb with threadState := .Ready })) } : SystemState) tid ||
      !({ st with objects := (st.objects.insert tid.toObjId
        (.tcb { tcb with threadState := .Ready })) } : SystemState).runEnqueueAdmits
          (determineTargetCore st tid) tid) = !startFresh st tid := by
  have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
        some { tcb with threadState := .Ready } := by
    rw [SystemState.getTcb?_eq_some_iff]
    exact RHTable.getElem?_insert_self st.objects _ _ hInv
  have hA : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).runEnqueueAdmits
        (determineTargetCore st tid) tid = st.runEnqueueAdmits (determineTargetCore st tid) tid := by
    unfold SystemState.runEnqueueAdmits SystemState.runLinksAdmit; rw [hT1, hT]
  have hRn : runnableOnSomeCore ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState) tid =
        runnableOnSomeCore st tid := by
    simp only [runnableOnSomeCore, SystemState.queuedOn, hT1, hT]
  rw [hA, hRn]
  unfold startFresh
  cases runnableOnSomeCore st tid <;> cases st.runEnqueueAdmits (determineTargetCore st tid) tid <;> rfl

-- ============================================================================
-- §2  What the start writes
-- ============================================================================

/-- **WS-BP BP7.11** (the decomposition, object half): on a thread that
resolves and is queued nowhere, the start's object store is two writes at the
thread's key — the flag, then the enqueue's `.ready` — up to TCB run-queue
fields (WS-ZA ZA4.5: the enqueue also writes the run-queue links of the thread
and its queue neighbours).  Everything the other lemmas say of the objects is
read off this. -/
theorem startInitialThreadOnCore_objectsAgree {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : startFresh st tid = true)
    (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).objectsAgreeOffRunLinks
      { st with
        objects := (st.objects.insert tid.toObjId
            (.tcb { tcb with threadState := .Ready })).insert tid.toObjId
            (.tcb (startedThread tcb)) } := by
  unfold startInitialThreadOnCore
  rw [SystemState.updateTcb_eq_of_some hT]
  have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
        some { tcb with threadState := .Ready } := by
    rw [SystemState.getTcb?_eq_some_iff]
    exact RHTable.getElem?_insert_self st.objects _ _ hInv
  have hG := startFresh_ready hT hInv
  rw [hNR] at hG
  simp only [Bool.not_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hG
  exact enqueueRunnableOnCore_objectsAgree_marked _ _ tid _ hT1
    (wakeDeclines_eq_false_iff.mpr ⟨hG.1, hG.2⟩)

/-- **WS-BP BP7.11** (the decomposition, scheduler half): the home core's run
queue gains the thread at its boosted priority (ghost queue and concrete ends),
and the home core's reschedule-pending flag is raised. -/
theorem startInitialThreadOnCore_scheduler {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : startFresh st tid = true)
    (hInv : st.objects.invExt) :
    ∃ E : RunQueueEnds, (startInitialThreadOnCore st tid).scheduler =
      ((st.scheduler.setRunQueueEndsOnCore (determineTargetCore st tid) E).setRunQueueOnCore
        (determineTargetCore st tid)
        ((st.scheduler.runQueueOnCore (determineTargetCore st tid)).insert tid
          tcb.boostedPriority)).markReschedulePendingOnCore (determineTargetCore st tid) := by
  unfold startInitialThreadOnCore
  rw [SystemState.updateTcb_eq_of_some hT]
  have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
        some { tcb with threadState := .Ready } := by
    rw [SystemState.getTcb?_eq_some_iff]
    exact RHTable.getElem?_insert_self st.objects _ _ hInv
  have hG := startFresh_ready hT hInv
  rw [hNR] at hG
  simp only [Bool.not_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hG
  obtain ⟨E, hE⟩ := enqueueRunnableOnCore_scheduler_of_fresh _ _ tid _ hT1
    (wakeDeclines_eq_false_iff.mpr ⟨hG.1, hG.2⟩)
  exact ⟨E, hE⟩

/-- **WS-BP BP7.11** (field frame): the start writes the object store and the
scheduler, and no other field of the state. -/
theorem startInitialThreadOnCore_onlyObjectsSchedulerDiffer (st : SystemState)
    (tid : SeLe4n.ThreadId) : (startInitialThreadOnCore st tid).onlyObjectsSchedulerDiffer st := by
  unfold startInitialThreadOnCore
  refine (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ tid).trans ?_
  cases hT : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact .refl _
  | some tcb => rw [SystemState.updateTcb_eq_of_some hT]; rfl

/-- **WS-BP BP7.11**: on a thread that resolves to nothing the start is the
identity — both steps look the thread up and find nothing. -/
theorem startInitialThreadOnCore_eq_of_none {st : SystemState} {tid : SeLe4n.ThreadId}
    (hT : st.getTcb? tid = none) : startInitialThreadOnCore st tid = st := by
  unfold startInitialThreadOnCore
  rw [SystemState.updateTcb_eq_self_of_none hT]
  unfold enqueueRunnableOnCore
  rw [SystemState.getTcbWitnessed?_eq_none hT]

/-- **WS-BP BP7.11**: on a thread already queued (or whose links name another
core) the start writes the flag and nothing else — the enqueue declines it.
(`initialThreadStartable` refuses that case; stated so every witness below is
total.) -/
theorem startInitialThreadOnCore_eq_of_declined {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : startFresh st tid = false)
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
  have hG := startFresh_ready hT hInv
  rw [hNR, Bool.not_false] at hG
  dsimp only
  rw [if_pos (by unfold wakeDeclines; exact hG)]

/-- **WS-BP BP7.11**: the started thread's key holds `startedThread tcb`, off
its run-queue fields. -/
theorem startInitialThreadOnCore_objects_self {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : startFresh st tid = true)
    (hInv : st.objects.invExt) :
    ∃ t', (startInitialThreadOnCore st tid).objects[tid.toObjId]? = some (.tcb t') ∧
      t'.withoutRunLinks = (startedThread tcb).withoutRunLinks :=
  (startInitialThreadOnCore_objectsAgree hT hNR hInv).get_tcb
    (RHTable.getElem?_insert_self _ _ _ (RHTable_insert_preserves_invExt _ _ _ hInv))

/-- **WS-BP BP7.11** (frame): every other key is untouched off TCB run-queue
fields (the enqueue links the thread beside its queue neighbours). -/
theorem startInitialThreadOnCore_objects_ne {st : SystemState} {tid : SeLe4n.ThreadId}
    (k : SeLe4n.ObjId) (hNe : tid.toObjId ≠ k) (hInv : st.objects.invExt) :
    ((startInitialThreadOnCore st tid).objects[k]?).map KernelObject.withoutRunLinks =
      (st.objects[k]?).map KernelObject.withoutRunLinks := by
  have hNeB : ¬(tid.toObjId == k) = true := fun h => hNe (eq_of_beq h)
  cases hT : st.getTcb? tid with
  | none =>
    unfold startInitialThreadOnCore
    rw [SystemState.updateTcb_eq_self_of_none hT]
    unfold enqueueRunnableOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hT]
  | some tcb =>
    cases hNR : startFresh st tid with
    | true =>
      rw [startInitialThreadOnCore_objectsAgree hT hNR hInv k]
      show (((st.objects.insert _ _).insert _ _).get? k).map _ = (st.objects.get? k).map _
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeB (RHTable_insert_preserves_invExt _ _ _ hInv),
        RHTable.getElem?_insert_ne _ _ _ _ hNeB hInv]
    | false =>
      rw [startInitialThreadOnCore_eq_of_declined hT hNR hInv]
      show ((st.objects.insert _ _).get? k).map _ = (st.objects.get? k).map _
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeB hInv]

/-- **WS-BP BP7.11**: the start writes the run queue (ghost queues and concrete
ends) and the reschedule-pending flags (the KSC-1 accumulator the enqueue
raises), and no other scheduler field. -/
theorem startInitialThreadOnCore_scheduler_runQueueOnly (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    ∃ rq re rp, (startInitialThreadOnCore st tid).scheduler =
      { st.scheduler with runQueue := rq, runQueueEnds := re, reschedulePending := rp } := by
  unfold startInitialThreadOnCore
  rcases enqueueRunnableOnCore_scheduler_cases
      (st.updateTcb tid fun t => { t with threadState := .Ready })
      (determineTargetCore st tid) tid with h | ⟨E, p, h⟩ <;>
    rw [h, SystemState.updateTcb_scheduler] <;> exact ⟨_, _, _, rfl⟩

/-- **WS-BP BP7.11**: the start writes no current slot on any core — it does
not dispatch. -/
theorem startInitialThreadOnCore_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (startInitialThreadOnCore st tid).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
  obtain ⟨rq, re, rp, hrq⟩ := startInitialThreadOnCore_scheduler_runQueueOnly st tid
  rw [hrq]; rfl

/-- **WS-BP BP7.11**: the home core's run queue gains the thread at its
boosted priority. -/
theorem startInitialThreadOnCore_runQueueOnCore_self {st : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hT : st.getTcb? tid = some tcb)
    (hNR : startFresh st tid = true) (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).scheduler.runQueueOnCore (determineTargetCore st tid) =
      (st.scheduler.runQueueOnCore (determineTargetCore st tid)).insert tid
        tcb.boostedPriority := by
  obtain ⟨E, hE⟩ := startInitialThreadOnCore_scheduler hT hNR hInv
  rw [hE, SchedulerState.markReschedulePendingOnCore_runQueueOnCore]
  exact SchedulerState.setRunQueueOnCore_runQueueOnCore_self _ _ _

/-- **WS-BP BP7.11**: where the start writes nothing to the scheduler — the
thread resolves to nothing, or the enqueue declines it — every core's queue is
as before. -/
theorem startInitialThreadOnCore_runQueueOnCore_ne' (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : st.getTcb? tid = none ∨ startFresh st tid = false) (c : CoreId) :
    (startInitialThreadOnCore st tid).scheduler.runQueueOnCore c =
      st.scheduler.runQueueOnCore c := by
  rcases h with hT | hNR
  · rw [startInitialThreadOnCore_eq_of_none hT]
  · cases hT : st.getTcb? tid with
    | none => rw [startInitialThreadOnCore_eq_of_none hT]
    | some tcb => rw [startInitialThreadOnCore_eq_of_declined hT hNR hInv]

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
    cases hNR : startFresh st tid with
    | true =>
      obtain ⟨E, hE⟩ := startInitialThreadOnCore_scheduler hT hNR hInv
      rw [hE, SchedulerState.markReschedulePendingOnCore_runQueueOnCore,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc,
        SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]
    | false => rw [startInitialThreadOnCore_eq_of_declined hT hNR hInv]

-- ============================================================================
-- §3  The `IntermediateState` witnesses
-- ============================================================================

/-- **WS-BP BP7.11**: the start preserves `allTablesInvExtK`. -/
theorem startInitialThreadOnCore_preserves_allTablesInvExtK (st : SystemState)
    (tid : SeLe4n.ThreadId) (h : st.allTablesInvExtK) :
    (startInitialThreadOnCore st tid).allTablesInvExtK := by
  have hK1 : (st.updateTcb tid fun t => { t with threadState := .Ready }).objects.invExtK := by
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact h.1
    | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact RHTable.insert_preserves_invExtK _ _ _ h.1
  exact (startInitialThreadOnCore_onlyObjectsSchedulerDiffer st tid).allTablesInvExtK
    (enqueueRunnableOnCore_objects_invExtK _ _ tid hK1) h

/-- **WS-BP BP7.11**: **what the start can leave at a key** — the pre-state's
object, or, where the pre-state held a TCB, that TCB off its run-queue fields:
unchanged (a queue neighbour whose links the enqueue rewrites, WS-ZA ZA4.5), or
with its flag set `.Ready` and (on the branch that enqueues) its IPC state
`.ready`.  Every object-level
witness the boot needs is read off this. -/
theorem startInitialThreadOnCore_objects_cases (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObj : (startInitialThreadOnCore st tid).objects[k]? = some obj) :
    st.objects[k]? = some obj ∨
    ∃ t t', st.objects[k]? = some (.tcb t) ∧ obj = .tcb t' ∧
      (t'.withoutRunLinks = t.withoutRunLinks ∨
       t'.withoutRunLinks = ({ t with threadState := .Ready } : TCB).withoutRunLinks ∨
       t'.withoutRunLinks = (startedThread t).withoutRunLinks) := by
  by_cases hEq : tid.toObjId = k
  · subst hEq
    cases hT : st.getTcb? tid with
    | none =>
      left; rw [startInitialThreadOnCore_eq_of_none hT] at hObj; exact hObj
    | some tcb =>
      right
      have hT0 := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      cases hNR : startFresh st tid with
      | true =>
        obtain ⟨t', h', ht⟩ := startInitialThreadOnCore_objects_self hT hNR hInv
        rw [h'] at hObj; cases hObj
        exact ⟨tcb, t', hT0, rfl, Or.inr (Or.inr ht)⟩
      | false =>
        rw [startInitialThreadOnCore_eq_of_declined hT hNR hInv] at hObj
        change (st.objects.insert _ _).get? _ = _ at hObj
        rw [RHTable.getElem?_insert_self _ _ _ hInv] at hObj
        cases hObj; exact ⟨tcb, _, hT0, rfl, Or.inr (Or.inl rfl)⟩
  · obtain ⟨o₀, h₀, ho⟩ := KernelObject.map_withoutRunLinks_eq_some
      (startInitialThreadOnCore_objects_ne k hEq hInv) hObj
    rcases KernelObject.withoutRunLinks_eq_cases ho with rfl | ⟨t, t', rfl, rfl⟩
    · exact Or.inl h₀
    · exact Or.inr ⟨t, t', h₀, rfl, Or.inl (KernelObject.tcb.inj ho)⟩

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
  · obtain ⟨o', h', ho⟩ := KernelObject.map_withoutRunLinks_eq_some
      (startInitialThreadOnCore_objects_ne k hEq hInv).symm hObj
    rw [h', KernelObject.withoutRunLinks_eq_of_not_tcb ho.symm hNot]

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
    cases hNR : startFresh st tid with
    | true =>
      obtain ⟨t', h', _⟩ := startInitialThreadOnCore_objects_self hT hNR hInv
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h']; rfl
    | false =>
      have : (startInitialThreadOnCore st tid).getTcb? tid =
          some { tcb with threadState := .Ready } := by
        rw [SystemState.getTcb?_eq_some_iff, startInitialThreadOnCore_eq_of_declined hT hNR hInv]
        exact RHTable.getElem?_insert_self st.objects _ _ hInv
      rw [this]; rfl
  · obtain ⟨o', h', ho⟩ := KernelObject.map_withoutRunLinks_eq_some
      (startInitialThreadOnCore_objects_ne _ hEq hInv).symm hObj
    obtain ⟨t', rfl, _⟩ := KernelObject.withoutRunLinks_eq_tcb ho.symm
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h']; rfl

/-- **WS-BP BP7.11** (field frame): the start writes the object store and the
scheduler, and no other field of the state. -/
theorem startInitialThreadOnCore_frame (st : SystemState) (tid : SeLe4n.ThreadId) :
    startInitialThreadOnCore st tid =
      { st with objects := (startInitialThreadOnCore st tid).objects,
                scheduler := (startInitialThreadOnCore st tid).scheduler } :=
  startInitialThreadOnCore_onlyObjectsSchedulerDiffer st tid

/-- **WS-BP BP7.11**: the start preserves the object store's `invExt`. -/
theorem startInitialThreadOnCore_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).objects.invExt :=
  enqueueRunnableOnCore_preserves_objects_invExt _ _ tid
    (SystemState.updateTcb_preserves_objects_invExt st tid _ hInv)


/-- WS-ZA ZA4.5: the start keeps the run queues in agreement with the threads'
links: the state flag moves no link, and the enqueue keeps the agreement. -/
theorem startInitialThreadOnCore_runQueueRefined (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    (startInitialThreadOnCore st tid).runQueueRefined :=
  enqueueRunnableOnCore_runQueueRefined _ tid
    (SystemState.updateTcb_preserves_objects_invExt st tid _ hInv)
    (SystemState.updateTcb_runQueueRefined hInv (fun _ _ => rfl) hR)
/-- **WS-BP BP7.11**: the start preserves the per-object CNode-slot invariant —
it writes a TCB, and every CNode it holds is the pre-state's. -/
theorem startInitialThreadOnCore_preserves_perObjectSlotsInvariant (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (h : perObjectSlotsInvariant st) :
    perObjectSlotsInvariant (startInitialThreadOnCore st tid) := by
  intro oid cn hObj
  rcases startInitialThreadOnCore_objects_cases st tid hInv oid _ hObj with
    hB | ⟨_, _, _, hT, _⟩
  · exact h oid cn hB
  · cases hT

/-- **WS-BP BP7.11**: the start preserves the per-object VSpace-mapping
invariant, for the same reason. -/
theorem startInitialThreadOnCore_preserves_perObjectMappingsInvariant (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (h : perObjectMappingsInvariant st) :
    perObjectMappingsInvariant (startInitialThreadOnCore st tid) := by
  intro oid vs hObj
  rcases startInitialThreadOnCore_objects_cases st tid hInv oid _ hObj with
    hB | ⟨_, _, _, hT, _⟩
  · exact h oid vs hB
  · cases hT

/-- **WS-BP BP7.11**: the start preserves the lifecycle metadata's consistency
with the object store — the flag write is `updateTcb`'s own theorem, and the
enqueue writes no metadata and keeps every object's kind. -/
theorem startInitialThreadOnCore_preserves_objectTypeMetadataConsistent (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hC : SystemState.objectTypeMetadataConsistent st) :
    SystemState.objectTypeMetadataConsistent (startInitialThreadOnCore st tid) :=
  enqueueRunnableOnCore_preserves_objectTypeMetadataConsistent _ _ tid
    (SystemState.updateTcb_preserves_objects_invExt st tid _ hInv)
    (SystemState.updateTcb_preserves_objectTypeMetadataConsistent st tid
      (fun t => { t with threadState := .Ready }) hInv hC)

-- ============================================================================
-- §4  Placement, classification, and the run-queue facts the boot reads
-- ============================================================================

/-- A thread queued on no core: its links name none of them. -/
theorem queuedOn_false_of_runnableOnSomeCore_false {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : runnableOnSomeCore st tid = false) (c : CoreId) :
    st.queuedOn c tid = false := by
  unfold runnableOnSomeCore at h
  rw [List.any_eq_false] at h
  exact Bool.eq_false_iff.mpr (h c (mem_allCores c))

/-- ...so, under the link agreement, it is a member of no core's run queue. -/
theorem not_mem_runQueueOnCore_of_runnableOnSomeCore_false {st : SystemState}
    {tid : SeLe4n.ThreadId} (hR : st.runQueueRefined) (h : runnableOnSomeCore st tid = false)
    (c : CoreId) : tid ∉ st.scheduler.runQueueOnCore c := by
  intro hMem
  have hq := queuedOn_false_of_runnableOnSomeCore_false h c
  rw [(hR c).queuedOn, RunQueue.mem_iff_contains.mp hMem] at hq
  cases hq

/-- **WS-BP BP7.11** (placement frame): every other thread keeps its placement
— the start inserts one thread into one queue and writes no current slot. -/
theorem startInitialThreadOnCore_runnableOnSomeCore_ne (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (hNe : tid' ≠ tid) (hInv : st.objects.invExt) :
    runnableOnSomeCore (startInitialThreadOnCore st tid) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  congr 1; funext c
  unfold startInitialThreadOnCore
  rw [enqueueRunnableOnCore_queuedOn _ _ _
      (SystemState.updateTcb_preserves_objects_invExt st tid _ hInv),
    if_neg (fun h => hNe h.1)]
  exact SystemState.RunCoresAgree.queuedOn
    (SystemState.updateTcb_runCoreCode st tid (fun t => { t with threadState := .Ready })
      (fun _ => rfl) hInv) c tid'

/-- **WS-BP BP7.11**: the same, for the running test — no current slot moves. -/
theorem startInitialThreadOnCore_runningOnSomeCore (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) :
    runningOnSomeCore (startInitialThreadOnCore st tid) tid' = runningOnSomeCore st tid' := by
  unfold runningOnSomeCore
  congr 1; funext c
  rw [startInitialThreadOnCore_currentOnCore]

/-- **WS-BP BP7.11**: the started thread is queued — on its home core. -/
theorem startInitialThreadOnCore_queuedOn_self {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb) (hNR : startFresh st tid = true)
    (hInv : st.objects.invExt) :
    (startInitialThreadOnCore st tid).queuedOn (determineTargetCore st tid) tid = true := by
  unfold startInitialThreadOnCore
  rw [enqueueRunnableOnCore_queuedOn _ _ _
      (SystemState.updateTcb_preserves_objects_invExt st tid _ hInv),
    SystemState.updateTcb_eq_of_some hT]
  have hT1 : ({ st with objects := (st.objects.insert tid.toObjId
      (.tcb { tcb with threadState := .Ready })) } : SystemState).getTcb? tid =
        some { tcb with threadState := .Ready } := by
    rw [SystemState.getTcb?_eq_some_iff]
    exact RHTable.getElem?_insert_self st.objects _ _ hInv
  have hG := startFresh_ready hT hInv
  rw [hNR] at hG
  simp only [Bool.not_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hG
  rw [if_pos ⟨rfl, by rw [hT1]; rfl, wakeDeclines_eq_false_iff.mpr ⟨hG.1, hG.2⟩⟩]
  simp

/-- **WS-BP BP7.11**: ...so it is placed on some core. -/
theorem startInitialThreadOnCore_runnableOnSomeCore_self {st : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hT : st.getTcb? tid = some tcb)
    (hNR : startFresh st tid = true) (hInv : st.objects.invExt) :
    runnableOnSomeCore (startInitialThreadOnCore st tid) tid = true := by
  unfold runnableOnSomeCore
  rw [List.any_eq_true]
  exact ⟨_, mem_allCores _, startInitialThreadOnCore_queuedOn_self hT hNR hInv⟩

/-- WS-ZA ZA4.5: a startable thread is fresh under the link agreement — queued
nowhere, so its links name no core and its home core admits it. -/
theorem startFresh_of_startable {st : SystemState} {tid : SeLe4n.ThreadId}
    (hStart : initialThreadStartable st tid = true) (hR : st.runQueueRefined) :
    startFresh st tid = true := by
  obtain ⟨tcb, hT, _, _, _, hNR, _⟩ := initialThreadStartable_spec hStart
  have hA : st.runEnqueueAdmits (determineTargetCore st tid) tid = true :=
    SystemState.runEnqueueAdmits_of_refined hR (by rw [hT]; rfl) (fun c' _ =>
      RunQueue.contains_false_of_not_mem (not_mem_runQueueOnCore_of_runnableOnSomeCore_false hR hNR c'))
      (initialThreadStartable_not_idle hStart)
  unfold startFresh
  rw [hNR, hA]; rfl

/-- **WS-BP BP7.11**: **the start keeps the full thread-state classification.**
The started thread is stored `.Ready` and is queued on no current slot, which is
what `inferThreadState` calls `.Ready`; every other thread keeps its record and
its placement.  So the boot state's `threadStateConsistent` — and with it the
inactive-flag relation the live decisions read — survives every start. -/
theorem startInitialThreadOnCore_preserves_threadStateConsistent {st : SystemState}
    {tid : SeLe4n.ThreadId} (hStart : initialThreadStartable st tid = true)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (h : threadStateConsistent st) :
    threadStateConsistent (startInitialThreadOnCore st tid) := by
  obtain ⟨tcb, hT, _, _, _, -, hNRun⟩ := initialThreadStartable_spec hStart
  have hNR := startFresh_of_startable hStart hR
  intro oid t hObj
  by_cases hEq : tid.toObjId = oid
  · subst hEq
    obtain ⟨t', h', ht⟩ := startInitialThreadOnCore_objects_self hT hNR hInv
    rw [h'] at hObj
    have e : t' = t := by injection hObj with hObj; injection hObj
    subst e
    rw [show t'.threadState = ThreadState.Ready from TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState ht]
    show ThreadState.Ready = inferThreadState _ tid t'
    unfold inferThreadState threadRunningOnSomeCore threadQueuedOnSomeCore
    rw [startInitialThreadOnCore_runningOnSomeCore, hNRun,
      startInitialThreadOnCore_runnableOnSomeCore_self hT hNR hInv]
    rfl
  · obtain ⟨o₀, h₀, ho⟩ := KernelObject.map_withoutRunLinks_eq_some
      (startInitialThreadOnCore_objects_ne oid hEq hInv) hObj
    obtain ⟨t₀, rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb ho.symm
    rw [show t.threadState = t₀.threadState from (TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState ht).symm,
      h oid t₀ h₀]
    have hNe : (⟨oid.toNat⟩ : SeLe4n.ThreadId) ≠ tid := by
      intro hc; apply hEq; rw [← hc]; rfl
    unfold inferThreadState threadRunningOnSomeCore threadQueuedOnSomeCore
    rw [startInitialThreadOnCore_runningOnSomeCore,
      startInitialThreadOnCore_runnableOnSomeCore_ne st tid _ hNe hInv,
      show t.ipcState = t₀.ipcState from (TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState ht).symm]

/-- **WS-BP BP7.11**: what the boot's bundle theorem reads of a core's run
queue — its members are distinct, and each is a stored TCB with a positive time
slice and no inherited boost, bucketed at its own base priority. -/
def runQueueBootSound (st : SystemState) (c : CoreId) : Prop :=
  (st.scheduler.runQueueOnCore c).toList.Nodup ∧
  ∀ tid, tid ∈ st.scheduler.runQueueOnCore c →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ 0 < tcb.timeSlice ∧
      tcb.pipBoost = none ∧
      (st.scheduler.runQueueOnCore c).priorityOf tid = some tcb.priority

/-- **WS-BP BP7.11**: **the start keeps every core's run queue boot-sound.**
The started thread enters one queue at its boosted priority, which with no
boost is its base priority; every thread already queued is another thread,
whose record and bucket the start leaves alone. -/
theorem startInitialThreadOnCore_preserves_runQueueBootSound {st : SystemState}
    {tid : SeLe4n.ThreadId} (hStart : initialThreadStartable st tid = true)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (c : CoreId)
    (h : runQueueBootSound st c) :
    runQueueBootSound (startInitialThreadOnCore st tid) c := by
  obtain ⟨tcb, hT, _, hBoost, hSlice, hNR0, _⟩ := initialThreadStartable_spec hStart
  have hNR := startFresh_of_startable hStart hR
  obtain ⟨hNodup, hMem⟩ := h
  unfold runQueueBootSound
  have hNotMem := not_mem_runQueueOnCore_of_runnableOnSomeCore_false hR hNR0
  -- A thread already queued on `c` is not the started one, so its record is framed.
  have hOld : ∀ tid', tid' ∈ st.scheduler.runQueueOnCore c → ∀ t,
      st.objects[tid'.toObjId]? = some (.tcb t) → 0 < t.timeSlice → t.pipBoost = none →
      ∃ t', (startInitialThreadOnCore st tid).objects[tid'.toObjId]? = some (.tcb t') ∧
        0 < t'.timeSlice ∧ t'.pipBoost = none ∧ t'.priority = t.priority := by
    intro tid' hm t hObj hPos hB
    have hNe : tid.toObjId ≠ tid'.toObjId := by
      intro hk
      have : tid = tid' := ThreadId.toObjId_injective _ _ hk
      subst this; exact hNotMem c hm
    obtain ⟨o', h', ho⟩ := KernelObject.map_withoutRunLinks_eq_some
      (startInitialThreadOnCore_objects_ne _ hNe hInv).symm hObj
    obtain ⟨t', rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb ho.symm
    exact ⟨t', h', (TCB.proj_eq_of_withoutRunLinks_eq TCB.timeSlice ht).symm ▸ hPos,
      (TCB.proj_eq_of_withoutRunLinks_eq TCB.pipBoost ht).trans hB, TCB.proj_eq_of_withoutRunLinks_eq TCB.priority ht⟩
  by_cases hc : determineTargetCore st tid = c
  · subst hc
    rw [startInitialThreadOnCore_runQueueOnCore_self hT hNR hInv]
    refine ⟨RunQueue.insert_preserves_toList_nodup _ _ _ hNodup, ?_⟩
    intro tid' hm
    have hContains : (st.scheduler.runQueueOnCore (determineTargetCore st tid)).contains tid =
        false := RunQueue.contains_false_of_not_mem (hNotMem _)
    rcases (RunQueue.mem_insert _ _ _ _).mp hm with hm | hEqT
    · obtain ⟨t, hObj, hPos, hB, hPrio⟩ := hMem tid' hm
      obtain ⟨t', h', hPos', hB', hP'⟩ := hOld tid' hm t hObj hPos hB
      refine ⟨t', h', hPos', hB', ?_⟩
      have hNe : tid' ≠ tid := by
        intro e; subst e; exact hNotMem _ hm
      rw [RunQueue.priorityOf_insert, hContains, hP']
      simp only [Bool.false_eq_true, ↓reduceIte, hNe]
      exact hPrio
    · rw [hEqT]
      obtain ⟨t', h', ht⟩ := startInitialThreadOnCore_objects_self hT hNR hInv
      refine ⟨t', h', (TCB.proj_eq_of_withoutRunLinks_eq TCB.timeSlice ht).symm ▸ hSlice,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.pipBoost ht).trans hBoost, ?_⟩
      rw [(TCB.proj_eq_of_withoutRunLinks_eq TCB.priority ht :
        t'.priority = (startedThread tcb).priority)]
      rw [RunQueue.priorityOf_insert, hContains]
      simp only [Bool.false_eq_true, ↓reduceIte]
      show some (tcb.priority.raisedBy tcb.pipBoost) = some tcb.priority
      rw [hBoost]; rfl
  · rw [startInitialThreadOnCore_runQueueOnCore_ne st tid c hc hInv]
    refine ⟨hNodup, ?_⟩
    intro tid' hm
    obtain ⟨t, hObj, hPos, hB, hPrio⟩ := hMem tid' hm
    obtain ⟨t', h', hPos', hB', hP'⟩ := hOld tid' hm t hObj hPos hB
    exact ⟨t', h', hPos', hB', hP' ▸ hPrio⟩

/-- **WS-BP BP7.11**: what it means for a thread to have been started — it is
queued on some core and stored `.Ready`. -/
def threadStarted (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  runnableOnSomeCore st tid = true ∧ ∃ t, st.getTcb? tid = some t ∧ t.threadState = .Ready

/-- **WS-BP BP7.11**: the start starts its thread. -/
theorem startInitialThreadOnCore_threadStarted {st : SystemState} {tid : SeLe4n.ThreadId}
    (hStart : initialThreadStartable st tid = true) (hInv : st.objects.invExt)
    (hR : st.runQueueRefined) :
    threadStarted (startInitialThreadOnCore st tid) tid := by
  obtain ⟨tcb, hT, _, _, _, -, _⟩ := initialThreadStartable_spec hStart
  have hNR := startFresh_of_startable hStart hR
  obtain ⟨t', h', ht⟩ := startInitialThreadOnCore_objects_self hT hNR hInv
  exact ⟨startInitialThreadOnCore_runnableOnSomeCore_self hT hNR hInv, t',
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr h', TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState ht⟩

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
  have hNeO : tid.toObjId ≠ tid'.toObjId := fun hk => hNe (ThreadId.toObjId_injective _ _ hk).symm
  obtain ⟨o', h', ho⟩ := KernelObject.map_withoutRunLinks_eq_some
    (startInitialThreadOnCore_objects_ne _ hNeO hInv).symm
    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
  obtain ⟨t', rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb ho.symm
  exact ⟨by rw [startInitialThreadOnCore_runnableOnSomeCore_ne st tid tid' hNe hInv]; exact hRun,
    t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h', (TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState ht).trans hReady⟩

/-- **WS-BP BP7.11**: a thread startable before a start of **another** thread is
startable after it — the start writes only its own thread's record, inserts
only its own thread into a queue, and sets no current slot. -/
theorem initialThreadStartable_of_start_ne {st : SystemState} {tid tid' : SeLe4n.ThreadId}
    (hNe : tid' ≠ tid) (hInv : st.objects.invExt)
    (h : initialThreadStartable st tid' = true) :
    initialThreadStartable (startInitialThreadOnCore st tid) tid' = true := by
  have hNeO : tid.toObjId ≠ tid'.toObjId := fun hk => hNe (ThreadId.toObjId_injective _ _ hk).symm
  unfold initialThreadStartable at h ⊢
  obtain ⟨hIdle, h⟩ := (Bool.and_eq_true _ _).mp h
  rw [hIdle, Bool.true_and]
  rw [startInitialThreadOnCore_runnableOnSomeCore_ne st tid tid' hNe hInv,
    startInitialThreadOnCore_runningOnSomeCore]
  cases hT0 : st.getTcb? tid' with
  | none => rw [hT0] at h; cases h
  | some t =>
    rw [hT0] at h
    obtain ⟨o', h', ho⟩ := KernelObject.map_withoutRunLinks_eq_some
      (startInitialThreadOnCore_objects_ne _ hNeO hInv).symm
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT0)
    obtain ⟨t', rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb ho.symm
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h']
    have e1 : t'.threadState = t.threadState := TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState ht
    have e2 : t'.pipBoost = t.pipBoost := TCB.proj_eq_of_withoutRunLinks_eq TCB.pipBoost ht
    have e3 : t'.timeSlice = t.timeSlice := TCB.proj_eq_of_withoutRunLinks_eq TCB.timeSlice ht
    simp only [e1, e2, e3]
    exact h

end SeLe4n.Kernel
