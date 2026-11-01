-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Model.TableReferences
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAt
import SeLe4n.Kernel.Scheduler.IdleThread
import SeLe4n.Kernel.SchedContext.ReleaseLinks
import SeLe4n.Kernel.SchedContext.RefillState
import SeLe4n.Kernel.SchedContext.YieldLinkInvariant

/-!
# The run queue's links in the threads (WS-ZA ZA4.5)

As in seL4, a queued thread's run-queue links live in its TCB
(`TCB.runPrevCode`, `TCB.runNextCode`, the bucket pair, `TCB.runPrio`) beside
the core whose queue it is on (`TCB.runCoreCode`), and each core keeps only the
ends (`SchedulerState.runQueueEnds`).  The scheduler also carries each core's
queue as a whole (`SchedulerState.runQueueOnCore`), the value every scheduler
statement reads; `runQueueRefined` is the invariant that the two agree.

Reading a core's queue through the threads (`runLinkOn`) gives, for each
thread, the entry the queue holds for it while it is queued and the empty
entry otherwise (`RunQueue.queuedLink`).  Under the agreement every read the
kernel makes through the threads — membership, a thread's priority, the walk
from the head, a bucket's walk, the highest priority — equals the queue's.
-/

namespace SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The run-queue entry a TCB holds, read as a queued entry. -/
def TCB.runLink (tcb : TCB) : RunQueueLink :=
  { prio := tcb.runPrio, queued := true, prev := tcb.runPrevCode, next := tcb.runNextCode,
    bucketPrev := tcb.runBucketPrevCode, bucketNext := tcb.runBucketNextCode }

/-- A TCB's entry in core `c`'s queue: its links when it is queued there, the
empty entry otherwise. -/
def TCB.runLinkOn (tcb : TCB) (c : CoreId) : RunQueueLink :=
  if tcb.runCoreCode = c.val + 1 then TCB.runLink tcb else RunQueue.RunQueueLink.none

/-- A TCB's successor in core `c`'s queue (in its bucket when `bucket` holds),
read as one field: `(tcb.runLinkOn c).next` / `.bucketNext` with no link
record built (`TCB.runNextOn_eq`). -/
@[inline] def TCB.runNextOn (tcb : TCB) (c : CoreId) (bucket : Bool) : Nat :=
  if tcb.runCoreCode = c.val + 1 then
    (if bucket then tcb.runBucketNextCode else tcb.runNextCode)
  else 0

theorem TCB.runNextOn_eq (tcb : TCB) (c : CoreId) (bucket : Bool) :
    tcb.runNextOn c bucket =
      if bucket then (tcb.runLinkOn c).bucketNext else (tcb.runLinkOn c).next := by
  unfold TCB.runNextOn TCB.runLinkOn TCB.runLink
  split <;> cases bucket <;> rfl

/-- A queued entry with its successor replaced; any other entry kept. -/
def RunQueueLink.withNextIfQueued (v : Nat) (l : RunQueueLink) : RunQueueLink :=
  if l.queued then { l with next := v } else l
/-- A queued entry with its bucket successor replaced; any other entry kept. -/
def RunQueueLink.withBucketNextIfQueued (v : Nat) (l : RunQueueLink) : RunQueueLink :=
  if l.queued then { l with bucketNext := v } else l
/-- A queued entry with its predecessor replaced; any other entry kept. -/
def RunQueueLink.withPrevIfQueued (v : Nat) (l : RunQueueLink) : RunQueueLink :=
  if l.queued then { l with prev := v } else l
/-- A queued entry with its bucket predecessor replaced; any other entry kept. -/
def RunQueueLink.withBucketPrevIfQueued (v : Nat) (l : RunQueueLink) : RunQueueLink :=
  if l.queued then { l with bucketPrev := v } else l

theorem TCB.runLinkOn_setNext (tcb : TCB) (v : Nat) (c : CoreId) :
    ({ tcb with runNextCode := v } : TCB).runLinkOn c =
      RunQueueLink.withNextIfQueued v (tcb.runLinkOn c) := by
  unfold TCB.runLinkOn RunQueueLink.withNextIfQueued
  by_cases h : tcb.runCoreCode = c.val + 1 <;> simp [h, TCB.runLink, RunQueue.RunQueueLink.none]
theorem TCB.runLinkOn_setBucketNext (tcb : TCB) (v : Nat) (c : CoreId) :
    ({ tcb with runBucketNextCode := v } : TCB).runLinkOn c =
      RunQueueLink.withBucketNextIfQueued v (tcb.runLinkOn c) := by
  unfold TCB.runLinkOn RunQueueLink.withBucketNextIfQueued
  by_cases h : tcb.runCoreCode = c.val + 1 <;> simp [h, TCB.runLink, RunQueue.RunQueueLink.none]
theorem TCB.runLinkOn_setPrev (tcb : TCB) (v : Nat) (c : CoreId) :
    ({ tcb with runPrevCode := v } : TCB).runLinkOn c =
      RunQueueLink.withPrevIfQueued v (tcb.runLinkOn c) := by
  unfold TCB.runLinkOn RunQueueLink.withPrevIfQueued
  by_cases h : tcb.runCoreCode = c.val + 1 <;> simp [h, TCB.runLink, RunQueue.RunQueueLink.none]
theorem TCB.runLinkOn_setBucketPrev (tcb : TCB) (v : Nat) (c : CoreId) :
    ({ tcb with runBucketPrevCode := v } : TCB).runLinkOn c =
      RunQueueLink.withBucketPrevIfQueued v (tcb.runLinkOn c) := by
  unfold TCB.runLinkOn RunQueueLink.withBucketPrevIfQueued
  by_cases h : tcb.runCoreCode = c.val + 1 <;> simp [h, TCB.runLink, RunQueue.RunQueueLink.none]

/-- A TCB taken out of its run queue: marked on no core, with its four
neighbour links cleared too, so a dequeued thread keeps no stale neighbour
code, though every reader masks the four by the core code (`TCB.runLinkOn`). -/
@[inline] def TCB.detachRun (tcb : TCB) : TCB :=
  { tcb with runCoreCode := 0, runPrevCode := 0, runNextCode := 0,
             runBucketPrevCode := 0, runBucketNextCode := 0 }

theorem TCB.runLinkOn_detachRun (tcb : TCB) (c : CoreId) :
    tcb.detachRun.runLinkOn c = RunQueue.RunQueueLink.none := by
  unfold TCB.runLinkOn TCB.detachRun; rw [if_neg (fun h => by simp at h)]

theorem TCB.runLinkOn_eq_none_of_not_queued {tcb : TCB} {c : CoreId}
    (h : (tcb.runLinkOn c).queued = false) : tcb.runLinkOn c = RunQueue.RunQueueLink.none := by
  unfold TCB.runLinkOn at h ⊢
  split
  · next hc => rw [if_pos hc] at h; cases h
  · rfl

@[simp] theorem RunQueueLink.withNextIfQueued_none (v : Nat) :
    RunQueueLink.withNextIfQueued v RunQueue.RunQueueLink.none = RunQueue.RunQueueLink.none := rfl
@[simp] theorem RunQueueLink.withBucketNextIfQueued_none (v : Nat) :
    RunQueueLink.withBucketNextIfQueued v RunQueue.RunQueueLink.none = RunQueue.RunQueueLink.none := rfl
@[simp] theorem RunQueueLink.withPrevIfQueued_none (v : Nat) :
    RunQueueLink.withPrevIfQueued v RunQueue.RunQueueLink.none = RunQueue.RunQueueLink.none := rfl
@[simp] theorem RunQueueLink.withBucketPrevIfQueued_none (v : Nat) :
    RunQueueLink.withBucketPrevIfQueued v RunQueue.RunQueueLink.none = RunQueue.RunQueueLink.none := rfl

/-- A thread a core may run: ready in IPC and not suspended — seL4's
`runnable` thread states. -/
def TCB.Runnable (t : TCB) : Prop := t.ipcState = .ready ∧ t.threadState ≠ .Inactive

/-- The executable test reads the property. -/
theorem TCB.runnable_of_isRunnable {t : TCB} (h : t.isRunnable = true) : t.Runnable := by
  unfold TCB.isRunnable at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨by simpa using h.1, h.2⟩

/-- A thread's two state fields agree: a thread blocked in IPC is not
suspended.  seL4 keeps one thread state, so the two can never disagree there;
here the suspend clears the IPC state before it marks the thread inactive. -/
def TCB.Coherent (t : TCB) : Prop := t.ipcState = .ready ∨ t.threadState ≠ .Inactive

/-- A thread not suspended. -/
def TCB.Active (t : TCB) : Prop := t.threadState ≠ .Inactive

/-- One TCB replaced by another **monotonely**: a ready thread stays ready and
an active one active, so a runnable thread stays runnable and a coherent one
coherent — and its affinity, so its home core, is kept.  Every write that
leaves both state fields and the affinity alone is one; so is every write that
makes a thread ready.  The affinity write (`setThreadCpuAffinity`) is the one
TCB write that is not: it moves the thread's home, and the operation around it
moves the thread with it. -/
def TCB.StepMono (x x' : TCB) : Prop :=
  (x.ipcState = .ready → x'.ipcState = .ready) ∧ (x.Active → x'.Active) ∧
    x'.cpuAffinity = x.cpuAffinity

theorem TCB.StepMono.runnable {x x' : TCB} (h : x.StepMono x') (hr : x.Runnable) :
    x'.Runnable :=
  ⟨h.1 hr.1, h.2.1 hr.2⟩

theorem TCB.StepMono.coherent {x x' : TCB} (h : x.StepMono x') (hc : x.Coherent) :
    x'.Coherent :=
  hc.imp h.1 h.2.1

/-- A TCB write that is a monotone step on every TCB. -/
abbrev TCB.StateMono (f : TCB → TCB) : Prop := ∀ x : TCB, TCB.StepMono x (f x)

/-- A scheduling point open on one core: the window between the step that
takes core `c`'s current thread out of the steady state and the dispatch that
replaces it (seL4's scheduler action other than `resume_cur_thread`). -/
inductive SchedPoint where
  /-- A preemption: `c`'s current thread, still runnable, may be back on `c`'s
  queue. -/
  | preempt (c : CoreId)
  /-- A block: `c`'s current thread is no longer runnable and holds `c`'s slot
  until the dispatch. -/
  | block (c : CoreId)
  deriving DecidableEq

/-- The core a scheduling point is open on. -/
def SchedPoint.core : SchedPoint → CoreId
  | .preempt c => c
  | .block c => c

end SeLe4n.Model

namespace SeLe4n.Model.SystemState
open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.LinkedQueue
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA4.5: thread `t`'s entry in core `c`'s run queue, read from its TCB:
its links when it is queued on `c`, the empty entry when it is queued on
another core, on none, or is no thread. -/
def runLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : RunQueueLink :=
  match st.getTcb? t with
  | some tcb => tcb.runLinkOn c
  | none => RunQueue.RunQueueLink.none

theorem runLinkOn_of_getTcb? {st st' : SystemState} {t : SeLe4n.ThreadId}
    (h : st'.getTcb? t = st.getTcb? t) (c : CoreId) : st'.runLinkOn c t = st.runLinkOn c t := by
  unfold runLinkOn; rw [h]

theorem runLinkOn_of_objects {st st' : SystemState} (h : st'.objects = st.objects)
    (c : CoreId) (t : SeLe4n.ThreadId) : st'.runLinkOn c t = st.runLinkOn c t :=
  runLinkOn_of_getTcb? (getTcb?_frame h t) c

/-- The object with a TCB rewritten through `g`; every other kind as is. -/
@[inline] def _root_.SeLe4n.Model.KernelObject.mapTcb (g : TCB → TCB) : KernelObject → KernelObject
  | .tcb x => .tcb (g x)
  | o => o

/-- WS-ZA ZA4.5: rewrite thread `t`'s TCB through `g` **in its slot**
(`RHTable.mapValueAt`): no probe, no resize, no key moved, so the frame holds
on every object table (`objects_mapTcbInPlace`).  The run queue's link writes
go through it; a key holding no TCB is left as it is. -/
@[inline] def mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) : SystemState :=
  { st with objects := st.objects.mapValueAt t.toObjId (KernelObject.mapTcb g) }

theorem objects_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (x : SeLe4n.ObjId) :
    (st.mapTcbInPlace t g).objects[x]? =
      if t.toObjId == x then (st.objects[x]?).map (KernelObject.mapTcb g) else st.objects[x]? := by
  simp only [mapTcbInPlace, RHTable_getElem?_eq_get?]
  exact RHTable.get?_mapValueAt _ _ _ _

theorem mapTcbInPlace_getTcb?_self (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) :
    (st.mapTcbInPlace t g).getTcb? t = (st.getTcb? t).map g := by
  unfold getTcb?
  rw [objects_mapTcbInPlace, if_pos (beq_self_eq_true _)]
  cases st.objects[t.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem mapTcbInPlace_getTcb?_ne (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (y : SeLe4n.ThreadId) (hNe : t.toObjId ≠ y.toObjId) :
    (st.mapTcbInPlace t g).getTcb? y = st.getTcb? y := by
  unfold getTcb?
  rw [objects_mapTcbInPlace, if_neg (by simpa using hNe)]

@[simp] theorem mapTcbInPlace_scheduler (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) :
    (st.mapTcbInPlace t g).scheduler = st.scheduler := rfl

/-- **The in-place thread write primitive keeps the table references**: a
thread's only back-link is its taint words, which the write keeps, and the
tables are untouched. -/
theorem TableReferenceFrame.mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (hW : ∀ x, (g x).taintWords = x.taintWords := by taint_words_kept) :
    TableReferenceFrame st (st.mapTcbInPlace t g) :=
  ⟨rfl, fun x => by
    rw [objects_mapTcbInPlace]
    split
    · cases st.objects[x]? with
      | none => rfl
      | some o =>
        cases o <;> try rfl
        simp only [Option.map_some, objTableBackLinks_some, KernelObject.mapTcb,
          KernelObject.tableBackLinks, hW]
    · rfl⟩

/-- **The in-place thread write primitive holds the release queues**: it writes
a thread, which holds no release link, and no scheduler slot. -/
theorem releaseStateAgree.mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) : releaseStateAgree (st.mapTcbInPlace t g) st :=
  ⟨.of_objReleaseLinkOn fun x _ => by
    rw [objects_mapTcbInPlace]
    split
    · cases st.objects[x]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl, rfl⟩

/-- **The in-place thread write primitive keeps every slot's yield codes** when
its update keeps the thread's yield-to code (WS-ZA ZA6.6). -/
theorem _root_.SeLe4n.Kernel.YieldLinksKept.mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (hg : ∀ x, (g x).yieldToCode = x.yieldToCode) :
    YieldLinksKept (st.mapTcbInPlace t g) st := fun x => by
  rw [objects_mapTcbInPlace]
  split
  · cases st.objects[x]? with
    | none => rfl
    | some o => cases o <;> simp [KernelObject.mapTcb, objYieldCodes, hg]
  · rfl

/-- **The in-place thread write primitive keeps every context's refill view**:
it writes a thread, which holds none. -/
theorem _root_.SeLe4n.Kernel.RefillViewsKept.mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) : RefillViewsKept (st.mapTcbInPlace t g) st :=
  .of_eq fun x => by
    rw [objects_mapTcbInPlace]
    split
    · cases st.objects[x]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl

theorem mapTcbInPlace_objects_invExt (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hInv : st.objects.invExt) : (st.mapTcbInPlace t g).objects.invExt :=
  RHTable.mapValueAt_invExt _ _ _ hInv

theorem mapTcbInPlace_getTcb?_isSome (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (y : SeLe4n.ThreadId) :
    ((st.mapTcbInPlace t g).getTcb? y).isSome = (st.getTcb? y).isSome := by
  by_cases hy : y = t
  · subst hy; rw [mapTcbInPlace_getTcb?_self]; cases st.getTcb? y <;> rfl
  · rw [mapTcbInPlace_getTcb?_ne _ _ _ _ (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)]

/-- Rewriting a thread's TCB rewrites its entry and no other thread's. -/
theorem runLinkOn_mapTcbInPlace_self (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (c : CoreId) :
    (st.mapTcbInPlace t f).runLinkOn c t =
      match st.getTcb? t with
      | some tcb => (f tcb).runLinkOn c
      | none => RunQueue.RunQueueLink.none := by
  unfold runLinkOn
  rw [mapTcbInPlace_getTcb?_self st t f]
  cases st.getTcb? t <;> rfl

theorem runLinkOn_mapTcbInPlace_ne (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (c : CoreId) {y : SeLe4n.ThreadId} (hy : y ≠ t) :
    (st.mapTcbInPlace t f).runLinkOn c y = st.runLinkOn c y :=
  runLinkOn_of_getTcb? (mapTcbInPlace_getTcb?_ne st t f y
    (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)) c

/-- WS-ZA ZA4.5: core `c`'s run queue and the threads agree — the core's ends
are the queue's, and each thread's entry read from its TCB is the queue's entry
for it while it is queued and the empty entry otherwise. -/
def runQueueRefinedOnCore (st : SystemState) (c : CoreId) : Prop :=
  st.scheduler.runQueueEndsOnCore c = (st.scheduler.runQueueOnCore c).ends ∧
  ∀ t, st.runLinkOn c t = (st.scheduler.runQueueOnCore c).queuedLink t

/-- WS-ZA ZA4.5: every core's run queue agrees with the threads. -/
def runQueueRefined (st : SystemState) : Prop := ∀ c, st.runQueueRefinedOnCore c

/-- A transition that leaves every thread's entry, every queue and every queue's
ends as they were keeps the agreement. -/
theorem runQueueRefined_of_frame {st st' : SystemState}
    (hL : ∀ c t, st'.runLinkOn c t = st.runLinkOn c t)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : st.runQueueRefined) : st'.runQueueRefined := by
  intro c
  have hc := h c
  unfold runQueueRefinedOnCore SchedulerState.runQueueEndsOnCore SchedulerState.runQueueOnCore
    at hc ⊢
  rw [hQ, hE]
  exact ⟨hc.1, fun t => (hL c t).trans (hc.2 t)⟩

/-- ...in particular one that writes neither the objects nor the scheduler. -/
theorem runQueueRefined_of_objects_scheduler_eq {st st' : SystemState}
    (hO : st'.objects = st.objects) (hS : st'.scheduler = st.scheduler)
    (h : st.runQueueRefined) : st'.runQueueRefined :=
  runQueueRefined_of_frame (fun c t => runLinkOn_of_objects hO c t)
    (congrArg SchedulerState.runQueue hS) (congrArg SchedulerState.runQueueEnds hS) h


theorem runLinkOn_queued_iff (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runLinkOn c t).queued = true ↔
      ∃ tcb, st.getTcb? t = some tcb ∧ tcb.runCoreCode = c.val + 1 := by
  unfold runLinkOn
  cases h : st.getTcb? t with
  | none => simp [RunQueue.RunQueueLink.none]
  | some tcb =>
    by_cases hc : tcb.runCoreCode = c.val + 1
    · simp [hc, TCB.runLinkOn, TCB.runLink]
    · simp [hc, TCB.runLinkOn, RunQueue.RunQueueLink.none]

/-- WS-ZA ZA4.5: is thread `t` queued on core `c`?  Read from its TCB alone —
the core its run-queue links name — with no queue consulted, which is what the
compiled kernel runs for every run-queue membership test (`queuedOn_eq`). -/
def queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? t with
  | some tcb => tcb.runCoreCode == c.val + 1
  | none => false

theorem queuedOn_eq_runLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    st.queuedOn c t = (st.runLinkOn c t).queued := by
  unfold queuedOn
  apply Bool.eq_iff_iff.mpr
  rw [runLinkOn_queued_iff]
  cases h : st.getTcb? t with
  | none => simp
  | some tcb => simp

/-- WS-ZA ZA4.5: the priority thread `t` is queued at on core `c`, read from
its TCB; `none` when it is not queued there.  Under the link agreement it is the
queue's `priorityOf` (`runQueueRefinedOnCore.queuedPriorityOn`). -/
def queuedPriorityOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    Option SeLe4n.Priority :=
  if (st.runLinkOn c t).queued then some (st.runLinkOn c t).prio else none

theorem queuedOn_of_getTcb? {st st' : SystemState} {t : SeLe4n.ThreadId}
    (h : st'.getTcb? t = st.getTcb? t) (c : CoreId) : st'.queuedOn c t = st.queuedOn c t := by
  unfold queuedOn; rw [h]

/-- WS-ZA ZA4.5: two states whose threads name the same run-queue core — the
TCB field `queuedOn` reads, compared thread by thread (a thread that is no TCB
in one is none in the other).  What a step that moves no thread on or off a run
queue keeps, whatever else it writes. -/
def RunCoresAgree (st' st : SystemState) : Prop :=
  ∀ y : SeLe4n.ThreadId, (st'.getTcb? y).map TCB.runCoreCode = (st.getTcb? y).map TCB.runCoreCode

namespace RunCoresAgree

theorem refl (st : SystemState) : RunCoresAgree st st := fun _ => rfl

theorem symm {st st' : SystemState} (h : RunCoresAgree st' st) : RunCoresAgree st st' :=
  fun y => (h y).symm

theorem trans {s1 s2 s3 : SystemState} (h₂ : RunCoresAgree s3 s2) (h₁ : RunCoresAgree s2 s1) :
    RunCoresAgree s3 s1 := fun y => (h₂ y).trans (h₁ y)

theorem of_objects {st st' : SystemState} (h : st'.objects = st.objects) : RunCoresAgree st' st :=
  fun y => by unfold getTcb?; rw [h]

theorem queuedOn {st st' : SystemState} (h : RunCoresAgree st' st) (c : CoreId)
    (t : SeLe4n.ThreadId) : st'.queuedOn c t = st.queuedOn c t := by
  have ht := h t
  unfold SystemState.queuedOn
  cases h1 : st'.getTcb? t <;> cases h2 : st.getTcb? t <;> rw [h1, h2] at ht <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at ht <;>
    simp only [ht]

/-- A TCB update that keeps the run-queue core keeps every thread's core. -/
theorem updateTcb {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ t, (f t).runCoreCode = t.runCoreCode) :
    RunCoresAgree (st.updateTcb tid f) st := by
  intro y
  by_cases h : tid.toObjId = y.toObjId
  · cases ThreadId.toObjId_injective tid y h
    rw [updateTcb_getTcb?_self st tid f hInv]
    cases st.getTcb? tid <;> simp [hf]
  · rw [updateTcb_getTcb?_ne st tid f hInv y h]

/-- An in-place rewrite of a TCB that keeps its run-queue core keeps every
thread's core. -/
theorem rewriteObject_tcb {st : SystemState} {tid : SeLe4n.ThreadId} {tcb tcb' : TCB}
    (hT : st.getTcb? tid = some tcb) (h : st.rewriteAdmissible tid.toObjId (.tcb tcb'))
    (hInv : st.objects.invExt) (hc : tcb'.runCoreCode = tcb.runCoreCode) :
    RunCoresAgree (st.rewriteObject tid.toObjId (.tcb tcb') h) st := by
  intro y
  by_cases hy : tid.toObjId = y.toObjId
  · cases ThreadId.toObjId_injective tid y hy
    rw [hT, (getTcb?_eq_some_iff _ tid tcb').mpr (rewriteObject_objects_self st _ _ h hInv)]
    simp [hc]
  · rw [rewriteObject_getTcb?_ne st _ _ h hInv y hy]

/-- An in-place rewrite of a slot that holds no TCB, with no TCB, keeps every
thread's core. -/
theorem rewriteObject_not_tcb {st : SystemState} {id : SeLe4n.ObjId} {new : KernelObject}
    (h : st.rewriteAdmissible id new) (hInv : st.objects.invExt)
    (hOld : ∀ t, st.objects[id]? ≠ some (.tcb t)) (hNew : ∀ t, new ≠ .tcb t) :
    RunCoresAgree (st.rewriteObject id new h) st := by
  intro y
  by_cases hy : id = y.toObjId
  · subst hy
    unfold getTcb?
    rw [rewriteObject_objects_self st _ _ h hInv]
    cases hO : st.objects[y.toObjId]? with
    | none => cases new <;> simp_all
    | some o => cases o <;> cases new <;> simp_all
  · rw [rewriteObject_getTcb?_ne st _ _ h hInv y hy]

end RunCoresAgree

/-- A thread is on at most one core's queue: its TCB names one core. -/
theorem runLinkOn_queued_unique {st : SystemState} {c c' : CoreId} {t : SeLe4n.ThreadId}
    (h : (st.runLinkOn c t).queued = true) (h' : (st.runLinkOn c' t).queued = true) : c = c' := by
  obtain ⟨tcb, ht, hc⟩ := (runLinkOn_queued_iff st c t).mp h
  obtain ⟨tcb', ht', hc'⟩ := (runLinkOn_queued_iff st c' t).mp h'
  rw [ht] at ht'; cases ht'
  exact Fin.ext (by omega)

/-- A rewrite of a TCB that acts on its entry in core `c`'s queue through `G`
rewrites the entry `runLinkOn` reads through `G`, at that thread only.  `G`
keeps the empty entry, so a thread that is no TCB keeps reading empty. -/
theorem runLinkOn_mapTcbInPlace_map (st : SystemState) (y : SeLe4n.ThreadId) (g : TCB → TCB)
    (c : CoreId) (G : RunQueueLink → RunQueueLink)
    (hg : ∀ tcb, (g tcb).runLinkOn c = G (tcb.runLinkOn c))
    (hG : G RunQueue.RunQueueLink.none = RunQueue.RunQueueLink.none) (x : SeLe4n.ThreadId) :
    (st.mapTcbInPlace y g).runLinkOn c x = if x = y then G (st.runLinkOn c x) else st.runLinkOn c x := by
  by_cases hx : x = y
  · subst hx
    rw [if_pos rfl, runLinkOn_mapTcbInPlace_self st x g c]
    unfold runLinkOn
    cases st.getTcb? x with
    | none => exact hG.symm
    | some tcb => exact hg tcb
  · rw [if_neg hx, runLinkOn_mapTcbInPlace_ne st y g c hx]

/-- Rewrite the TCB a link code names (`LinkedQueue.decode`); nothing for the
code `0`, which names no thread. -/
@[inline] def updateTcbAtCode (st : SystemState) (k : Nat) (g : TCB → TCB) : SystemState :=
  if k = 0 then st else st.mapTcbInPlace (decode k) g

theorem updateTcbAtCode_objects_invExt (st : SystemState) (k : Nat) (g : TCB → TCB)
    (hInv : st.objects.invExt) : (st.updateTcbAtCode k g).objects.invExt := by
  unfold updateTcbAtCode; split
  · exact hInv
  · exact mapTcbInPlace_objects_invExt _ _ _ hInv

theorem TableReferenceFrame.updateTcbAtCode (st : SystemState) (k : Nat) (g : TCB → TCB)
    (hW : ∀ x, (g x).taintWords = x.taintWords := by taint_words_kept) :
    TableReferenceFrame st (st.updateTcbAtCode k g) := by
  unfold SystemState.updateTcbAtCode; split
  · exact .refl st
  · exact .mapTcbInPlace _ _ _ hW

theorem updateTcbAtCode_scheduler (st : SystemState) (k : Nat) (g : TCB → TCB) :
    (st.updateTcbAtCode k g).scheduler = st.scheduler := by
  unfold updateTcbAtCode; split
  · rfl
  · exact mapTcbInPlace_scheduler _ _ _

theorem runLinkOn_updateTcbAtCode_map (st : SystemState) (k : Nat) (g : TCB → TCB)
    (c : CoreId) (G : RunQueueLink → RunQueueLink)
    (hg : ∀ tcb, (g tcb).runLinkOn c = G (tcb.runLinkOn c))
    (hG : G RunQueue.RunQueueLink.none = RunQueue.RunQueueLink.none) (x : SeLe4n.ThreadId) :
    (st.updateTcbAtCode k g).runLinkOn c x =
      if code x = k then G (st.runLinkOn c x) else st.runLinkOn c x := by
  unfold updateTcbAtCode
  by_cases hk : k = 0
  · subst hk; rw [if_pos rfl, if_neg (code_ne_zero x)]
  · rw [if_neg hk, runLinkOn_mapTcbInPlace_map st _ g c G hg hG x]
    by_cases hx : code x = k
    · rw [if_pos hx, if_pos (by rw [← hx, decode_code])]
    · rw [if_neg hx, if_neg (fun e => hx (by rw [e]; exact (RunQueue.code_eq_iff _ _).mpr ⟨hk, rfl⟩))]

/-- WS-ZA ZA4.5: core `c`'s queue in order, walked along the threads' successor
links from the core's head, at most its size steps. -/
def runQueueWalk (st : SystemState) (c : CoreId) : List SeLe4n.ThreadId :=
  walk (fun t => (st.runLinkOn c t).next) (st.scheduler.runQueueEndsOnCore c).size
    (st.scheduler.runQueueEndsOnCore c).head

/-- WS-ZA ZA4.5: core `c`'s highest occupied priority bucket in order, walked
along the threads' bucket links from that bucket's head; empty when the core's
queue is. -/
def runMaxBucketWalk (st : SystemState) (c : CoreId) : List SeLe4n.ThreadId :=
  walk (fun t => (st.runLinkOn c t).bucketNext) (st.scheduler.runQueueEndsOnCore c).size
    (if (st.scheduler.runQueueEndsOnCore c).maxCode = 0 then 0
      else (RunQueue.endsOf (st.scheduler.runQueueEndsOnCore c).buckets
        ⟨(st.scheduler.runQueueEndsOnCore c).maxCode - 1⟩).head)

namespace runQueueRefinedOnCore

variable {st : SystemState} {c : CoreId}

theorem contains (h : st.runQueueRefinedOnCore c) (t : SeLe4n.ThreadId) :
    (st.runLinkOn c t).queued = (st.scheduler.runQueueOnCore c).contains t := by
  rw [h.2 t, RunQueue.queuedLink_queued]

/-- Membership read from the threads' links is the queue's. -/
theorem queuedOn (h : st.runQueueRefinedOnCore c) (t : SeLe4n.ThreadId) :
    st.queuedOn c t = (st.scheduler.runQueueOnCore c).contains t := by
  rw [queuedOn_eq_runLinkOn, h.contains]

/-- A thread whose TCB names core `c` is on `c`'s queue. -/
theorem contains_of_runCoreCode (h : st.runQueueRefinedOnCore c) {t : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? t = some tcb) (hc : tcb.runCoreCode = c.val + 1) :
    (st.scheduler.runQueueOnCore c).contains t = true := by
  rw [← h.queuedOn]; unfold SystemState.queuedOn; rw [hT]; simp [hc]

/-- A queued thread's entry, read from its TCB, is the queue's. -/
theorem link_of_mem (h : st.runQueueRefinedOnCore c) {t : SeLe4n.ThreadId}
    (ht : t ∈ (st.scheduler.runQueueOnCore c).toList) :
    st.runLinkOn c t = RunQueue.linkOf (st.scheduler.runQueueOnCore c).links t := by
  rw [h.2 t]
  exact RunQueue.queuedLink_of_contains
    (((st.scheduler.runQueueOnCore c).mem_toList_iff_mem t).mp ht)

/-- A thread on the queue is a TCB queued on this core. -/
theorem tcb_of_contains (h : st.runQueueRefinedOnCore c) {t : SeLe4n.ThreadId}
    (ht : (st.scheduler.runQueueOnCore c).contains t = true) :
    ∃ tcb, st.getTcb? t = some tcb ∧ tcb.runCoreCode = c.val + 1 :=
  (runLinkOn_queued_iff st c t).mp (by rw [h.contains]; exact ht)

theorem head (h : st.runQueueRefinedOnCore c) :
    (st.scheduler.runQueueEndsOnCore c).head = (st.scheduler.runQueueOnCore c).head := by
  rw [h.1]; rfl
theorem tail (h : st.runQueueRefinedOnCore c) :
    (st.scheduler.runQueueEndsOnCore c).tail = (st.scheduler.runQueueOnCore c).tail := by
  rw [h.1]; rfl
theorem size (h : st.runQueueRefinedOnCore c) :
    (st.scheduler.runQueueEndsOnCore c).size = (st.scheduler.runQueueOnCore c).size := by
  rw [h.1]; rfl
theorem maxCode (h : st.runQueueRefinedOnCore c) :
    (st.scheduler.runQueueEndsOnCore c).maxCode = (st.scheduler.runQueueOnCore c).maxCode := by
  rw [h.1]; rfl
theorem buckets (h : st.runQueueRefinedOnCore c) :
    (st.scheduler.runQueueEndsOnCore c).buckets = (st.scheduler.runQueueOnCore c).buckets := by
  rw [h.1]; rfl

/-- The walk along the threads' successor links from the core's head is the
queue's list. -/
theorem walk_eq (h : st.runQueueRefinedOnCore c) :
    walk (fun t => (st.runLinkOn c t).next) (st.scheduler.runQueueEndsOnCore c).size
      (st.scheduler.runQueueEndsOnCore c).head = (st.scheduler.runQueueOnCore c).toList := by
  have hL := (st.scheduler.runQueueOnCore c).layout_toList
  have hq := (isQueue_congr (nx' := fun t => (st.runLinkOn c t).next)
    (pv' := fun t => (st.runLinkOn c t).prev)
    (fun x hx => by dsimp only; rw [h.link_of_mem hx]) (fun x hx => by dsimp only; rw [h.link_of_mem hx])).mpr hL.queue
  rw [h.size, h.head]
  exact hq.walk_eq (Nat.le_of_eq hL.length)

/-- A bucket's walk along the threads' bucket links is the queue's bucket. -/
theorem bucket_walk_eq (h : st.runQueueRefinedOnCore c) (p : SeLe4n.Priority) :
    walk (fun t => (st.runLinkOn c t).bucketNext) (st.scheduler.runQueueEndsOnCore c).size
      (RunQueue.endsOf (st.scheduler.runQueueEndsOnCore c).buckets p).head =
      (st.scheduler.runQueueOnCore c).atPriority p := by
  have hL := (st.scheduler.runQueueOnCore c).layout_toList
  have hmem : ∀ x ∈ (st.scheduler.runQueueOnCore c).toList.filter
      (fun t => (RunQueue.linkOf (st.scheduler.runQueueOnCore c).links t).prio == p),
      x ∈ (st.scheduler.runQueueOnCore c).toList := fun x hx => (List.mem_filter.mp hx).1
  have hq := (isQueue_congr (nx' := fun t => (st.runLinkOn c t).bucketNext)
    (pv' := fun t => (st.runLinkOn c t).bucketPrev)
    (fun x hx => by dsimp only; rw [h.link_of_mem (hmem x hx)])
    (fun x hx => by dsimp only; rw [h.link_of_mem (hmem x hx)])).mpr (hL.bucket p)
  rw [h.size, h.buckets, RunQueue.atPriority_eq]
  exact hq.walk_eq (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq hL.length))

/-- A thread's priority, read from its TCB, is the queue's. -/
theorem priorityOf (h : st.runQueueRefinedOnCore c) (t : SeLe4n.ThreadId) :
    (if (st.runLinkOn c t).queued then some (st.runLinkOn c t).prio else none) =
      (st.scheduler.runQueueOnCore c).priorityOf t := by
  rw [h.2 t]
  unfold RunQueue.priorityOf
  cases hc : (st.scheduler.runQueueOnCore c).contains t
  · rw [RunQueue.queuedLink_of_not_contains hc]; rfl
  · rw [RunQueue.queuedLink_of_contains hc]
    simp [show (RunQueue.linkOf (st.scheduler.runQueueOnCore c).links t).queued = true from hc]

/-- The priority read from the threads' links is the queue's. -/
theorem queuedPriorityOn (h : st.runQueueRefinedOnCore c) (t : SeLe4n.ThreadId) :
    st.queuedPriorityOn c t = (st.scheduler.runQueueOnCore c).priorityOf t :=
  h.priorityOf t

/-- The walk along the threads' links is the queue's list. -/
theorem runQueueWalk_eq (h : st.runQueueRefinedOnCore c) :
    st.runQueueWalk c = (st.scheduler.runQueueOnCore c).toList :=
  h.walk_eq

/-- The walk of the highest bucket along the threads' links is the queue's. -/
theorem runMaxBucketWalk_eq (h : st.runQueueRefinedOnCore c) :
    st.runMaxBucketWalk c = (st.scheduler.runQueueOnCore c).maxPriorityBucket := by
  unfold runMaxBucketWalk RunQueue.maxPriorityBucket RunQueue.maxPriority
  rw [h.maxCode]
  split
  · show walk _ _ 0 = []
    cases (st.scheduler.runQueueEndsOnCore c).size <;> rfl
  · exact h.bucket_walk_eq _

end runQueueRefinedOnCore

-- ============================================================================
-- Enqueue
-- ============================================================================

/-- WS-ZA ZA4.5: thread `t` joins the back of core `c`'s queue at priority `p`,
as the threads and the core hold it: `t`'s TCB takes the core, the bucket and
its links (behind the queue's last thread and its bucket's last), those two
point forward at `t`, and the core's ends move.  For a thread on no queue;
`runEnqueueOnCore` is the guarded form. -/
def runAppendLinks (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let e := st.scheduler.runQueueEndsOnCore c
  let btail := (RunQueue.endsOf e.buckets p).tail
  let st1 := st.mapTcbInPlace t (fun x => { x with
    runCoreCode := c.val + 1, runPrio := p, runPrevCode := e.tail, runNextCode := 0,
    runBucketPrevCode := btail, runBucketNextCode := 0 })
  let st2 := st1.updateTcbAtCode e.tail (fun x => { x with runNextCode := code t })
  st2.updateTcbAtCode btail (fun x => { x with runBucketNextCode := code t })

/-- The code of the last thread in a queue's bucket for priority `p`. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.bucketTail (e : RunQueueEnds) (p : SeLe4n.Priority) : Nat :=
  (RunQueue.endsOf e.buckets p).tail

/-- `runAppendLinks`'s three TCB writes, on the object table alone, given the
queue's and the bucket's last codes. -/
def appendLinkObjects (o : RHTable SeLe4n.ObjId KernelObject) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (qtail btail : Nat) : RHTable SeLe4n.ObjId KernelObject :=
  let o1 := o.mapValueAt t.toObjId (KernelObject.mapTcb fun x => { x with
    runCoreCode := c.val + 1, runPrio := p, runPrevCode := qtail, runNextCode := 0,
    runBucketPrevCode := btail, runBucketNextCode := 0 })
  let o2 := if qtail = 0 then o1 else
    o1.mapValueAt (decode qtail).toObjId (KernelObject.mapTcb fun x => { x with runNextCode := code t })
  if btail = 0 then o2 else
    o2.mapValueAt (decode btail).toObjId
      (KernelObject.mapTcb fun x => { x with runBucketNextCode := code t })

/-- WS-ZA ZA4.5: the compiled `runAppendLinks`.  The two last codes are read
first; the state record is then rebuilt once around the table writes, with no
branch between taking it apart and rebuilding it, so an exclusive state is
rewritten in place. -/
def runAppendLinksImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let e := st.scheduler.runQueueEndsOnCore c
  let qtail := e.tail
  let btail := e.bucketTail p
  { st with objects := appendLinkObjects st.objects c t p qtail btail }

@[csimp] theorem runAppendLinks_eq_impl : @runAppendLinks = @runAppendLinksImpl := by
  funext st c t p
  unfold runAppendLinks runAppendLinksImpl appendLinkObjects RunQueueEnds.bucketTail
    updateTcbAtCode mapTcbInPlace
  dsimp only
  split <;> split <;> rfl

/-- The ends of a queue once `t` joins it at priority `p`: `RunQueue.insert`'s
ends, read off the old ones. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.append (e : RunQueueEnds) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    RunQueueEnds :=
  let btail := (RunQueue.endsOf e.buckets p).tail
  { buckets := RunQueue.setEnds e.buckets p (RunQueue.appendEnds t btail)
    head := if e.tail = 0 then code t else e.head
    tail := code t
    size := e.size + 1
    maxCode := max e.maxCode (p.val + 1) }

/-- WS-ZA ZA4.5: the compiled `RunQueueEnds.append`.  The ends are taken apart
before the bucket table is rewritten, so on exclusively owned ends the table
reaches `setEnds` with its only reference and is written in place, and the new
ends reuse the old cell. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.appendImpl (e : RunQueueEnds) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : RunQueueEnds :=
  match e with
  | ⟨b, h, tl, s, m⟩ =>
    let btail := (RunQueue.endsOf b p).tail
    ⟨RunQueue.setEnds b p (RunQueue.appendEnds t btail), if tl = 0 then code t else h, code t,
      s + 1, max m (p.val + 1)⟩

@[csimp] theorem _root_.SeLe4n.Kernel.RunQueueEnds.append_eq_impl :
    @RunQueueEnds.append = @RunQueueEnds.appendImpl := by
  funext e t p; cases e; rfl

/-- WS-ZA ZA4.5: thread `t` joins the back of core `c`'s queue at priority `p`,
as the threads and the core hold it (`runAppendLinks`, `RunQueueEnds.append`). -/
def runAppendOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st3 := st.runAppendLinks c t p
  let e' := (st3.scheduler.runQueueEndsOnCore c).append t p
  { st3 with scheduler := st3.scheduler.setRunQueueEndsOnCore c e' }

/-- WS-ZA ZA4.5: the compiled `runAppendOnCore`: the core's ends are rewritten
in their slot (`modifyRunQueueEndsOnCore`). -/
def runAppendOnCoreImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st3 := st.runAppendLinks c t p
  { st3 with scheduler := st3.scheduler.modifyRunQueueEndsOnCore c (·.append t p) }

@[csimp] theorem runAppendOnCore_eq_impl : @runAppendOnCore = @runAppendOnCoreImpl := by
  funext st c t p
  simp only [runAppendOnCore, runAppendOnCoreImpl, SchedulerState.modifyRunQueueEndsOnCore_eq]

/-- The link half of `runEnqueueAdmits`: a TCB on no core's queue, or already
on `c`'s. -/
def runLinksAdmit (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? t with
  | some tcb =>
      tcb.runCoreCode == c.val + 1 || tcb.runCoreCode == 0 ||
        decide (Concurrency.numCores < tcb.runCoreCode)
  | none => false

/-- WS-ZA ZA4.5: may `t` join core `c`'s queue?  Only a thread — a TCB — on no
core's queue, or already on `c`'s: a TCB holds one run core, so a thread is on
at most one queue, as seL4's single `tcbQueued` bit keeps it.  A run-core code
naming no core places the thread on no queue.  An idle thread never joins a
queue: seL4 runs the idle thread only when nothing is queued and never
enqueues it, so a preemption of an idle core leaves its idle thread off every
queue. -/
def runEnqueueAdmits (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : Bool :=
  !Kernel.isIdleThreadId t && st.runLinksAdmit c t

/-- WS-ZA ZA4.5: the enqueue of an admitted thread — `RunQueue.insert` on the
core's queue, written through the threads; a thread already queued there is
left where it is. -/
def runEnqueueAdmitted (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st' := if (st.runLinkOn c t).queued then st else st.runAppendOnCore c t p
  let rq := (st'.scheduler.runQueueOnCore c).insert t p
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

/-- WS-ZA ZA4.5: the compiled `runEnqueueAdmitted`: membership is read as the
run-core field (`queuedOn`), with no link record built. -/
def runEnqueueAdmittedImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st' := if st.queuedOn c t then st else st.runAppendOnCore c t p
  let rq := (st'.scheduler.runQueueOnCore c).insert t p
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

@[csimp] theorem runEnqueueAdmitted_eq_impl : @runEnqueueAdmitted = @runEnqueueAdmittedImpl := by
  funext st c t p
  simp only [runEnqueueAdmitted, runEnqueueAdmittedImpl, queuedOn_eq_runLinkOn]

/-- WS-ZA ZA4.5: enqueue `t` on core `c` at priority `p`.  A thread queued on
another core stays there and a non-thread is not queued (`runEnqueueAdmits`):
like seL4's `tcbSchedEnqueue`, which does nothing to a thread whose
`tcbQueued` bit is set, the enqueue never gives a thread a second place. -/
def runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  if st.runEnqueueAdmits c t then st.runEnqueueAdmitted c t p else st

theorem runEnqueueOnCore_of_admits {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = true) :
    st.runEnqueueOnCore c t p = st.runEnqueueAdmitted c t p := by
  unfold runEnqueueOnCore; rw [if_pos h]

theorem runEnqueueOnCore_of_not_admits {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = false) :
    st.runEnqueueOnCore c t p = st := by
  unfold runEnqueueOnCore; rw [if_neg (by simp [h])]

/-- Admission reads only the thread's core code. -/
theorem runEnqueueAdmits_congr {st st' : SystemState} {y : SeLe4n.ThreadId}
    (h : (st'.getTcb? y).map TCB.runCoreCode = (st.getTcb? y).map TCB.runCoreCode)
    (c : CoreId) : st'.runEnqueueAdmits c y = st.runEnqueueAdmits c y := by
  unfold runEnqueueAdmits runLinksAdmit
  cases h1 : st'.getTcb? y <;> cases h2 : st.getTcb? y <;> rw [h1, h2] at h <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h <;>
    simp only [h]

theorem mapTcbInPlace_runCoreCode (st : SystemState) (t y : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ x, (g x).runCoreCode = x.runCoreCode ∨ t ≠ y) :
    ((st.mapTcbInPlace t g).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  by_cases hy : y = t
  · subst hy
    rw [mapTcbInPlace_getTcb?_self, Option.map_map]
    cases st.getTcb? y with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Function.comp_apply]
      rcases hg x with h | h
      · rw [h]
      · exact absurd rfl h
  · rw [mapTcbInPlace_getTcb?_ne _ _ _ _ (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)]

theorem updateTcbAtCode_runCoreCode (st : SystemState) (k : Nat) (g : TCB → TCB)
    (hg : ∀ x, (g x).runCoreCode = x.runCoreCode) (y : SeLe4n.ThreadId) :
    ((st.updateTcbAtCode k g).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  unfold updateTcbAtCode; split
  · rfl
  · exact mapTcbInPlace_runCoreCode _ _ _ _ (fun x => Or.inl (hg x))

/-- A TCB rewrite that keeps the core code keeps every thread's. -/
theorem updateTcb_runCoreCode (st : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ x, (f x).runCoreCode = x.runCoreCode) (hInv : st.objects.invExt)
    (y : SeLe4n.ThreadId) :
    ((st.updateTcb tid f).getTcb? y).map TCB.runCoreCode = (st.getTcb? y).map TCB.runCoreCode := by
  by_cases hy : y = tid
  · subst hy
    rw [updateTcb_getTcb?_self _ _ _ hInv, Option.map_map]
    cases st.getTcb? y with
    | none => rfl
    | some x => simp only [Option.map_some, Function.comp_apply, hf]
  · rw [updateTcb_getTcb?_ne _ _ _ hInv _ (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)]

/-- An admitted enqueue of `t` moves no other thread's core code. -/
theorem runEnqueueAdmitted_runCoreCode_ne (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hy : y ≠ t) :
    ((st.runEnqueueAdmitted c t p).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  unfold runEnqueueAdmitted; dsimp only
  split
  · rfl
  · show ((st.runAppendLinks c t p).getTcb? y).map TCB.runCoreCode = _
    unfold runAppendLinks; dsimp only
    refine (updateTcbAtCode_runCoreCode _ _ (fun x => { x with runBucketNextCode := code t })
      (fun _ => rfl) y).trans ?_
    refine (updateTcbAtCode_runCoreCode _ _ (fun x => { x with runNextCode := code t })
      (fun _ => rfl) y).trans ?_
    exact mapTcbInPlace_runCoreCode _ _ _ _ (fun _ => Or.inr (Ne.symm hy))

/-- An enqueue of `t` moves no other thread's core code. -/
theorem runEnqueueOnCore_runCoreCode_ne (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hy : y ≠ t) :
    ((st.runEnqueueOnCore c t p).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_runCoreCode_ne st c t y p hy
  · rfl

/-- The append's TCB writes give `t` core `c`'s code and keep every other
thread's. -/
theorem runAppendLinks_runCoresAgree_self (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    ((st.runAppendLinks c t p).getTcb? t).map TCB.runCoreCode =
      (st.getTcb? t).map (fun _ => c.val + 1) := by
  unfold runAppendLinks; dsimp only
  rw [updateTcbAtCode_runCoreCode _ _ (fun x => { x with runBucketNextCode := code t })
      (fun _ => rfl) t,
    updateTcbAtCode_runCoreCode _ _ (fun x => { x with runNextCode := code t }) (fun _ => rfl) t,
    mapTcbInPlace_getTcb?_self, Option.map_map]
  rfl

/-- WS-ZA ZA4.5: after the admitted enqueue of `t` on core `c`, `t` — when it is
a thread — is queued on `c` and on no other core, and no other thread moves on
or off a queue. -/
theorem runEnqueueAdmitted_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runEnqueueAdmitted c t p).queuedOn c' y =
      if y = t then ((st.getTcb? t).isSome && decide (c' = c)) else st.queuedOn c' y := by
  by_cases hy : y = t
  · subst hy
    rw [if_pos rfl]
    have hcode : ∀ tcb : TCB, tcb.runCoreCode = c.val + 1 →
        (tcb.runCoreCode == c'.val + 1) = decide (c' = c) := by
      intro tcb hC
      rw [hC]
      by_cases hc : c' = c
      · subst hc; simp
      · simp only [hc, decide_false, beq_eq_false_iff_ne]
        intro h; exact hc (Fin.ext (by omega))
    unfold runEnqueueAdmitted; dsimp only
    split
    · next hq =>
      show st.queuedOn c' y = _
      obtain ⟨tcb, hT, hC⟩ := (runLinkOn_queued_iff st c y).mp hq
      unfold queuedOn; rw [hT]
      simp only [Option.isSome_some, Bool.true_and]
      exact hcode tcb hC
    · show (st.runAppendLinks c y p).queuedOn c' y = _
      have h := runAppendLinks_runCoresAgree_self st c y p
      unfold queuedOn
      cases h1 : (st.runAppendLinks c y p).getTcb? y <;> cases h2 : st.getTcb? y <;>
        rw [h1, h2] at h <;>
        simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h
      · rfl
      · simp only [Option.isSome_some, Bool.true_and]; exact hcode _ h
  · rw [if_neg hy]
    have h := runEnqueueAdmitted_runCoreCode_ne st c t y p hy
    unfold queuedOn
    cases h1 : (st.runEnqueueAdmitted c t p).getTcb? y <;> cases h2 : st.getTcb? y <;>
      rw [h1, h2] at h <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h <;>
      simp only [h]


/-- A thread on no queue other than `c`'s is admitted. -/
theorem runEnqueueAdmits_of_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (hR : st.runQueueRefined) (hT : (st.getTcb? t).isSome)
    (hOther : ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false)
    (hI : Kernel.isIdleThreadId t = false) :
    st.runEnqueueAdmits c t = true := by
  obtain ⟨tcb, hTcb⟩ := Option.isSome_iff_exists.mp hT
  unfold runEnqueueAdmits runLinksAdmit; rw [hI, hTcb, Bool.not_false, Bool.true_and]
  by_cases h0 : tcb.runCoreCode = 0
  · simp [h0]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    by_cases hc : k = c.val
    · simp [hk, hc]
    · by_cases hlt : k < Concurrency.numCores
      · exfalso
        have hq := (hR ⟨k, hlt⟩).contains t
        rw [hOther ⟨k, hlt⟩ (fun e => hc (by rw [← e])), runLinkOn, hTcb] at hq
        simp only [TCB.runLinkOn, hk, Nat.succ_eq_add_one, if_true] at hq
        cases hq
      · simp only [hk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
        omega

/-- A thread whose links admit core `c` is on no other core's queue. -/
theorem runLinksAdmit_not_contains {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (hR : st.runQueueRefined) (h : st.runLinksAdmit c t = true) :
    ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false := by
  intro c' hne
  rw [← (hR c').contains, runLinkOn]
  unfold runLinksAdmit at h
  cases hT : st.getTcb? t with
  | none => rfl
  | some tcb =>
    rw [hT] at h
    unfold TCB.runLinkOn
    dsimp only at h ⊢
    by_cases hc : tcb.runCoreCode = c'.val + 1
    · rw [if_pos hc]
      exfalso
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      have := c'.isLt
      rcases h with (h | h) | h
      · exact hne (Fin.ext (by omega))
      · omega
      · omega
    · rw [if_neg hc]; rfl

/-- An admitted thread is on no other core's queue. -/
theorem runEnqueueAdmits_not_contains {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (hR : st.runQueueRefined) (h : st.runEnqueueAdmits c t = true) :
    ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false :=
  runLinksAdmit_not_contains hR ((Bool.and_eq_true _ _).mp h).2

/-- An admitted thread is no idle thread. -/
theorem runEnqueueAdmits_not_idle {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (h : st.runEnqueueAdmits c t = true) : Kernel.isIdleThreadId t = false := by
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  cases hI : Kernel.isIdleThreadId t
  · rfl
  · rw [hI] at h1; cases h1

theorem runEnqueueAdmits_isSome {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (h : st.runEnqueueAdmits c t = true) : (st.getTcb? t).isSome := by
  replace h := ((Bool.and_eq_true _ _).mp h).2
  unfold runLinksAdmit at h
  cases hT : st.getTcb? t with
  | none => rw [hT] at h; cases h
  | some _ => rfl

/-- A thread is admitted on `c` exactly when it is a TCB its links queue on no
other core. -/
theorem runEnqueueAdmits_iff {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (hT : (st.getTcb? t).isSome) (hI : Kernel.isIdleThreadId t = false) :
    st.runEnqueueAdmits c t = true ↔ ∀ c', c' ≠ c → st.queuedOn c' t = false := by
  obtain ⟨tcb, hTcb⟩ := Option.isSome_iff_exists.mp hT
  unfold runEnqueueAdmits runLinksAdmit queuedOn
  rw [hI, Bool.not_false, Bool.true_and]
  simp only [hTcb, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, beq_eq_false_iff_ne]
  constructor
  · rintro ((h1 | h0) | hlt) c' hne he
    · exact hne (Fin.ext (by omega))
    · omega
    · have := c'.isLt; omega
  · intro hN
    by_cases h0 : tcb.runCoreCode = 0
    · exact Or.inl (Or.inr h0)
    · by_cases hlt : Concurrency.numCores < tcb.runCoreCode
      · exact Or.inr hlt
      · refine Or.inl (Or.inl ?_)
        by_cases hc : (⟨tcb.runCoreCode - 1, by omega⟩ : CoreId) = c
        · rw [← hc]; show tcb.runCoreCode = tcb.runCoreCode - 1 + 1; omega
        · exact absurd (show tcb.runCoreCode = tcb.runCoreCode - 1 + 1 by omega) (hN _ hc)

theorem runEnqueueOnCore_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runEnqueueOnCore c t p).queuedOn c' y =
      if y = t ∧ st.runEnqueueAdmits c t = true then decide (c' = c)
      else st.queuedOn c' y := by
  unfold runEnqueueOnCore
  split
  · next hA =>
    rw [runEnqueueAdmitted_queuedOn]
    by_cases hy : y = t
    · subst hy
      rw [if_pos rfl, if_pos ⟨rfl, hA⟩, runEnqueueAdmits_isSome hA, Bool.true_and]
    · rw [if_neg hy, if_neg (fun h => hy h.1)]
  · next hA =>
    rw [if_neg (fun h => hA h.2)]

/-- An enqueue on core `c` queues nothing new on any other core. -/
theorem runEnqueueOnCore_queuedOn_imp_ne {st : SystemState} {c c' : CoreId} {t y : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (h : c' ≠ c) (hq : (st.runEnqueueOnCore c t p).queuedOn c' y = true) :
    st.queuedOn c' y = true := by
  rw [runEnqueueOnCore_queuedOn] at hq
  split at hq
  · exact absurd (of_decide_eq_true hq) h
  · exact hq

/-- An enqueue leaves a thread with a TCB queued on some core, read off its own
links: on `c` when admitted, otherwise on the core its links already name. -/
theorem runEnqueueOnCore_queuedOn_somewhere {st : SystemState} {c : CoreId}
    {t : SeLe4n.ThreadId} (p : SeLe4n.Priority) (hT : (st.getTcb? t).isSome)
    (hI : Kernel.isIdleThreadId t = false) :
    ∃ c', (st.runEnqueueOnCore c t p).queuedOn c' t = true := by
  cases hA : st.runEnqueueAdmits c t
  · obtain ⟨tcb, hTcb⟩ := Option.isSome_iff_exists.mp hT
    have hA' := hA
    simp only [runEnqueueAdmits, runLinksAdmit, hI, Bool.not_false, Bool.true_and, hTcb, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not, Nat.not_lt] at hA'
    obtain ⟨⟨_, h0⟩, hle⟩ := hA'
    refine ⟨⟨tcb.runCoreCode - 1, by omega⟩, ?_⟩
    rw [runEnqueueOnCore_queuedOn, if_neg (fun h => absurd h.2 (by simp [hA]))]
    simp only [queuedOn, hTcb, beq_iff_eq]
    show tcb.runCoreCode = tcb.runCoreCode - 1 + 1
    omega
  · exact ⟨c, by rw [runEnqueueOnCore_queuedOn, if_pos ⟨rfl, hA⟩]; simp⟩

/-- An admitted enqueue on `c` leaves `t` admitted on `c`: it is on `c`'s
queue now, or was already. -/
theorem runEnqueueAdmitted_runEnqueueAdmits_self (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = true) :
    (st.runEnqueueAdmitted c t p).runEnqueueAdmits c t = true := by
  unfold runEnqueueAdmitted; dsimp only
  split
  · exact h
  · show (st.runAppendLinks c t p).runEnqueueAdmits c t = true
    obtain ⟨tcb, hT⟩ := Option.isSome_iff_exists.mp (runEnqueueAdmits_isSome h)
    have hCode : ((st.runAppendLinks c t p).getTcb? t).map TCB.runCoreCode = some (c.val + 1) := by
      unfold runAppendLinks; dsimp only
      refine (updateTcbAtCode_runCoreCode _ _ (fun x => { x with runBucketNextCode := code t })
        (fun _ => rfl) t).trans ?_
      refine (updateTcbAtCode_runCoreCode _ _ (fun x => { x with runNextCode := code t })
        (fun _ => rfl) t).trans ?_
      rw [mapTcbInPlace_getTcb?_self, hT]; rfl
    unfold runEnqueueAdmits runLinksAdmit
    rw [runEnqueueAdmits_not_idle h, Bool.not_false, Bool.true_and]
    cases hA : (st.runAppendLinks c t p).getTcb? t with
    | none => rw [hA] at hCode; cases hCode
    | some x =>
      rw [hA] at hCode
      simp only [Option.map_some, Option.some.injEq] at hCode
      simp [hCode]

/-- An enqueue keeps an admitted thread admitted on the same core. -/
theorem runEnqueueOnCore_runEnqueueAdmits (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c y = true) :
    (st.runEnqueueOnCore c t p).runEnqueueAdmits c y = true := by
  unfold runEnqueueOnCore; split
  · by_cases hy : y = t
    · subst hy; exact runEnqueueAdmitted_runEnqueueAdmits_self st c y p h
    · rw [runEnqueueAdmits_congr (runEnqueueAdmitted_runCoreCode_ne st c t y p hy)]; exact h
  · exact h

theorem runAppendLinks_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runAppendLinks c t p).scheduler = st.scheduler := by
  simp only [runAppendLinks, updateTcbAtCode_scheduler, mapTcbInPlace_scheduler]

theorem runAppendOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runAppendOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runAppendOnCore
  rw [SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runAppendLinks_scheduler]

theorem runEnqueueAdmitted_runQueueOnCore_self (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueAdmitted c t p).scheduler.runQueueOnCore c =
      (st.scheduler.runQueueOnCore c).insert t p := by
  unfold runEnqueueAdmitted
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  split
  · rfl
  · rw [runAppendOnCore_runQueueOnCore]

/-- An admitted thread joins the core's queue (`RunQueue.insert`). -/
theorem runEnqueueOnCore_runQueueOnCore_self {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = true) :
    (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c =
      (st.scheduler.runQueueOnCore c).insert t p := by
  rw [runEnqueueOnCore_of_admits p h, runEnqueueAdmitted_runQueueOnCore_self]

theorem runEnqueueAdmitted_runQueueOnCore_ne (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (h : c ≠ c') :
    (st.runEnqueueAdmitted c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runEnqueueAdmitted
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
  split
  · rfl
  · rw [runAppendOnCore_runQueueOnCore]

theorem runEnqueueOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (h : c ≠ c') :
    (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runEnqueueOnCore
  split
  · exact runEnqueueAdmitted_runQueueOnCore_ne st c c' t p h
  · rfl

/-- Core `c`'s queue after an enqueue there: the insert when admitted, the
queue as it was otherwise. -/
theorem runEnqueueOnCore_runQueueOnCore_self_eq (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c =
      if st.runEnqueueAdmits c t then (st.scheduler.runQueueOnCore c).insert t p
      else st.scheduler.runQueueOnCore c := by
  unfold runEnqueueOnCore
  split
  · exact runEnqueueAdmitted_runQueueOnCore_self st c t p
  · rfl

/-- Admission reads only the run-core code, so a TCB rewrite that keeps the code
keeps every admission. -/
theorem runEnqueueAdmits_rewriteObject_tcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {t t' : TCB} (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hT : st.getTcb? tid = some t) (hCode : t'.runCoreCode = t.runCoreCode)
    (c : CoreId) (x : SeLe4n.ThreadId) :
    (st.rewriteObject tid.toObjId (.tcb t') h).runEnqueueAdmits c x = st.runEnqueueAdmits c x := by
  unfold runEnqueueAdmits runLinksAdmit
  by_cases hx : x = tid
  · subst hx
    rw [rewriteObject_tcb_getTcb?_self st x t' h hInv, hT]
    dsimp only
    rw [hCode]
  · rw [rewriteObject_getTcb?_ne st _ _ h hInv x
      (fun he => hx (SeLe4n.ThreadId.toObjId_injective _ _ he.symm))]

/-- A SchedContext rewrite keeps every thread's admission: the rewritten key
held a SchedContext, so no thread lives there. -/
theorem runEnqueueAdmits_rewriteObject_schedContext {st : SystemState}
    {scId : SeLe4n.SchedContextId} {sc : SchedContext} {new : KernelObject}
    (h : st.rewriteAdmissible scId.toObjId new) (hInv : st.objects.invExt)
    (hSc : st.getSchedContext? scId = some sc) (c : CoreId) (x : SeLe4n.ThreadId) :
    (st.rewriteObject scId.toObjId new h).runEnqueueAdmits c x = st.runEnqueueAdmits c x := by
  by_cases hx : scId.toObjId = x.toObjId
  · have hNone : st.getTcb? x = none := by
      cases hT : st.getTcb? x with
      | none => rfl
      | some t =>
        have h1 := (getTcb?_eq_some_iff st x t).mp hT
        have h2 := (getSchedContext?_eq_some_iff st scId sc).mp hSc
        rw [hx, h1] at h2; cases h2
    have hA : st.runEnqueueAdmits c x = false := by
      unfold runEnqueueAdmits runLinksAdmit; rw [hNone]; simp
    rw [hA]
    unfold runEnqueueAdmits runLinksAdmit
    unfold getTcb?
    rw [← hx, rewriteObject_objects_self st _ _ h hInv]
    obtain ⟨old, hOld, hTy, _⟩ := h
    rw [(getSchedContext?_eq_some_iff st scId sc).mp hSc] at hOld
    cases hOld
    cases new <;> first | (dsimp only; exact Bool.and_false _) | cases hTy
  · unfold runEnqueueAdmits runLinksAdmit
    rw [rewriteObject_getTcb?_ne st _ _ h hInv x hx]

/-- An enqueue on `c` adds at most `t` to `c`'s queue. -/
theorem runEnqueueOnCore_mem_runQueueOnCore_self {st : SystemState} {c : CoreId}
    {t x : SeLe4n.ThreadId} {p : SeLe4n.Priority}
    (h : x ∈ (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c) :
    x ∈ st.scheduler.runQueueOnCore c ∨ x = t := by
  unfold runEnqueueOnCore at h
  split at h
  · rwa [runEnqueueAdmitted_runQueueOnCore_self, RunQueue.mem_insert] at h
  · exact Or.inl h

/-- Under the link agreement an enqueue leaves a thread queued on some core: on
`c` when admitted, and otherwise on the core its links already name. -/
theorem runEnqueueOnCore_queued_somewhere {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (hR : st.runQueueRefined) (hT : (st.getTcb? t).isSome)
    (hI : Kernel.isIdleThreadId t = false) :
    ∃ c', t ∈ (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c' := by
  cases hA : st.runEnqueueAdmits c t
  · rw [runEnqueueOnCore_of_not_admits p hA]
    refine Classical.byContradiction fun hNo => ?_
    have hAll : ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false :=
      fun c' _ => Bool.eq_false_iff.mpr fun hc => hNo ⟨c', hc⟩
    rw [runEnqueueAdmits_of_refined hR hT hAll hI] at hA
    cases hA
  · refine ⟨c, ?_⟩
    rw [runEnqueueOnCore_runQueueOnCore_self p hA, RunQueue.mem_insert]
    exact Or.inr rfl

theorem runAppendLinks_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    (st.runAppendLinks c t p).objects.invExt :=
  updateTcbAtCode_objects_invExt _ _ _ (updateTcbAtCode_objects_invExt _ _ _
    (mapTcbInPlace_objects_invExt _ _ _ hInv))

/-- The in-place link writes keep the kernel-level table invariant: they
rewrite a resident value, so the size and capacity are unchanged. -/
theorem mapTcbInPlace_objects_invExtK (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hK : st.objects.invExtK) : (st.mapTcbInPlace t g).objects.invExtK :=
  ⟨RHTable.mapValueAt_invExt _ _ _ hK.1,
   by simp only [mapTcbInPlace, RHTable.mapValueAt_size, RHTable.mapValueAt_capacity]; exact hK.2.1,
   by simp only [mapTcbInPlace, RHTable.mapValueAt_capacity]; exact hK.2.2⟩

theorem updateTcbAtCode_objects_invExtK (st : SystemState) (k : Nat) (g : TCB → TCB)
    (hK : st.objects.invExtK) : (st.updateTcbAtCode k g).objects.invExtK := by
  unfold updateTcbAtCode; split
  · exact hK
  · exact mapTcbInPlace_objects_invExtK _ _ _ hK

theorem runAppendLinks_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hK : st.objects.invExtK) :
    (st.runAppendLinks c t p).objects.invExtK :=
  updateTcbAtCode_objects_invExtK _ _ _ (updateTcbAtCode_objects_invExtK _ _ _
    (mapTcbInPlace_objects_invExtK _ _ _ hK))

theorem runAppendOnCore_objects (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runAppendOnCore c t p).objects = (st.runAppendLinks c t p).objects :=
  rfl

theorem runAppendOnCore_runQueueEndsOnCore (st : SystemState) (c c' : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runAppendOnCore c t p).scheduler.runQueueEndsOnCore c' =
      if c' = c then (st.scheduler.runQueueEndsOnCore c).append t p
      else st.scheduler.runQueueEndsOnCore c' := by
  unfold runAppendOnCore
  by_cases h : c' = c
  · subst h; rw [if_pos rfl, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_self,
      runAppendLinks_scheduler]
  · rw [if_neg h, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_ne _ _ _ _ (Ne.symm h),
      runAppendLinks_scheduler]

/-- The entry every core's queue reads for every thread after the append: the
joining thread's TCB entry, then the forward links of the queue's and the
bucket's old last threads. -/
theorem runAppendLinks_runLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (x : SeLe4n.ThreadId) :
    (st.runAppendLinks c t p).runLinkOn c' x =
      let e := st.scheduler.runQueueEndsOnCore c
      let btail := (RunQueue.endsOf e.buckets p).tail
      let L1 := if x = t then
          (match st.getTcb? t with
           | some tcb => ({ tcb with
              runCoreCode := c.val + 1, runPrio := p, runPrevCode := e.tail, runNextCode := 0,
              runBucketPrevCode := btail, runBucketNextCode := 0 } : TCB).runLinkOn c'
           | none => RunQueue.RunQueueLink.none)
        else st.runLinkOn c' x
      let L2 := if code x = e.tail then RunQueueLink.withNextIfQueued (code t) L1 else L1
      if code x = btail then RunQueueLink.withBucketNextIfQueued (code t) L2 else L2 := by
  unfold runAppendLinks
  rw [runLinkOn_updateTcbAtCode_map _ _ _ c' _ (fun tcb => TCB.runLinkOn_setBucketNext tcb _ c')
      (RunQueueLink.withBucketNextIfQueued_none _),
    runLinkOn_updateTcbAtCode_map _ _ _ c' _ (fun tcb => TCB.runLinkOn_setNext tcb _ c')
      (RunQueueLink.withNextIfQueued_none _)]
  by_cases hx : x = t
  · subst hx; rw [runLinkOn_mapTcbInPlace_self _ _ _]; simp only [if_true]
  · rw [runLinkOn_mapTcbInPlace_ne _ _ _ _ hx]; simp only [hx, if_false]

theorem _root_.SeLe4n.Model.RunQueueLink.withNextIfQueued_of_not_queued {l : RunQueueLink}
    (h : l.queued = false) (v : Nat) : RunQueueLink.withNextIfQueued v l = l := by
  unfold RunQueueLink.withNextIfQueued; rw [if_neg (by rw [h]; decide)]
theorem _root_.SeLe4n.Model.RunQueueLink.withBucketNextIfQueued_of_not_queued {l : RunQueueLink}
    (h : l.queued = false) (v : Nat) : RunQueueLink.withBucketNextIfQueued v l = l := by
  unfold RunQueueLink.withBucketNextIfQueued; rw [if_neg (by rw [h]; decide)]

@[simp] theorem runLinkOn_withScheduler (st : SystemState) (s : SchedulerState) (c : CoreId)
    (x : SeLe4n.ThreadId) : ({ st with scheduler := s } : SystemState).runLinkOn c x = st.runLinkOn c x :=
  rfl

theorem runAppendOnCore_runLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (x : SeLe4n.ThreadId) :
    (st.runAppendOnCore c t p).runLinkOn c' x = (st.runAppendLinks c t p).runLinkOn c' x := rfl

/-- Writing a core's queue back into its slot changes nothing. -/
theorem _root_.SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore
    (s : SchedulerState) (c : CoreId) : s.setRunQueueOnCore c (s.runQueueOnCore c) = s := by
  unfold SchedulerState.setRunQueueOnCore SchedulerState.runQueueOnCore
  cases s
  simp only [SchedulerState.mk.injEq, and_true]
  exact SeLe4n.Erased.ext (by simp [Vector.get])

/-- WS-ZA ZA4.5: enqueueing a TCB that is on no other core's queue keeps every
core's queue in agreement with the threads. -/
theorem runEnqueueAdmitted_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (hR : st.runQueueRefined) 
    (hT : (st.getTcb? t).isSome)
    (hOther : ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false) :
    (st.runEnqueueAdmitted c t p).runQueueRefined := by
  unfold runEnqueueAdmitted
  by_cases hq : (st.runLinkOn c t).queued = true
  · have hc : (st.scheduler.runQueueOnCore c).contains t = true := by
      rw [← (hR c).contains]; exact hq
    simp only [hq, if_true]
    rw [RunQueue.insert_of_mem _ _ _ hc, SchedulerState.setRunQueueOnCore_runQueueOnCore]
    exact hR
  · simp only [hq, if_false, Bool.false_eq_true]
    have hc : (st.scheduler.runQueueOnCore c).contains t = false := by
      rw [← (hR c).contains]; simpa using hq
    obtain ⟨tcb, hTcb⟩ := Option.isSome_iff_exists.mp hT
    intro c'
    refine ⟨?_, fun x => ?_⟩
    · rw [SchedulerState.setRunQueueOnCore_runQueueEndsOnCore, runAppendOnCore_runQueueEndsOnCore]
      by_cases h : c' = c
      · subst h
        rw [if_pos rfl, SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
          runAppendOnCore_runQueueOnCore, (hR c').1]
        unfold RunQueueEnds.append RunQueue.insert
        rw [dif_neg (by rw [hc]; decide)]
        rfl
      · rw [if_neg h, SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm h),
          runAppendOnCore_runQueueOnCore]
        exact (hR c').1
    · rw [runLinkOn_withScheduler, runAppendOnCore_runLinkOn,
        runAppendLinks_runLinkOn st c t p c' x]
      have hE := (hR c).1
      have hT0 : (st.scheduler.runQueueEndsOnCore c).tail = (st.scheduler.runQueueOnCore c).tail := by
        rw [hE]; rfl
      have hB0 : (st.scheduler.runQueueEndsOnCore c).buckets = (st.scheduler.runQueueOnCore c).buckets := by
        rw [hE]; rfl
      dsimp only
      rw [hT0, hB0, hTcb]
      have htT := RunQueue.code_ne_tail hc
      have htB := RunQueue.code_ne_bucket_tail hc p
      by_cases h : c' = c
      · subst h
        rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, runAppendOnCore_runQueueOnCore]
        unfold RunQueue.queuedLink
        rw [RunQueue.links_insert_of_not_contains hc,
          RunQueue.linkOf_appendLinks (st.scheduler.runQueueOnCore c').links_invExtK _ _ _ _ htT htB]
        by_cases hx : x = t
        · subst hx
          simp only [if_true, if_neg htT, if_neg htB, TCB.runLinkOn, TCB.runLink]
        · simp only [if_neg hx]
          rw [(hR c').2 x]
          unfold RunQueue.queuedLink
          by_cases hLq : (RunQueue.linkOf (st.scheduler.runQueueOnCore c').links x).queued = true
          · by_cases e1 : code x = (st.scheduler.runQueueOnCore c').tail <;>
            by_cases e2 : code x = (RunQueue.endsOf (st.scheduler.runQueueOnCore c').buckets p).tail
            · simp only [hLq, if_pos e1, if_pos e2, if_true, RunQueueLink.withNextIfQueued,
                RunQueueLink.withBucketNextIfQueued]
            · simp only [hLq, if_pos e1, if_neg e2, if_true, RunQueueLink.withNextIfQueued]
            · simp only [hLq, if_neg e1, if_pos e2, if_true, RunQueueLink.withBucketNextIfQueued]
            · simp only [hLq, if_neg e1, if_neg e2, if_true]
              generalize RunQueue.linkOf (st.scheduler.runQueueOnCore c').links x = L at hLq ⊢
              cases L; simp_all
          · have hLq' : (RunQueue.linkOf (st.scheduler.runQueueOnCore c').links x).queued = false := by
              simpa using hLq
            simp [hLq']
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm h),
          runAppendOnCore_runQueueOnCore, ← (hR c').2 x]
        have hL1 : (if x = t then (({ tcb with
              runCoreCode := c.val + 1, runPrio := p, runPrevCode := (st.scheduler.runQueueOnCore c).tail,
              runNextCode := 0,
              runBucketPrevCode := (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).tail,
              runBucketNextCode := 0 } : TCB).runLinkOn c') else st.runLinkOn c' x) = st.runLinkOn c' x := by
          by_cases hx : x = t
          · subst hx
            rw [if_pos rfl, (hR c').2 x, RunQueue.queuedLink_of_not_contains (hOther c' h)]
            unfold TCB.runLinkOn
            rw [if_neg (fun e => h (Fin.ext (by simp at e; omega)))]
          · rw [if_neg hx]
        rw [hL1]
        have hoff : ∀ {k : Nat}, k = (st.scheduler.runQueueOnCore c).tail ∨
            k = (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).tail →
            code x = k → (st.runLinkOn c' x).queued = false := by
          intro k hk e
          have hcx : (st.scheduler.runQueueOnCore c).contains x = true := by
            rcases hk with hk | hk
            · exact RunQueue.contains_of_code_eq_tail (e.trans hk)
            · exact RunQueue.contains_of_code_eq_bucket_tail (e.trans hk)
          have hq1 : (st.runLinkOn c x).queued = true := by rw [(hR c).contains]; exact hcx
          cases hq2 : (st.runLinkOn c' x).queued
          · rfl
          · exact absurd (runLinkOn_queued_unique hq1 hq2).symm h
        by_cases e1 : code x = (st.scheduler.runQueueOnCore c).tail
        · rw [if_pos e1, RunQueueLink.withNextIfQueued_of_not_queued (hoff (Or.inl rfl) e1)]
          by_cases e2 : code x = (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).tail
          · rw [if_pos e2, RunQueueLink.withBucketNextIfQueued_of_not_queued (hoff (Or.inr rfl) e2)]
          · rw [if_neg e2]
        · rw [if_neg e1]
          by_cases e2 : code x = (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).tail
          · rw [if_pos e2, RunQueueLink.withBucketNextIfQueued_of_not_queued (hoff (Or.inr rfl) e2)]
          · rw [if_neg e2]

/-- WS-ZA ZA4.5: **every enqueue keeps every core's queue in agreement with the
threads** — the admission guard is what the agreement needs, so no caller owes
a hypothesis. -/
theorem runEnqueueOnCore_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (hR : st.runQueueRefined) :
    (st.runEnqueueOnCore c t p).runQueueRefined := by
  unfold runEnqueueOnCore
  split
  · next h =>
    exact runEnqueueAdmitted_refined hR (runEnqueueAdmits_isSome h)
      (runEnqueueAdmits_not_contains hR h)
  · exact hR

theorem runLinkOn_eq_none_of_not_queued {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (h : (st.runLinkOn c t).queued = false) : st.runLinkOn c t = RunQueue.RunQueueLink.none := by
  unfold runLinkOn at h ⊢
  cases hT : st.getTcb? t with
  | none => rfl
  | some tcb => rw [hT] at h; exact TCB.runLinkOn_eq_none_of_not_queued h

/-- The empty queue holds the empty entry for every thread. -/
theorem _root_.SeLe4n.Kernel.RunQueue.queuedLink_empty (t : SeLe4n.ThreadId) :
    RunQueue.empty.queuedLink t = RunQueue.RunQueueLink.none := by
  unfold RunQueue.queuedLink
  have h := RunQueue.contains_false_of_not_mem (RunQueue.not_mem_empty t)
  unfold RunQueue.contains at h
  rw [if_neg (by rw [h]; decide)]

/-- An empty queue with empty ends agrees with threads none of which is on it. -/
theorem runQueueRefinedOnCore_of_empty {st : SystemState} {c : CoreId}
    (hQ : st.scheduler.runQueueOnCore c = RunQueue.empty)
    (hE : st.scheduler.runQueueEndsOnCore c = RunQueueEnds.empty)
    (hL : ∀ t, (st.runLinkOn c t).queued = false) : st.runQueueRefinedOnCore c := by
  refine ⟨by rw [hQ, hE]; rfl, fun t => ?_⟩
  rw [hQ, RunQueue.queuedLink_empty]
  exact runLinkOn_eq_none_of_not_queued (hL t)

/-- The default state: no threads, and every queue empty. -/
theorem default_runQueueRefined : (default : SystemState).runQueueRefined := by
  intro c
  refine runQueueRefinedOnCore_of_empty (default_state_perCoreInitialized c).2.1
    (PerCoreVector.replicate_get _ _ c) (fun t => ?_)
  have hNone : (default : SystemState).getTcb? t = none := by
    unfold getTcb?
    simp only [RHTable_getElem?_eq_get?]
    rw [show (default : SystemState).objects = RHTable.empty 16 from rfl, RHTable_get?_empty 16 (by omega)]
  unfold runLinkOn
  rw [hNone]
  rfl

/-- Rewriting a thread's TCB with one that holds the same entry on every core
keeps every thread's entry. -/
theorem runLinkOn_rewriteObject_tcb {st : SystemState} {tid : SeLe4n.ThreadId} {t t' : TCB}
    (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hT : st.getTcb? tid = some t) (hRun : ∀ c, t'.runLinkOn c = t.runLinkOn c)
    (c : CoreId) (x : SeLe4n.ThreadId) :
    (st.rewriteObject tid.toObjId (.tcb t') h).runLinkOn c x = st.runLinkOn c x := by
  by_cases hx : x = tid
  · subst hx
    unfold runLinkOn
    rw [rewriteObject_tcb_getTcb?_self st x t' h hInv, hT]
    exact hRun c
  · unfold runLinkOn
    rw [rewriteObject_getTcb?_ne st _ _ h hInv x
      (fun he => hx (SeLe4n.ThreadId.toObjId_injective _ _ he.symm))]

/-- ...so such a rewrite keeps the agreement. -/
theorem rewriteObject_tcb_runQueueRefined {st : SystemState} {tid : SeLe4n.ThreadId}
    {t t' : TCB} (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hT : st.getTcb? tid = some t) (hRun : ∀ c, t'.runLinkOn c = t.runLinkOn c)
    (hR : st.runQueueRefined) : (st.rewriteObject tid.toObjId (.tcb t') h).runQueueRefined :=
  runQueueRefined_of_frame (runLinkOn_rewriteObject_tcb h hInv hT hRun) rfl rfl hR

/-- A TCB rewritten over a TCB with the same run-queue core moves no thread's
membership. -/
theorem rewriteObject_tcb_queuedOn {st : SystemState} {tid : SeLe4n.ThreadId}
    {t t' : TCB} (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hT : st.getTcb? tid = some t) (hc : t'.runCoreCode = t.runCoreCode)
    (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.rewriteObject tid.toObjId (.tcb t') h).queuedOn c y = st.queuedOn c y := by
  by_cases hy : y = tid
  · subst hy; unfold queuedOn; rw [rewriteObject_tcb_getTcb?_self _ _ _ _ hInv, hT]; simp [hc]
  · exact queuedOn_of_getTcb? (rewriteObject_getTcb?_ne _ _ _ h hInv y
      (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)) c

/-- A TCB update that keeps every core's entry keeps the agreement. -/
theorem updateTcb_runQueueRefined {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (hInv : st.objects.invExt) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hR : st.runQueueRefined) : (st.updateTcb tid f).runQueueRefined := by
  unfold updateTcb
  split
  · rename_i t hT _
    exact rewriteObject_tcb_runQueueRefined _ hInv hT (hf t) hR
  · exact hR

/-- Storing a TCB that claims no run-queue place, at a thread no core's queue
holds, keeps the agreement: the stored thread reads the empty entry before and
after, and every other thread's TCB is untouched. -/
theorem withObjectStored_tcb_runQueueRefined {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : st.objects.invExt) (hT : t.runCoreCode = 0)
    (hNot : ∀ c, (st.runLinkOn c tid).queued = false)
    (hR : st.runQueueRefined) : (st.withObjectStored tid.toObjId (.tcb t)).runQueueRefined := by
  refine runQueueRefined_of_frame (fun c x => ?_)
    (by rw [withObjectStored_scheduler]) (by rw [withObjectStored_scheduler]) hR
  by_cases hx : x = tid
  · subst hx
    rw [runLinkOn_eq_none_of_not_queued (hNot c)]
    unfold runLinkOn getTcb?
    rw [withObjectStored_objects_self st _ _ hInv]
    show t.runLinkOn c = _
    unfold TCB.runLinkOn
    rw [if_neg (by rw [hT]; omega)]
  · unfold runLinkOn getTcb?
    rw [withObjectStored_objects]
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne st.objects _ _ _
      (fun hb => hx (SeLe4n.ThreadId.toObjId_injective _ _ (eq_of_beq hb).symm)) hInv]

/-- A state whose queues and ends are the default ones and none of whose
threads claims a run-queue place agrees: the unchecked boot's shape. -/
theorem runQueueRefined_of_default_queues {st : SystemState}
    (hQ : st.scheduler.runQueue = (default : SystemState).scheduler.runQueue)
    (hE : st.scheduler.runQueueEnds = (default : SystemState).scheduler.runQueueEnds)
    (hT : ∀ t tcb, st.getTcb? t = some tcb → tcb.runCoreCode = 0) : st.runQueueRefined := by
  intro c
  refine runQueueRefinedOnCore_of_empty ?_ ?_ (fun t => ?_)
  · unfold SchedulerState.runQueueOnCore; rw [hQ]
    exact (default_state_perCoreInitialized c).2.1
  · unfold SchedulerState.runQueueEndsOnCore; rw [hE]
    exact PerCoreVector.replicate_get _ _ c
  · unfold runLinkOn
    cases h : st.getTcb? t with
    | none => rfl
    | some tcb =>
      show (tcb.runLinkOn c).queued = false
      unfold TCB.runLinkOn
      rw [if_neg (by rw [hT t tcb h]; omega)]
      rfl

theorem _root_.SeLe4n.Model.RunQueueLink.withPrevIfQueued_of_not_queued {l : RunQueueLink}
    (h : l.queued = false) (v : Nat) : RunQueueLink.withPrevIfQueued v l = l := by
  unfold RunQueueLink.withPrevIfQueued; rw [if_neg (by rw [h]; decide)]
theorem _root_.SeLe4n.Model.RunQueueLink.withBucketPrevIfQueued_of_not_queued {l : RunQueueLink}
    (h : l.queued = false) (v : Nat) : RunQueueLink.withBucketPrevIfQueued v l = l := by
  unfold RunQueueLink.withBucketPrevIfQueued; rw [if_neg (by rw [h]; decide)]

-- ============================================================================
-- Dequeue
-- ============================================================================

/-- WS-ZA ZA4.5: the TCB writes that take `t` out of its queue, given its four
links (read before any write): each neighbour takes over the link `t` held
towards the other, and `t` is marked on no core with its own links cleared
(`TCB.detachRun`).  As `RunQueue.unlinkLinks`. -/
def runUnlinkLinks (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) : SystemState :=
  let st1 := st.updateTcbAtCode pv (fun y => { y with runNextCode := nx })
  let st2 := st1.updateTcbAtCode nx (fun y => { y with runPrevCode := pv })
  let st3 := st2.updateTcbAtCode bpv (fun y => { y with runBucketNextCode := bnx })
  let st4 := st3.updateTcbAtCode bnx (fun y => { y with runBucketPrevCode := bpv })
  st4.mapTcbInPlace t TCB.detachRun

/-- A TCB write at a link code on the object table; nothing for the code `0`. -/
@[inline] def mapTcbAtCodeObjects (o : RHTable SeLe4n.ObjId KernelObject) (k : Nat)
    (g : TCB → TCB) : RHTable SeLe4n.ObjId KernelObject :=
  if k = 0 then o else o.mapValueAt (decode k).toObjId (KernelObject.mapTcb g)

/-- `runUnlinkLinks`'s five TCB writes, on the object table alone. -/
def unlinkLinkObjects (o : RHTable SeLe4n.ObjId KernelObject) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) : RHTable SeLe4n.ObjId KernelObject :=
  let o1 := mapTcbAtCodeObjects o pv (fun y => { y with runNextCode := nx })
  let o2 := mapTcbAtCodeObjects o1 nx (fun y => { y with runPrevCode := pv })
  let o3 := mapTcbAtCodeObjects o2 bpv (fun y => { y with runBucketNextCode := bnx })
  let o4 := mapTcbAtCodeObjects o3 bnx (fun y => { y with runBucketPrevCode := bpv })
  o4.mapValueAt t.toObjId (KernelObject.mapTcb TCB.detachRun)

/-- WS-ZA ZA4.5: the compiled `runUnlinkLinks`: the state record is rebuilt
once around the table writes (`runAppendLinksImpl`). -/
def runUnlinkLinksImpl (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    SystemState :=
  { st with objects := unlinkLinkObjects st.objects t pv nx bpv bnx }

@[csimp] theorem runUnlinkLinks_eq_impl : @runUnlinkLinks = @runUnlinkLinksImpl := by
  funext st t pv nx bpv bnx
  unfold runUnlinkLinks runUnlinkLinksImpl unlinkLinkObjects mapTcbAtCodeObjects
    updateTcbAtCode mapTcbInPlace
  dsimp only
  split <;> split <;> split <;> split <;> rfl

theorem runUnlinkLinks_scheduler (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    (st.runUnlinkLinks t pv nx bpv bnx).scheduler = st.scheduler := by
  simp only [runUnlinkLinks, updateTcbAtCode_scheduler, mapTcbInPlace_scheduler]

theorem runUnlinkLinks_objects_invExt (st : SystemState) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) (hInv : st.objects.invExt) :
    (st.runUnlinkLinks t pv nx bpv bnx).objects.invExt :=
  mapTcbInPlace_objects_invExt _ _ _ (updateTcbAtCode_objects_invExt _ _ _
    (updateTcbAtCode_objects_invExt _ _ _ (updateTcbAtCode_objects_invExt _ _ _
      (updateTcbAtCode_objects_invExt _ _ _ hInv))))

theorem runUnlinkLinks_runLinkOn (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat)
    (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.runUnlinkLinks t pv nx bpv bnx).runLinkOn c y =
      if y = t then RunQueue.RunQueueLink.none else
      let L1 := if code y = pv then RunQueueLink.withNextIfQueued nx (st.runLinkOn c y)
        else st.runLinkOn c y
      let L2 := if code y = nx then RunQueueLink.withPrevIfQueued pv L1 else L1
      let L3 := if code y = bpv then RunQueueLink.withBucketNextIfQueued bnx L2 else L2
      if code y = bnx then RunQueueLink.withBucketPrevIfQueued bpv L3 else L3 := by
  unfold runUnlinkLinks
  rw [runLinkOn_mapTcbInPlace_map _ _ _ c (fun _ => RunQueue.RunQueueLink.none)
      (fun tcb => TCB.runLinkOn_detachRun tcb c) rfl,
    runLinkOn_updateTcbAtCode_map _ _ _ c _ (fun tcb => TCB.runLinkOn_setBucketPrev tcb _ c)
      (RunQueueLink.withBucketPrevIfQueued_none _),
    runLinkOn_updateTcbAtCode_map _ _ _ c _ (fun tcb => TCB.runLinkOn_setBucketNext tcb _ c)
      (RunQueueLink.withBucketNextIfQueued_none _),
    runLinkOn_updateTcbAtCode_map _ _ _ c _ (fun tcb => TCB.runLinkOn_setPrev tcb _ c)
      (RunQueueLink.withPrevIfQueued_none _),
    runLinkOn_updateTcbAtCode_map _ _ _ c _ (fun tcb => TCB.runLinkOn_setNext tcb _ c)
      (RunQueueLink.withNextIfQueued_none _)]

/-- The ends of a queue once the thread with links `pv`, `nx`, `bpv`, `bnx` at
priority `p` leaves it; `walkMax` is the highest priority code left, read only
when the leaving thread was alone at the highest priority.  As `RunQueue.remove`. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.unlink (e : RunQueueEnds) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) (walkMax : Nat → Nat → Nat) : RunQueueEnds :=
  let head' := if pv = 0 then nx else e.head
  { buckets := RunQueue.setEnds e.buckets p (RunQueue.unlinkEnds bpv bnx)
    head := head'
    tail := if nx = 0 then pv else e.tail
    size := e.size - 1
    maxCode := if bpv = 0 ∧ bnx = 0 ∧ e.maxCode = p.val + 1 then walkMax (e.size - 1) head'
      else e.maxCode }

/-- WS-ZA ZA4.5: dequeue `t` from core `c` — `RunQueue.remove` on the core's
queue, written through the threads; a thread not queued there is left alone. -/
def runRemoveOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : SystemState :=
  let L := st.runLinkOn c t
  let st' := if L.queued then
      let st5 := st.runUnlinkLinks t L.prev L.next L.bucketPrev L.bucketNext
      let e' := (st5.scheduler.runQueueEndsOnCore c).unlink L.prev L.next L.bucketPrev
        L.bucketNext L.prio (fun n h => RunQueue.maxPrioCodeWalkBy (st5.runLinkOn c) n h 0)
      { st5 with scheduler := st5.scheduler.setRunQueueEndsOnCore c e' }
    else st
  let rq := (st'.scheduler.runQueueOnCore c).remove t
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

/-- WS-ZA ZA4.5: `maxPrioCodeWalkBy (st.runLinkOn c)` as compiled: each thread's
priority and successor read straight off its TCB, with no link record built
(`runMaxCodeWalk_eq`). -/
def runMaxCodeWalk (st : SystemState) (c : CoreId) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | n + 1, k + 1, acc =>
      match st.getTcb? ⟨k⟩ with
      | some tcb =>
          if tcb.runCoreCode = c.val + 1 then
            runMaxCodeWalk st c n tcb.runNextCode (max (tcb.runPrio.val + 1) acc)
          else runMaxCodeWalk st c n 0 (max 1 acc)
      | none => runMaxCodeWalk st c n 0 (max 1 acc)

theorem runMaxCodeWalk_eq (st : SystemState) (c : CoreId) (n k acc : Nat) :
    st.runMaxCodeWalk c n k acc = RunQueue.maxPrioCodeWalkBy (st.runLinkOn c) n k acc := by
  induction n generalizing k acc with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [runMaxCodeWalk, RunQueue.maxPrioCodeWalkBy, runLinkOn, TCB.runLinkOn, TCB.runLink]
      split
      · split <;> simp [ih, RunQueue.RunQueueLink.none]
      · simp [ih, RunQueue.RunQueueLink.none]

/-- The ends of a queue once the thread with links `pv`, `nx`, `bpv`, `bnx` at
priority `p` leaves it, with the highest priority code left, `mx`, already
read: `RunQueueEnds.unlink` with its scan run beforehand.  Taken apart first,
as `RunQueueEnds.appendImpl`, so exclusively owned ends are rewritten in place. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.unlinkTo (e : RunQueueEnds) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) (mx : Nat) : RunQueueEnds :=
  match e with
  | ⟨b, h, tl, s, _⟩ =>
    ⟨RunQueue.setEnds b p (RunQueue.unlinkEnds bpv bnx), if pv = 0 then nx else h,
      if nx = 0 then pv else tl, s - 1, mx⟩

/-- The highest priority code left on core `c` once the thread with links
`pv`, `nx`, `bpv`, `bnx` at priority `p` has been unlinked from the threads in
`st` (its ends not yet written): `RunQueueEnds.unlink`'s `maxCode`.  A call of
its own, so the scan's reads of `st` end before the caller rewrites `st`. -/
def runUnlinkMaxCode (st : SystemState) (c : CoreId) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) : Nat :=
  let e0 := st.scheduler.runQueueEndsOnCore c
  let head' := if pv = 0 then nx else e0.head
  if bpv = 0 ∧ bnx = 0 ∧ e0.maxCode = p.val + 1 then
    st.runMaxCodeWalk c (e0.size - 1) head' 0 else e0.maxCode

/-- Core `c`'s ends once the thread with links `pv`, `nx`, `bpv`, `bnx` at
priority `p` leaves, with the highest priority code left, `mx`, read
beforehand, rewritten in their slot.  Taking `mx` as an argument orders the scan
(`runUnlinkMaxCode`) before the state is taken apart, so an exclusive state is
rewritten in place. -/
@[noinline] def runUnlinkEndsAt (st : SystemState) (c : CoreId) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) (mx : Nat) : SystemState :=
  { st with scheduler := st.scheduler.modifyRunQueueEndsOnCore c (·.unlinkTo pv nx bpv bnx p mx) }

/-- WS-ZA ZA4.5: the compiled `runRemoveOnCore`.  The leaving thread's links are
read off its TCB as fields, the highest-priority scan (`runMaxCodeWalk`) runs
before the core's ends are taken out of their slot, and the ends are rewritten
there (`modifyRunQueueEndsOnCore`): no link record, closure or state copy. -/
def runRemoveOnCoreImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) : SystemState :=
  let st' := match st.getTcb? t with
    | some tcb =>
      if tcb.runCoreCode = c.val + 1 then
        let pv := tcb.runPrevCode
        let nx := tcb.runNextCode
        let bpv := tcb.runBucketPrevCode
        let bnx := tcb.runBucketNextCode
        let p := tcb.runPrio
        let st5 := st.runUnlinkLinks t pv nx bpv bnx
        st5.runUnlinkEndsAt c pv nx bpv bnx p (st5.runUnlinkMaxCode c pv nx bpv bnx p)
      else st
    | none => st
  let rq := (st'.scheduler.runQueueOnCore c).remove t
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

@[csimp] theorem runRemoveOnCore_eq_impl : @runRemoveOnCore = @runRemoveOnCoreImpl := by
  funext st c t
  unfold runRemoveOnCore runRemoveOnCoreImpl
  unfold runLinkOn
  cases st.getTcb? t with
  | none => rfl
  | some tcb =>
    dsimp only
    unfold TCB.runLinkOn
    split
    · simp only [TCB.runLink, if_true, runUnlinkMaxCode, runUnlinkEndsAt,
        SchedulerState.modifyRunQueueEndsOnCore_eq]
      generalize (st.runUnlinkLinks t _ _ _ _).scheduler.runQueueEndsOnCore c = e
      cases e
      simp only [RunQueueEnds.unlink, RunQueueEnds.unlinkTo, runMaxCodeWalk_eq]
      split <;> rfl
    · rfl

/-- WS-ZA ZA4.5: dequeueing keeps every core's queue in agreement with the
threads. -/
theorem runRemoveOnCore_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (hR : st.runQueueRefined) :
    (st.runRemoveOnCore c t).runQueueRefined := by
  unfold runRemoveOnCore
  by_cases hq : (st.runLinkOn c t).queued = true
  rotate_left
  · have hc : (st.scheduler.runQueueOnCore c).contains t = false := by
      rw [← (hR c).contains]; simpa using hq
    simp only [hq, if_false, Bool.false_eq_true]
    rw [RunQueue.remove_of_not_mem _ _ (by simp [Membership.mem, hc]),
      SchedulerState.setRunQueueOnCore_runQueueOnCore]
    exact hR
  · simp only [hq, if_true]
    have hc : (st.scheduler.runQueueOnCore c).contains t = true := by
      rw [← (hR c).contains]; exact hq
    have hL : st.runLinkOn c t = RunQueue.linkOf (st.scheduler.runQueueOnCore c).links t :=
      (hR c).link_of_mem (((st.scheduler.runQueueOnCore c).mem_toList_iff_mem t).mpr hc)
    rw [hL]
    obtain ⟨⟨c1, c2, c3, c4⟩, hnb⟩ := (st.scheduler.runQueueOnCore c).own_links hc
    obtain ⟨hLk, hBk, hHd, hTl, hSz, hMx⟩ := (st.scheduler.runQueueOnCore c).remove_fields hc
    generalize hrq : st.scheduler.runQueueOnCore c = rq at *
    generalize hx : RunQueue.linkOf rq.links t = x at *

    -- the links of core `c`'s queue after the dequeue
    have hlinks : ∀ y, (st.runUnlinkLinks t x.prev x.next x.bucketPrev x.bucketNext).runLinkOn c y =
        (rq.remove t).queuedLink y := by
      intro y
      rw [runUnlinkLinks_runLinkOn _ _ _ _ _ _, RunQueue.queuedLink, hLk,
        RunQueue.linkOf_unlinkLinks rq.links_invExtK t _ _ _ _ c1 c2 c3 c4 y]
      by_cases hy : y = t
      · subst hy; simp
      · simp only [hy, if_false]
        have hRy := (hR c).2 y
        rw [hrq] at hRy
        rw [hRy, RunQueue.queuedLink]
        generalize RunQueue.linkOf rq.links y = Ly
        cases Ly with
        | mk pr q lp ln lbp lbn =>
          cases q
          · simp
          · simp only [RunQueueLink.withNextIfQueued, RunQueueLink.withPrevIfQueued,
              RunQueueLink.withBucketNextIfQueued, RunQueueLink.withBucketPrevIfQueued, if_true]
            by_cases e1 : code y = x.prev <;> by_cases e2 : code y = x.next <;>
              by_cases e3 : code y = x.bucketPrev <;> by_cases e4 : code y = x.bucketNext <;>
              simp (disch := first | assumption | rfl) only [if_pos, if_neg, if_true]
    intro c'
    refine ⟨?_, fun y => ?_⟩
    · rw [SchedulerState.setRunQueueOnCore_runQueueEndsOnCore]
      by_cases h : c' = c
      · subst h
        rw [SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_self,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
          SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runUnlinkLinks_scheduler, hrq,
          (hR c').1, hrq]
        unfold RunQueueEnds.unlink RunQueue.ends
        simp only [hBk, hHd, hTl, hSz, hMx]
        congr 1
        split
        · rw [← hSz, ← hHd, RunQueue.maxPrioCodeWalkBy_eq, RunQueue.walk_of_agree _ hlinks,
            RunQueue.maxPrioCode_of_agree _ hlinks, Nat.zero_max, hMx, hSz, hHd, if_pos (by assumption)]
        · rfl
      · rw [SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_ne _ _ _ _ (Ne.symm h),
          SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm h),
          SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runUnlinkLinks_scheduler]
        exact (hR c').1
    · rw [runLinkOn_withScheduler, runLinkOn_withScheduler]
      by_cases h : c' = c
      · subst h
        rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
          SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runUnlinkLinks_scheduler, hrq]
        exact hlinks y
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm h),
          SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runUnlinkLinks_scheduler,
          ← (hR c').2 y, runUnlinkLinks_runLinkOn _ _ _ _ _ _]
        have hoff : ∀ {z : SeLe4n.ThreadId}, rq.contains z = true →
            (st.runLinkOn c' z).queued = false := by
          intro z hz
          have hq1 : (st.runLinkOn c z).queued = true := by rw [(hR c).contains, hrq]; exact hz
          cases hq2 : (st.runLinkOn c' z).queued
          · rfl
          · exact absurd (runLinkOn_queued_unique hq1 hq2).symm h
        by_cases hy : y = t
        · subst hy; rw [if_pos rfl, runLinkOn_eq_none_of_not_queued (hoff hc)]
        · rw [if_neg hy]
          have hz := hoff (z := y)
          by_cases e : code y = x.prev ∨ code y = x.next ∨ code y = x.bucketPrev ∨ code y = x.bucketNext
          · have hq0 := hz (hnb y e)
            simp only [RunQueueLink.withNextIfQueued_of_not_queued hq0,
              RunQueueLink.withPrevIfQueued_of_not_queued hq0,
              RunQueueLink.withBucketNextIfQueued_of_not_queued hq0,
              RunQueueLink.withBucketPrevIfQueued_of_not_queued hq0, ite_self]
          · simp only [not_or] at e
            simp only [if_neg e.1, if_neg e.2.1, if_neg e.2.2.1, if_neg e.2.2.2]

theorem runRemoveOnCore_runQueueOnCore_self (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).scheduler.runQueueOnCore c = (st.scheduler.runQueueOnCore c).remove t := by
  unfold runRemoveOnCore
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  split
  · rw [SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runUnlinkLinks_scheduler]
  · rfl

theorem runRemoveOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (h : c ≠ c') :
    (st.runRemoveOnCore c t).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runRemoveOnCore
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
  split
  · rw [SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runUnlinkLinks_scheduler]
  · rfl

theorem updateTcbAtCode_getTcb?_isSome (st : SystemState) (k : Nat) (g : TCB → TCB)
    (t : SeLe4n.ThreadId) :
    ((st.updateTcbAtCode k g).getTcb? t).isSome = (st.getTcb? t).isSome := by
  unfold updateTcbAtCode
  split
  · rfl
  · by_cases h : decode k = t
    · subst h; rw [mapTcbInPlace_getTcb?_self _ _ _]; cases st.getTcb? (decode k) <;> rfl
    · rw [mapTcbInPlace_getTcb?_ne _ _ _ _
        (fun e => h (SeLe4n.ThreadId.toObjId_injective _ _ e))]

theorem runUnlinkLinks_getTcb?_isSome (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat)
    (y : SeLe4n.ThreadId) :
    ((st.runUnlinkLinks t pv nx bpv bnx).getTcb? y).isSome = (st.getTcb? y).isSome := by
  unfold runUnlinkLinks
  rw [mapTcbInPlace_getTcb?_isSome, updateTcbAtCode_getTcb?_isSome,
    updateTcbAtCode_getTcb?_isSome, updateTcbAtCode_getTcb?_isSome,
    updateTcbAtCode_getTcb?_isSome _ _ _]

theorem runRemoveOnCore_objects (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).objects =
      if (st.runLinkOn c t).queued then
        (st.runUnlinkLinks t (st.runLinkOn c t).prev (st.runLinkOn c t).next
          (st.runLinkOn c t).bucketPrev (st.runLinkOn c t).bucketNext).objects
      else st.objects := by
  unfold runRemoveOnCore; dsimp only; split <;> rfl

/-- The unlink moves no core code but `t`'s. -/
theorem runUnlinkLinks_runCoreCode_ne (st : SystemState) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) (y : SeLe4n.ThreadId) (hy : y ≠ t) :
    ((st.runUnlinkLinks t pv nx bpv bnx).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  have h1 := updateTcbAtCode_runCoreCode st pv (fun y => { y with runNextCode := nx }) (fun _ => rfl) y
  have h2 := updateTcbAtCode_runCoreCode (st.updateTcbAtCode pv (fun y => { y with runNextCode := nx }))
    nx (fun y => { y with runPrevCode := pv }) (fun _ => rfl) y
  have h3 := updateTcbAtCode_runCoreCode ((st.updateTcbAtCode pv (fun y => { y with runNextCode := nx })).updateTcbAtCode
    nx (fun y => { y with runPrevCode := pv })) bpv (fun y => { y with runBucketNextCode := bnx }) (fun _ => rfl) y
  have h4 := updateTcbAtCode_runCoreCode (((st.updateTcbAtCode pv (fun y => { y with runNextCode := nx })).updateTcbAtCode
    nx (fun y => { y with runPrevCode := pv })).updateTcbAtCode bpv (fun y => { y with runBucketNextCode := bnx }))
    bnx (fun y => { y with runBucketPrevCode := bpv }) (fun _ => rfl) y
  have h5 := mapTcbInPlace_runCoreCode ((((st.updateTcbAtCode pv (fun y => { y with runNextCode := nx })).updateTcbAtCode
    nx (fun y => { y with runPrevCode := pv })).updateTcbAtCode bpv (fun y => { y with runBucketNextCode := bnx })).updateTcbAtCode
    bnx (fun y => { y with runBucketPrevCode := bpv })) t y TCB.detachRun
    (fun _ => Or.inr (Ne.symm hy))
  exact h5.trans (h4.trans (h3.trans (h2.trans h1)))

/-- A removal of `t` moves no other thread's core code. -/
theorem runRemoveOnCore_runCoreCode_ne (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (hy : y ≠ t) :
    ((st.runRemoveOnCore c t).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  by_cases hq : (st.runLinkOn c t).queued = true
  · have h := runRemoveOnCore_objects st c t
    rw [if_pos hq] at h
    rw [getTcb?_frame h]
    exact runUnlinkLinks_runCoreCode_ne _ _ _ _ _ _ y hy
  · have h := runRemoveOnCore_objects st c t
    rw [if_neg hq] at h
    rw [getTcb?_frame h]

theorem runRemoveOnCore_getTcb?_isSome (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    :
    ((st.runRemoveOnCore c t).getTcb? y).isSome = (st.getTcb? y).isSome := by
  by_cases hq : (st.runLinkOn c t).queued = true
  · have h := runRemoveOnCore_objects st c t
    rw [if_pos hq] at h
    rw [getTcb?_frame h, runUnlinkLinks_getTcb?_isSome _ _ _ _ _ _]
  · have h := runRemoveOnCore_objects st c t
    rw [if_neg hq] at h
    rw [getTcb?_frame h]

theorem runRemoveOnCore_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : (st.runRemoveOnCore c t).objects.invExt := by
  rw [runRemoveOnCore_objects]
  split
  · exact runUnlinkLinks_objects_invExt _ _ _ _ _ _ hInv
  · exact hInv

theorem RunQueueLink.queued_withNextIfQueued (v : Nat) (l : RunQueueLink) :
    (RunQueueLink.withNextIfQueued v l).queued = l.queued := by
  unfold RunQueueLink.withNextIfQueued; split <;> rfl
theorem RunQueueLink.queued_withPrevIfQueued (v : Nat) (l : RunQueueLink) :
    (RunQueueLink.withPrevIfQueued v l).queued = l.queued := by
  unfold RunQueueLink.withPrevIfQueued; split <;> rfl
theorem RunQueueLink.queued_withBucketNextIfQueued (v : Nat) (l : RunQueueLink) :
    (RunQueueLink.withBucketNextIfQueued v l).queued = l.queued := by
  unfold RunQueueLink.withBucketNextIfQueued; split <;> rfl
theorem RunQueueLink.queued_withBucketPrevIfQueued (v : Nat) (l : RunQueueLink) :
    (RunQueueLink.withBucketPrevIfQueued v l).queued = l.queued := by
  unfold RunQueueLink.withBucketPrevIfQueued; split <;> rfl

/-- Unlinking a thread takes it off every queue and moves no other thread on
or off one. -/
theorem runUnlinkLinks_queuedOn (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat)
    (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.runUnlinkLinks t pv nx bpv bnx).queuedOn c y = if y = t then false else st.queuedOn c y := by
  rw [queuedOn_eq_runLinkOn, runUnlinkLinks_runLinkOn, queuedOn_eq_runLinkOn]
  by_cases hy : y = t
  · rw [if_pos hy, if_pos hy]; rfl
  · rw [if_neg hy, if_neg hy]
    dsimp only
    simp only [apply_ite RunQueueLink.queued, RunQueueLink.queued_withBucketPrevIfQueued,
      RunQueueLink.queued_withBucketNextIfQueued, RunQueueLink.queued_withPrevIfQueued,
      RunQueueLink.queued_withNextIfQueued, ite_self]

/-- WS-ZA ZA4.5: dequeueing `t` from core `c` leaves it queued on `c` nowhere
and moves no other thread, and `t` on no other core, on or off a queue. -/
theorem runRemoveOnCore_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).queuedOn c' y =
      if y = t ∧ c' = c then false else st.queuedOn c' y := by
  have hO := runRemoveOnCore_objects st c t
  rw [show (st.runRemoveOnCore c t).queuedOn c' y =
      (if (st.runLinkOn c t).queued then
        (st.runUnlinkLinks t (st.runLinkOn c t).prev (st.runLinkOn c t).next
          (st.runLinkOn c t).bucketPrev (st.runLinkOn c t).bucketNext).queuedOn c' y
       else st.queuedOn c' y) from by
    split
    · next hq => rw [if_pos hq] at hO; exact (RunCoresAgree.of_objects hO).queuedOn c' y
    · next hq => rw [if_neg hq] at hO; exact (RunCoresAgree.of_objects hO).queuedOn c' y]
  split
  · next hq =>
    rw [runUnlinkLinks_queuedOn]
    by_cases hy : y = t
    · subst hy
      rw [if_pos rfl]
      by_cases hc : c' = c
      · rw [if_pos ⟨rfl, hc⟩]
      · rw [if_neg (fun h => hc h.2)]
        symm
        cases hq' : st.queuedOn c' y with
        | false => rfl
        | true =>
          exact absurd (runLinkOn_queued_unique hq ((queuedOn_eq_runLinkOn st c' y) ▸ hq'))
            (fun h => hc h.symm)
    · rw [if_neg hy, if_neg (fun h => hy h.1)]
  · next hq =>
    split
    · next h =>
      obtain ⟨rfl, rfl⟩ := h
      rw [queuedOn_eq_runLinkOn]; simpa using hq
    · rfl

-- ============================================================================
-- The current threads are off the run queues and current on one core each
-- ============================================================================

/-- Closes `TCB.StateMono f` for a record update that leaves both state fields
alone, or that only marks the thread ready or active. -/
macro "tcb_state_mono" : tactic => `(tactic| first
  | (intro _; exact ⟨id, id, rfl⟩)
  | (intro _; exact ⟨fun _ => rfl, id, rfl⟩)
  | (intro _; exact ⟨id, fun _ => by simp [TCB.Active], rfl⟩)
  | (intro _; exact ⟨fun _ => rfl, fun _ => by simp [TCB.Active], rfl⟩))

/-- Closes `st'.scheduler.currentCode = st.scheduler.currentCode` for a step that
leaves the current slots alone: by definition, or from a hypothesis that
equates the whole scheduler (or its `current` field) with the old one. -/
macro "current_frame" : tactic =>
  `(tactic| first
    | rfl
    | exact congrArg SchedulerState.currentCode (by assumption)
    | (rw [‹SystemState.scheduler _ = _›]))

/-- Closes `st'.referenceTables = st.referenceTables` for a step that writes none
of the three tables that name objects by id: by definition, or by rewriting
with the hypotheses that describe the step. -/
macro "table_frame" : tactic =>
  `(tactic| first
    | rfl
    | (simp_all only [SystemState.referenceTables]; done))

/-- Closes `st'.scheduler.releaseSlots = st.scheduler.releaseSlots` for a step
that writes no release-queue slot: by definition, or from a hypothesis that
equates the whole scheduler with the old one. -/
macro "release_frame" : tactic =>
  `(tactic| first
    | rfl
    | exact congrArg SchedulerState.releaseSlots (by assumption)
    | (rw [‹SystemState.scheduler _ = _›])
    | (simp_all only [SchedulerState.releaseSlots]; done)
    | (simp only [SchedulerState.releaseSlots]; split <;> rfl)
    | (simp only [SchedulerState.releaseSlots]; split <;> (split <;> rfl)))

/-- WS-ZA ZA6.8: closes `st'.machine.residentCode = st.machine.residentCode`
for a step that sets no core's resident thread: by definition, or from a
hypothesis that equates the whole machine with the old one. -/
macro "resident_frame" : tactic =>
  `(tactic| first
    | rfl
    | exact congrArg MachineState.residentCode (by assumption)
    | (rw [‹SystemState.machine _ = _›])
    | (simp only [SystemState.updateTcb_machine, SystemState.rewriteObject_machine,
        SystemState.updateSchedContext_machine]; done)
    | (simp; done)
    | (simp_all only [SystemState.machine]; done))

/-- Closes `obj.tableBackLinks = objTableBackLinks st.objects[k]?` for a store
that keeps the slot's table back-links: an object holding none over an object
holding none, or an object over the one it was updated from. -/
macro "table_backlinks" : tactic =>
  `(tactic| first
    | rfl
    | (simp only [objTableBackLinks_some, KernelObject.tableBackLinks]; done)
    | (rw [(getTcb?_eq_some_iff _ _ _).mp ‹SystemState.getTcb? _ _ = some _›]; rfl)
    | (rw [(getSchedContext?_eq_some_iff _ _ _).mp
        ‹SystemState.getSchedContext? _ _ = some _›]; rfl)
    | (rw [(getReply?_eq_some_iff _ _ _).mp ‹SystemState.getReply? _ _ = some _›]; rfl)
    | (rw [(getCNode?_eq_some_iff _ _ _).mp ‹SystemState.getCNode? _ _ = some _›]; rfl)
    | (rw [(getUntyped?_eq_some_iff _ _ _).mp ‹SystemState.getUntyped? _ _ = some _›]; rfl)
    | (simp_all only [objTableBackLinks_some, objTableBackLinks_none,
        KernelObject.tableBackLinks]; done)
    | (simp_all only [objTableBackLinks_some, objTableBackLinks_none,
        KernelObject.tableBackLinks, TCB.setSpaceLinkWords_taintWords]; done))

/-- Closes `∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c`
for a store that keeps the slot's release links: an object no context is over
one no context is, or a context over the one it was updated from. -/
macro "release_links" : tactic =>
  `(tactic| first
    | (intro _; rfl)
    | (intro _; rw [(getTcb?_eq_some_iff _ _ _).mp ‹SystemState.getTcb? _ _ = some _›]; rfl)
    | (intro _; rw [(getSchedContext?_eq_some_iff _ _ _).mp
        ‹SystemState.getSchedContext? _ _ = some _›]; rfl)
    | (intro _; rw [(getReply?_eq_some_iff _ _ _).mp ‹SystemState.getReply? _ _ = some _›]; rfl)
    | (intro _; rw [(getCNode?_eq_some_iff _ _ _).mp ‹SystemState.getCNode? _ _ = some _›]; rfl)
    | (intro _; rw [(getUntyped?_eq_some_iff _ _ _).mp ‹SystemState.getUntyped? _ _ = some _›]; rfl)
    | (intro _; simp_all only [objReleaseLinkOn]; done))

/-- Closes `objRefillView (some obj) = objRefillView st.objects[k]?` for a store
that keeps the slot's refill view (WS-ZA ZA6.4): an object that is no context
over one that is none, or a context over the one it was updated from with its
budget, period, refills and binding kept. -/
macro "refill_view" : tactic =>
  `(tactic| first
    | rfl
    | (rw [(getTcb?_eq_some_iff _ _ _).mp ‹SystemState.getTcb? _ _ = some _›]; rfl)
    | (rw [(getSchedContext?_eq_some_iff _ _ _).mp
        ‹SystemState.getSchedContext? _ _ = some _›]; rfl)
    | (rw [(getReply?_eq_some_iff _ _ _).mp ‹SystemState.getReply? _ _ = some _›]; rfl)
    | (rw [(getCNode?_eq_some_iff _ _ _).mp ‹SystemState.getCNode? _ _ = some _›]; rfl)
    | (rw [(getUntyped?_eq_some_iff _ _ _).mp ‹SystemState.getUntyped? _ _ = some _›]; rfl)
    | (simp_all only [objRefillView]; done))

/-- Closes `objYieldCodes (some obj) = objYieldCodes st.objects[k]?` for a store
that keeps the slot's yield codes (WS-ZA ZA6.6): an object holding no link end
over one holding none, or a thread or context over the one it was updated from
with its yield code kept. -/
macro "yield_codes" : tactic =>
  `(tactic| first
    | rfl
    | (rw [(getTcb?_eq_some_iff _ _ _).mp ‹SystemState.getTcb? _ _ = some _›]; rfl)
    | (rw [(getSchedContext?_eq_some_iff _ _ _).mp
        ‹SystemState.getSchedContext? _ _ = some _›]; rfl)
    | (rw [(getReply?_eq_some_iff _ _ _).mp ‹SystemState.getReply? _ _ = some _›]; rfl)
    | (rw [(getCNode?_eq_some_iff _ _ _).mp ‹SystemState.getCNode? _ _ = some _›]; rfl)
    | (rw [(getUntyped?_eq_some_iff _ _ _).mp ‹SystemState.getUntyped? _ _ = some _›]; rfl)
    | (simp_all only [objYieldCodes]; done)
    | (simp_all only [objYieldCodes]; rfl)
    | (simp_all [objYieldCodes]; done))

/-- `t` is a thread a core may run: its TCB is ready in IPC and not suspended
(seL4's `st_tcb_at runnable`). -/
def runnable (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∃ tcb, st.getTcb? t = some tcb ∧ tcb.Runnable

/-- `t`'s TCB, if it has one, has coherent state fields (`TCB.Coherent`). -/
def coherentAt (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ tcb, st.getTcb? t = some tcb → tcb.Coherent

/-- `t` has a TCB that is not suspended. -/
def activeAt (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∃ tcb, st.getTcb? t = some tcb ∧ tcb.Active

/-- A runnable thread is active. -/
theorem runnable.activeAt {st : SystemState} {t : SeLe4n.ThreadId} (h : st.runnable t) :
    st.activeAt t :=
  let ⟨x, hx, hr⟩ := h; ⟨x, hx, hr.2⟩

/-- An active thread's TCB is coherent. -/
theorem activeAt.coherentAt {st : SystemState} {t : SeLe4n.ThreadId} (h : st.activeAt t) :
    st.coherentAt t := fun y hy => by
  obtain ⟨x, hx, ha⟩ := h
  rw [hx] at hy; cases hy; exact .inr ha

/-- `t`'s TCB, if it has one, is homed on core `c`: its affinity, with an
unpinned thread homed on the boot core (`determineTargetCore`'s reading). -/
def homedOn (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId) : Prop :=
  ∀ x, st.getTcb? t = some x → x.cpuAffinity.getD Concurrency.bootCoreId = c

/-- A step that keeps every runnable thread runnable, every coherent TCB
coherent and every active thread active, and every active thread on its
affinity: what every step but a block, a suspend or an affinity change does to
the state fields. -/
def StateMono (st st' : SystemState) : Prop :=
  ∀ t, (st.runnable t → st'.runnable t) ∧ (st.coherentAt t → st'.coherentAt t) ∧
    (st.activeAt t → st'.activeAt t) ∧
    (st.activeAt t → ∀ x x', st.getTcb? t = some x → st'.getTcb? t = some x' →
      x'.cpuAffinity = x.cpuAffinity)

theorem StateMono.runnable {st st' : SystemState} (h : StateMono st st') {t : SeLe4n.ThreadId}
    (hr : st.runnable t) : st'.runnable t := (h t).1 hr

theorem StateMono.coherentAt {st st' : SystemState} (h : StateMono st st') {t : SeLe4n.ThreadId}
    (hc : st.coherentAt t) : st'.coherentAt t := (h t).2.1 hc

theorem StateMono.activeAt {st st' : SystemState} (h : StateMono st st') {t : SeLe4n.ThreadId}
    (ha : st.activeAt t) : st'.activeAt t := (h t).2.2.1 ha

/-- An active thread's kept TCB keeps its affinity. -/
theorem StateMono.affinity {st st' : SystemState} (h : StateMono st st') {t : SeLe4n.ThreadId}
    (ha : st.activeAt t) {x x' : TCB} (hx : st.getTcb? t = some x)
    (hx' : st'.getTcb? t = some x') : x'.cpuAffinity = x.cpuAffinity :=
  (h t).2.2.2 ha x x' hx hx'

/-- An active thread stays homed where it was. -/
theorem StateMono.homedOn {st st' : SystemState} (h : StateMono st st') {t : SeLe4n.ThreadId}
    {c : CoreId} (ha : st.activeAt t) (hh : st.homedOn t c) : st'.homedOn t c := fun x' hx' => by
  obtain ⟨x, hx, hA⟩ := ha
  rw [h.affinity ⟨x, hx, hA⟩ hx hx']; exact hh x hx

theorem StateMono.refl (st : SystemState) : StateMono st st :=
  fun _ => ⟨id, id, id, fun _ _ _ h h' => by rw [h] at h'; cases h'; rfl⟩

theorem StateMono.trans {st st' st'' : SystemState} (h1 : StateMono st st')
    (h2 : StateMono st' st'') : StateMono st st'' :=
  fun t => ⟨fun h => h2.runnable (h1.runnable h), fun h => h2.coherentAt (h1.coherentAt h),
    fun h => h2.activeAt (h1.activeAt h), fun ha x x'' hx hx'' => by
      obtain ⟨x', hx', hA'⟩ := h1.activeAt ha
      rw [h2.affinity ⟨x', hx', hA'⟩ hx' hx'', h1.affinity ha hx hx']⟩

/-- A step is state-monotone when, thread by thread, a TCB it keeps is
replaced by a monotone step of it and a TCB it creates is coherent. -/
theorem StateMono.of_pointwise {st st' : SystemState}
    (h1 : ∀ t x, st.getTcb? t = some x → ∃ x', st'.getTcb? t = some x' ∧ x.StepMono x')
    (h2 : ∀ t x', st'.getTcb? t = some x' → (∀ x, st.getTcb? t = some x → x.Coherent) →
      x'.Coherent) : StateMono st st' := fun t =>
  ⟨fun ⟨x, hx, hr⟩ => let ⟨x', hx', hm⟩ := h1 t x hx; ⟨x', hx', hm.runnable hr⟩,
    fun hc x' hx' => h2 t x' hx' hc,
    fun ⟨x, hx, ha⟩ => let ⟨x', hx', hm⟩ := h1 t x hx; ⟨x', hx', hm.2.1 ha⟩,
    fun _ x y hx hy => by
      obtain ⟨x', hx', hm⟩ := h1 t x hx
      rw [hy] at hx'; cases hx'; exact hm.2.2⟩

/-- **A step that may also erase suspended threads is state-monotone**: a TCB
it keeps is replaced by a monotone step of it, or the TCB is gone and was not
active, so neither runnable nor active before. -/
theorem StateMono.of_pointwise_erase {st st' : SystemState}
    (h1 : ∀ t x, st.getTcb? t = some x →
      (∃ x', st'.getTcb? t = some x' ∧ x.StepMono x') ∨ (st'.getTcb? t = none ∧ ¬ x.Active))
    (h2 : ∀ t x', st'.getTcb? t = some x' → (∀ x, st.getTcb? t = some x → x.Coherent) →
      x'.Coherent) : StateMono st st' := fun t =>
  ⟨fun ⟨x, hx, hr⟩ => by
      rcases h1 t x hx with ⟨x', hx', hm⟩ | ⟨-, hA⟩
      · exact ⟨x', hx', hm.runnable hr⟩
      · exact absurd hr.2 hA,
    fun hc x' hx' => h2 t x' hx' hc,
    fun ⟨x, hx, ha⟩ => by
      rcases h1 t x hx with ⟨x', hx', hm⟩ | ⟨-, hA⟩
      · exact ⟨x', hx', hm.2.1 ha⟩
      · exact absurd ha hA,
    fun _ x y hx hy => by
      rcases h1 t x hx with ⟨x', hx', hm⟩ | ⟨hn, -⟩
      · rw [hy] at hx'; cases hx'; exact hm.2.2
      · rw [hy] at hn; cases hn⟩

/-- The same, read off a step that rewrites every TCB through a monotone map
and adds or removes none. -/
theorem StateMono.of_map {st st' : SystemState} {f : SeLe4n.ThreadId → TCB → TCB}
    (h : ∀ t, st'.getTcb? t = (st.getTcb? t).map (f t)) (hm : ∀ t, TCB.StateMono (f t)) :
    StateMono st st' :=
  StateMono.of_pointwise (fun t x hx => ⟨f t x, by rw [h, hx]; rfl, hm t x⟩)
    (fun t x' hx' hc => by
      rw [h] at hx'
      cases hT : st.getTcb? t with
      | none => rw [hT] at hx'; cases hx'
      | some x => rw [hT] at hx'; cases hx'; exact (hm t x).coherent (hc x hT))

/-- A step that keeps every thread's TCB keeps the state fields. -/
theorem StateMono.of_getTcb {st st' : SystemState} (h : ∀ t, st'.getTcb? t = st.getTcb? t) :
    StateMono st st' :=
  StateMono.of_map (f := fun _ x => x) (fun t => by rw [h]; cases st.getTcb? t <;> rfl)
    (fun _ _ => ⟨id, id, rfl⟩)

/-- A step that keeps every TCB's two state fields and its affinity keeps them
monotone. -/
theorem StateMono.of_stateFields {st st' : SystemState}
    (h : ∀ t, (st'.getTcb? t).map (fun x => (x.ipcState, x.threadState, x.cpuAffinity)) =
      (st.getTcb? t).map (fun x => (x.ipcState, x.threadState, x.cpuAffinity))) :
    StateMono st st' := by
  have hs : ∀ x x' : TCB, x'.ipcState = x.ipcState → x'.threadState = x.threadState →
      x'.cpuAffinity = x.cpuAffinity → x.StepMono x' := fun x x' e1 e2 e3 =>
    ⟨fun h => e1.trans h, fun h => by unfold TCB.Active; rw [e2]; exact h, e3⟩
  refine StateMono.of_pointwise (fun t x hx => ?_) (fun t x' hx' hc => ?_)
  · have ht := h t
    rw [hx] at ht
    cases hT : st'.getTcb? t with
    | none => rw [hT] at ht; cases ht
    | some x' =>
      rw [hT] at ht
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
      exact ⟨x', rfl, hs x x' ht.1 ht.2.1 ht.2.2⟩
  · have ht := h t
    rw [hx'] at ht
    cases hT : st.getTcb? t with
    | none => rw [hT] at ht; cases ht
    | some x =>
      rw [hT] at ht
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
      exact (hs x x' ht.1 ht.2.1 ht.2.2).coherent (hc x hT)

/-- A step keeping every thread's two state fields keeps it runnable, coherent
and active — whatever it does to its affinity (the first three `StateMono`
clauses, which an affinity change keeps and the fourth it does not). -/
theorem stateFieldsKept_of_pair {st st' : SystemState}
    (h : ∀ t, (st'.getTcb? t).map (fun x => (x.ipcState, x.threadState)) =
      (st.getTcb? t).map (fun x => (x.ipcState, x.threadState))) (u : SeLe4n.ThreadId) :
    (st.runnable u → st'.runnable u) ∧ (st.coherentAt u → st'.coherentAt u) ∧
      (st.activeAt u → st'.activeAt u) := by
  have hu := h u
  refine ⟨fun ⟨x, hx, hr⟩ => ?_, fun hc x' hx' => ?_, fun ⟨x, hx, ha⟩ => ?_⟩
  · rw [hx] at hu
    cases hT : st'.getTcb? u with
    | none => rw [hT] at hu; cases hu
    | some x' =>
      rw [hT] at hu
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
      exact ⟨x', hT, by unfold TCB.Runnable at hr ⊢; rw [hu.1, hu.2]; exact hr⟩
  · rw [hx'] at hu
    cases hT : st.getTcb? u with
    | none => rw [hT] at hu; cases hu
    | some x =>
      rw [hT] at hu
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
      have := hc x hT
      unfold TCB.Coherent at this ⊢; rw [hu.1, hu.2]; exact this
  · rw [hx] at hu
    cases hT : st'.getTcb? u with
    | none => rw [hT] at hu; cases hu
    | some x' =>
      rw [hT] at hu
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
      exact ⟨x', hT, by unfold TCB.Active at ha ⊢; rw [hu.2]; exact ha⟩

theorem StateMono.of_objects {st st' : SystemState} (h : st'.objects = st.objects) :
    StateMono st st' :=
  StateMono.of_getTcb fun t => by unfold getTcb?; rw [h]

/-- A typed read-modify-write of one TCB through a state-monotone update. -/
theorem StateMono.updateTcb {st : SystemState} (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId)
    {f : TCB → TCB} (hm : TCB.StateMono f) : StateMono st (st.updateTcb tid f) := by
  classical
  refine StateMono.of_map (f := fun t => if tid.toObjId = t.toObjId then f else id)
    (fun t => ?_) (fun t => ?_)
  · dsimp only
    by_cases h : tid.toObjId = t.toObjId
    · have e1 : ∀ s : SystemState, s.getTcb? t = s.getTcb? tid := fun s => by
        unfold getTcb?; rw [h]
      rw [if_pos h, e1, e1, updateTcb_getTcb?_self _ _ _ hInv]
    · rw [if_neg h, updateTcb_getTcb?_ne _ _ _ hInv t h]
      cases st.getTcb? t <;> rfl
  · dsimp only
    split
    · exact hm
    · exact fun _ => ⟨id, id, rfl⟩

/-- The TCB an object slot holds, if any. -/
def objTcb? : Option KernelObject → Option TCB
  | some (.tcb t) => some t
  | _ => none

theorem getTcb?_eq_objTcb? (st : SystemState) (t : SeLe4n.ThreadId) :
    st.getTcb? t = objTcb? st.objects[t.toObjId]? := by
  unfold getTcb?
  cases h : st.objects[t.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- An object stored over a slot keeps the state fields monotone: a TCB is
replaced by a monotone step of it, and a TCB it stores is coherent whenever the
one it replaces was (or there was none). -/
def objStateMono (old : Option KernelObject) (new : KernelObject) : Prop :=
  (∀ x, objTcb? old = some x → ∃ x', objTcb? (some new) = some x' ∧ x.StepMono x') ∧
  (∀ x', objTcb? (some new) = some x' → (∀ x, objTcb? old = some x → x.Coherent) → x'.Coherent)

/-- A TCB stored over a TCB through a monotone step. -/
theorem objStateMono_tcb {x x' : TCB} (h : x.StepMono x') :
    objStateMono (some (.tcb x)) (.tcb x') :=
  ⟨fun y hy => by cases hy; exact ⟨x', rfl, h⟩,
    fun y hy hc => by cases hy; exact h.coherent (hc x rfl)⟩

/-- An object other than a TCB stored over an object other than a TCB. -/
theorem objStateMono_nonTcb {old : Option KernelObject} {new : KernelObject}
    (hOld : objTcb? old = none) (hNew : objTcb? (some new) = none) : objStateMono old new :=
  ⟨fun _ hy => (by rw [hOld] at hy; cases hy), fun _ hy _ => (by rw [hNew] at hy; cases hy)⟩

/-- Closes `objStateMono (some (.tcb old)) (.tcb new)` the same way. -/
macro "obj_state_mono" : tactic => `(tactic| first
  | exact objStateMono_tcb ⟨id, id, rfl⟩
  | exact objStateMono_tcb ⟨fun _ => rfl, id, rfl⟩
  | exact objStateMono_nonTcb rfl rfl)

/-- One object slot rewritten monotonely: the `objStateMono` relation with the
new slot possibly empty. -/
def slotStateMono (old new : Option KernelObject) : Prop :=
  (∀ x, objTcb? old = some x → ∃ x', objTcb? new = some x' ∧ x.StepMono x') ∧
  (∀ x', objTcb? new = some x' → (∀ x, objTcb? old = some x → x.Coherent) → x'.Coherent)

theorem slotStateMono.of_eq {old new : Option KernelObject} (h : new = old) :
    slotStateMono old new :=
  by subst h; exact ⟨fun x hx => ⟨x, hx, ⟨id, id, rfl⟩⟩, fun x' hx' hc => hc x' hx'⟩

theorem slotStateMono.of_obj {old new : Option KernelObject} {o : KernelObject}
    (h : new = some o) (hm : objStateMono old o) : slotStateMono old new := by
  subst h; exact hm

/-- A step that rewrites every object slot monotonely keeps the state fields
monotone. -/
theorem StateMono.of_slots {st st' : SystemState}
    (h : ∀ oid : SeLe4n.ObjId, slotStateMono st.objects[oid]? st'.objects[oid]?) :
    StateMono st st' :=
  StateMono.of_pointwise
    (fun t x hx => by rw [getTcb?_eq_objTcb?] at hx ⊢; exact (h _).1 x hx)
    (fun t x' hx' hc => by
      rw [getTcb?_eq_objTcb?] at hx'
      exact (h _).2 x' hx' fun x hx => hc x (by rw [getTcb?_eq_objTcb?]; exact hx))

theorem StateMono.insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k obj)
    (hm : objStateMono st.objects[k]? obj) : StateMono st st' := by
  have key : ∀ t, st'.getTcb? t =
      if k = t.toObjId then objTcb? (some obj) else st.getTcb? t := fun t => by
    rw [getTcb?_eq_objTcb?, getTcb?_eq_objTcb?, hO]
    simp only [RHTable_getElem?_eq_get?]
    split
    · rename_i hk; subst hk; rw [RHTable.getElem?_insert_self st.objects _ obj hInv]
    · rename_i hk
      rw [RHTable.getElem?_insert_ne st.objects _ _ obj (fun hb => hk (eq_of_beq hb)) hInv]
  have hold : ∀ t, k = t.toObjId → st.getTcb? t = objTcb? st.objects[k]? := fun t hk => by
    rw [getTcb?_eq_objTcb?, hk]
  refine StateMono.of_pointwise (fun t x hx => ?_) (fun t x' hx' hc => ?_)
  · rw [key]; split
    · rename_i hk; exact hm.1 x (by rw [← hold t hk]; exact hx)
    · exact ⟨x, hx, ⟨id, id, rfl⟩⟩
  · rw [key] at hx'; split at hx'
    · rename_i hk; exact hm.2 x' hx' (fun x h => hc x (by rw [hold t hk]; exact h))
    · exact hc x' hx'

/-- **seL4's `ct_not_in_q`, `ct_in_state activatable`, `valid_queues`'
runnability and the idle-thread placement facts, on every core, with one core's
scheduling point open.**  Between scheduling points (`e = none`) a core's
current thread is runnable, queued on no run queue (read off its run-queue
links), and run by no other core.  Inside core `c`'s scheduling point
(`e = some p`, `p.core = c`), `c`'s current thread may be queued on `c` after a
preemption (`.preempt c`), or no longer runnable after a block (`.block c`),
until the dispatch that replaces it; seL4 states the same exceptions by asking
these facts only while the scheduler action is `resume_cur_thread`.  The two
exceptions cannot meet: every queued thread is runnable.  In every case no idle thread is queued (seL4 never enqueues the idle
thread), an idle thread runs only on its own core and is always runnable, and
every TCB's two state fields agree (`TCB.Coherent`).

**Every placed thread is on its home core** (seL4's `tcbAffinity` placement:
`tcbSchedEnqueue` queues a thread on `tcbAffinity`'s queue and a core runs only
what its own queue holds).  A thread current on core `c` or queued on `c` is
homed on `c` (`homedOn`: its affinity, an unpinned thread on the boot core), and
so is each core's idle thread.  An affinity change keeps it by taking the
thread off its old home in the same transition (`setThreadCpuAffinityWithMigration`). -/
structure currentDequeuedUniqueExcept (st : SystemState) (e : Option SchedPoint) : Prop where
  current : ∀ c t, st.scheduler.currentOnCore c = some t →
    (∀ c', st.queuedOn c' t = true → e = some (.preempt c) ∧ c' = c) ∧
    (∀ c', st.scheduler.currentOnCore c' = some t → c' = c) ∧
    (e = some (.block c) ∨ st.runnable t)
  idleOff : ∀ t, Kernel.isIdleThreadId t = true → ∀ c', st.queuedOn c' t = false
  idleHome : ∀ c c', st.scheduler.currentOnCore c' = some (Kernel.idleThreadId c) → c' = c
  queuedRunnable : ∀ c t, st.queuedOn c t = true → st.runnable t
  coherent : ∀ t, st.coherentAt t
  idleRunnable : ∀ c, st.runnable (Kernel.idleThreadId c)
  currentActive : ∀ c t, st.scheduler.currentOnCore c = some t → st.activeAt t
  currentHome : ∀ c t, st.scheduler.currentOnCore c = some t → st.homedOn t c
  queuedHome : ∀ c t, st.queuedOn c t = true → st.homedOn t c
  idleHomed : ∀ c, st.homedOn (Kernel.idleThreadId c) c

/-- `t` is no core's current thread: the premise a wake of `t` needs. -/
def currentNowhere (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ c, st.scheduler.currentOnCore c ≠ some t

/-- A step that keeps every current slot keeps a thread current nowhere. -/
theorem currentNowhere.of_current_eq {st st' : SystemState} {t : SeLe4n.ThreadId}
    (h : st'.scheduler.currentCode = st.scheduler.currentCode) (hN : st.currentNowhere t) :
    st'.currentNowhere t := fun c => by
  unfold SchedulerState.currentOnCore; rw [h]; exact hN c

/-- ...and so does a step that keeps the whole scheduler. -/
theorem currentNowhere.of_scheduler_eq {st st' : SystemState} {t : SeLe4n.ThreadId}
    (h : st'.scheduler = st.scheduler) (hN : st.currentNowhere t) : st'.currentNowhere t :=
  hN.of_current_eq (by rw [h])

/-- The property between scheduling points: every core's current thread is on
no run queue and runs on that core alone. -/
def currentDequeuedUnique (st : SystemState) : Prop := st.currentDequeuedUniqueExcept none

/-- Between scheduling points a current thread is on no queue. -/
theorem currentDequeuedUnique.not_queued {st : SystemState} (h : st.currentDequeuedUnique)
    {c : CoreId} {t : SeLe4n.ThreadId} (ht : st.scheduler.currentOnCore c = some t)
    (c' : CoreId) : st.queuedOn c' t = false := by
  cases hq : st.queuedOn c' t
  · rfl
  · exact absurd ((h.current c t ht).1 c' hq).1 (fun h => by cases h)

/-- Between scheduling points a current thread is runnable. -/
theorem currentDequeuedUnique.runnable {st : SystemState} (h : st.currentDequeuedUnique)
    {c : CoreId} {t : SeLe4n.ThreadId} (ht : st.scheduler.currentOnCore c = some t) :
    st.runnable t :=
  ((h.current c t ht).2.2).resolve_left (fun h => by cases h)

/-- What holds between scheduling points holds inside any one. -/
theorem currentDequeuedUnique.except {st : SystemState} (h : st.currentDequeuedUnique)
    (e : Option SchedPoint) : st.currentDequeuedUniqueExcept e :=
  ⟨fun c t ht => ⟨fun c' hq => absurd ((h.current c t ht).1 c' hq).1 (fun h => by cases h),
    (h.current c t ht).2.1, .inr (h.runnable ht)⟩,
    h.idleOff, h.idleHome, h.queuedRunnable, h.coherent, h.idleRunnable, h.currentActive,
    h.currentHome, h.queuedHome, h.idleHomed⟩

/-- A step that empties or keeps every current slot, takes no current thread
and no idle thread onto a queue, queues only runnable threads on their home
cores and keeps the state fields monotone keeps the property whatever point is
open. -/
theorem currentDequeuedUniqueExcept_of_frame {st st' : SystemState} {e : Option SchedPoint}
    (hC : ∀ c t, st'.scheduler.currentOnCore c = some t → st.scheduler.currentOnCore c = some t)
    (hQ : ∀ c t, st.scheduler.currentOnCore c = some t → ∀ c',
      st'.queuedOn c' t = true → st.queuedOn c' t = true)
    (hI : ∀ t, Kernel.isIdleThreadId t = true → ∀ c',
      st'.queuedOn c' t = true → st.queuedOn c' t = true)
    (hN : ∀ c t, st'.queuedOn c t = true →
      st.queuedOn c t = true ∨ (st'.runnable t ∧ st'.homedOn t c))
    (hM : StateMono st st')
    (h : st.currentDequeuedUniqueExcept e) : st'.currentDequeuedUniqueExcept e := by
  refine ⟨fun c t hc => ?_, fun t ht c' => ?_, fun c c' hc => h.idleHome c c' (hC c' _ hc),
    fun c t hq => ?_, fun t => (hM t).2.1 (h.coherent t), fun c => (hM _).1 (h.idleRunnable c),
    fun c t hc => hM.activeAt (h.currentActive c t (hC c t hc)),
    fun c t hc => hM.homedOn (h.currentActive c t (hC c t hc)) (h.currentHome c t (hC c t hc)),
    fun c t hq => ?_,
    fun c => hM.homedOn (h.idleRunnable c).activeAt (h.idleHomed c)⟩
  · have hc0 := hC c t hc
    obtain ⟨h1, h2, h3⟩ := h.current c t hc0
    exact ⟨fun c' hq => h1 c' (hQ c t hc0 c' hq), fun c' hc' => h2 c' (hC c' t hc'),
      h3.imp_right (hM t).1⟩
  · cases hq : st'.queuedOn c' t
    · rfl
    · have h' := hI t ht c' hq
      rw [h.idleOff t ht c'] at h'
      cases h'
  · rcases hN c t hq with h' | h'
    · exact (hM t).1 (h.queuedRunnable c t h')
    · exact h'.1
  · rcases hN c t hq with h' | h'
    · exact hM.homedOn (h.queuedRunnable c t h').activeAt (h.queuedHome c t h')
    · exact h'.2

/-- **A step that moves one thread's home** — the affinity change: it empties
or keeps every current slot, takes no thread current after it onto a queue it
was not on, queues no idle thread and no new thread but `t`, keeps the state
fields monotone and every other active thread on its home, and leaves `t`
current or queued only on its new home.  The property holds whatever point is
open. -/
theorem currentDequeuedUniqueExcept_of_rehome {st st' : SystemState} {e : Option SchedPoint}
    {t : SeLe4n.ThreadId}
    (hC : ∀ c u, st'.scheduler.currentOnCore c = some u → st.scheduler.currentOnCore c = some u)
    (hQ : ∀ c u, st'.scheduler.currentOnCore c = some u → ∀ c',
      st'.queuedOn c' u = true → st.queuedOn c' u = true)
    (hI : ∀ u, Kernel.isIdleThreadId u = true → ∀ c',
      st'.queuedOn c' u = true → st.queuedOn c' u = true)
    (hN : ∀ c u, st'.queuedOn c u = true → st.queuedOn c u = true ∨ (u = t ∧ st'.runnable t))
    (hM : ∀ u, (st.runnable u → st'.runnable u) ∧ (st.coherentAt u → st'.coherentAt u) ∧
      (st.activeAt u → st'.activeAt u))
    (hA : ∀ u c, u ≠ t → st.activeAt u → st.homedOn u c → st'.homedOn u c)
    (hTq : ∀ c, st'.queuedOn c t = true → st'.homedOn t c)
    (hTc : ∀ c, st'.scheduler.currentOnCore c = some t → st'.homedOn t c)
    (hTi : Kernel.isIdleThreadId t = false)
    (h : st.currentDequeuedUniqueExcept e) : st'.currentDequeuedUniqueExcept e := by
  refine ⟨fun c u hc => ?_, fun u hu c' => ?_, fun c c' hc => h.idleHome c c' (hC c' _ hc),
    fun c u hq => ?_, fun u => (hM u).2.1 (h.coherent u), fun c => (hM _).1 (h.idleRunnable c),
    fun c u hc => (hM u).2.2 (h.currentActive c u (hC c u hc)),
    fun c u hc => ?_, fun c u hq => ?_, fun c => ?_⟩
  · have hc0 := hC c u hc
    obtain ⟨h1, h2, h3⟩ := h.current c u hc0
    exact ⟨fun c' hq => h1 c' (hQ c u hc c' hq), fun c' hc' => h2 c' (hC c' u hc'),
      h3.imp_right (hM u).1⟩
  · cases hq : st'.queuedOn c' u
    · rfl
    · have h' := hI u hu c' hq
      rw [h.idleOff u hu c'] at h'
      cases h'
  · rcases hN c u hq with h' | ⟨rfl, h'⟩
    · exact (hM u).1 (h.queuedRunnable c u h')
    · exact h'
  · by_cases hu : u = t
    · subst hu; exact hTc c hc
    · exact hA u c hu (h.currentActive c u (hC c u hc)) (h.currentHome c u (hC c u hc))
  · rcases hN c u hq with h' | ⟨rfl, -⟩
    · by_cases hu : u = t
      · subst hu; exact hTq c hq
      · exact hA u c hu (h.queuedRunnable c u h').activeAt (h.queuedHome c u h')
    · exact hTq c hq
  · have hne : Kernel.idleThreadId c ≠ t := fun hh => by
      rw [← hh, Kernel.isIdleThreadId_idleThreadId] at hTi; cases hTi
    exact hA _ c hne (h.idleRunnable c).activeAt (h.idleHomed c)

/-- The same, for a step whose queues only lose threads. -/
theorem currentDequeuedUniqueExcept_of_shrink {st st' : SystemState} {e : Option SchedPoint}
    (hC : ∀ c t, st'.scheduler.currentOnCore c = some t → st.scheduler.currentOnCore c = some t)
    (hQ : ∀ c t, st'.queuedOn c t = true → st.queuedOn c t = true)
    (hM : StateMono st st')
    (h : st.currentDequeuedUniqueExcept e) : st'.currentDequeuedUniqueExcept e :=
  currentDequeuedUniqueExcept_of_frame hC (fun _ t _ c' => hQ c' t) (fun t _ c' => hQ c' t)
    (fun c t h' => .inl (hQ c t h')) hM h

/-- The same, for a step that keeps every core's current slot and every
thread's run-queue entry. -/
theorem currentDequeuedUniqueExcept_of_eq {st st' : SystemState} {e : Option SchedPoint}
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hL : ∀ c t, st'.runLinkOn c t = st.runLinkOn c t)
    (hM : StateMono st st')
    (h : st.currentDequeuedUniqueExcept e) : st'.currentDequeuedUniqueExcept e :=
  currentDequeuedUniqueExcept_of_shrink
    (fun c t h' => by rw [SchedulerState.currentOnCore, hC] at h'; exact h')
    (fun c t h' => by rw [queuedOn_eq_runLinkOn, hL, ← queuedOn_eq_runLinkOn] at h'; exact h')
    hM h

/-- A thread's links name one core: it is queued on at most one. -/
theorem queuedOn_core_unique {st : SystemState} {c c' : CoreId} {t : SeLe4n.ThreadId}
    (h : st.queuedOn c t = true) (h' : st.queuedOn c' t = true) : c = c' := by
  unfold queuedOn at h h'
  cases hT : st.getTcb? t with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT, beq_iff_eq] at h h'
    exact Fin.ext (by omega)

/-- **A dispatch on core `c`** — `c`'s slot gets `new`, every other core's slot
is kept, and every thread queued afterwards was queued before or is `c`'s
outgoing (non-idle, runnable) thread, requeued on `c` — closes `c`'s
scheduling point, when the incoming thread ends queued nowhere, runs on no other
core, is runnable and homed on `c`, and is an idle thread only if it is `c`'s
own.  Any other core's open point stays open
(`he`). -/
theorem currentDequeuedUniqueExcept_of_dispatch {st st' : SystemState} {c : CoreId}
    {new : Option SeLe4n.ThreadId} {e e' : Option SchedPoint}
    (hD : st.currentDequeuedUniqueExcept e)
    (he : ∀ p, e = some p → p.core ≠ c → e' = some p)
    (hCur : ∀ c', st'.scheduler.currentOnCore c' =
      if c' = c then new else st.scheduler.currentOnCore c')
    (hNew : ∀ t, new = some t →
      (∀ c', st'.queuedOn c' t = false) ∧
      (∀ c', c' ≠ c → st.scheduler.currentOnCore c' ≠ some t) ∧ st'.runnable t ∧
      st'.homedOn t c)
    (hIdle : ∀ c0, new = some (Kernel.idleThreadId c0) → c0 = c)
    (hQ : ∀ c' x, st'.queuedOn c' x = true → st.queuedOn c' x = true ∨
      (st.scheduler.currentOnCore c = some x ∧ Kernel.isIdleThreadId x = false ∧
        st'.runnable x ∧ c' = c))
    (hM : StateMono st st') :
    st'.currentDequeuedUniqueExcept e' := by
  refine ⟨fun c1 t h1 => ?_, fun t ht c' => ?_, fun c0 c' h' => ?_, fun c' x hq => ?_,
    fun t => (hM t).2.1 (hD.coherent t), fun c0 => (hM _).1 (hD.idleRunnable c0),
    fun c1 t h1 => ?_, fun c1 t h1 => ?_, fun c' x hq => ?_,
    fun c0 => hM.homedOn (hD.idleRunnable c0).activeAt (hD.idleHomed c0)⟩
  rotate_left 4
  · rw [hCur] at h1
    by_cases hc : c1 = c
    · rw [if_pos hc] at h1; exact (hNew t h1).2.2.1.activeAt
    · rw [if_neg hc] at h1; exact hM.activeAt (hD.currentActive c1 t h1)
  · rw [hCur] at h1
    by_cases hc : c1 = c
    · rw [if_pos hc] at h1; rw [hc]; exact (hNew t h1).2.2.2
    · rw [if_neg hc] at h1
      exact hM.homedOn (hD.currentActive c1 t h1) (hD.currentHome c1 t h1)
  · rcases hQ c' x hq with h | ⟨h, _, _, hc'⟩
    · exact hM.homedOn (hD.queuedRunnable c' x h).activeAt (hD.queuedHome c' x h)
    · rw [hc']; exact hM.homedOn (hD.currentActive c x h) (hD.currentHome c x h)
  · rw [hCur] at h1
    by_cases hc : c1 = c
    · rw [if_pos hc] at h1
      refine ⟨fun c' hq => ?_, fun c' hc' => ?_, .inr (hNew t h1).2.2.1⟩
      · rw [(hNew t h1).1 c'] at hq; cases hq
      · rw [hCur] at hc'
        by_cases hc'c : c' = c
        · rw [hc'c, hc]
        · rw [if_neg hc'c] at hc'; exact absurd hc' ((hNew t h1).2.1 c' hc'c)
    · rw [if_neg hc] at h1
      obtain ⟨hNo, hU, hRun⟩ := hD.current c1 t h1
      refine ⟨fun c' hq => ?_, fun c' hc' => ?_, ?_⟩
      · rcases hQ c' t hq with h | ⟨h, _⟩
        · obtain ⟨he1, hc'⟩ := hNo c' h
          exact ⟨he _ he1 hc, hc'⟩
        · exact absurd (hU c h).symm hc
      · rw [hCur] at hc'
        by_cases hc'c : c' = c
        · rw [if_pos hc'c] at hc'; exact absurd h1 ((hNew t hc').2.1 c1 hc)
        · rw [if_neg hc'c] at hc'; exact hU c' hc'
      · rcases hRun with h | h
        · exact .inl (he _ h hc)
        · exact .inr ((hM t).1 h)
  · cases hq : st'.queuedOn c' t
    · rfl
    · rcases hQ c' t hq with h | ⟨_, h, _⟩
      · rw [hD.idleOff t ht c'] at h; cases h
      · rw [ht] at h; cases h
  · rw [hCur] at h'
    by_cases hc : c' = c
    · rw [if_pos hc] at h'; rw [hc, hIdle c0 h']
    · rw [if_neg hc] at h'; exact hD.idleHome c0 c' h'
  · rcases hQ c' x hq with h | ⟨_, _, h, _⟩
    · exact (hM x).1 (hD.queuedRunnable c' x h)
    · exact h

/-- **A preemption on core `c`** — every slot kept, and every thread queued
afterwards was queued before or is `c`'s current (non-idle) thread, now queued
on `c` — keeps `c`'s preemption point open.  The requeued thread is runnable:
a preemption point does not let `c`'s current thread block. -/
theorem currentDequeuedUniqueExcept_of_requeue {st st' : SystemState} {c : CoreId}
    (hD : st.currentDequeuedUniqueExcept (some (.preempt c)))
    (hC : ∀ c', st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c')
    (hQ : ∀ c' x, st'.queuedOn c' x = true → st.queuedOn c' x = true ∨
      (st.scheduler.currentOnCore c = some x ∧ c' = c ∧ Kernel.isIdleThreadId x = false))
    (hM : StateMono st st') :
    st'.currentDequeuedUniqueExcept (some (.preempt c)) := by
  refine ⟨fun c1 t h1 => ?_, fun t ht c' => ?_,
    fun c0 c' h' => hD.idleHome c0 c' (by rw [← hC]; exact h'), fun c' x hq => ?_,
    fun t => (hM t).2.1 (hD.coherent t), fun c0 => (hM _).1 (hD.idleRunnable c0),
    fun c1 t h1 => hM.activeAt (hD.currentActive c1 t (by rw [← hC]; exact h1)),
    fun c1 t h1 => hM.homedOn (hD.currentActive c1 t (by rw [← hC]; exact h1))
      (hD.currentHome c1 t (by rw [← hC]; exact h1)),
    fun c' x hq => ?_, fun c0 => hM.homedOn (hD.idleRunnable c0).activeAt (hD.idleHomed c0)⟩
  rotate_left 3
  · rcases hQ c' x hq with h | ⟨hx, hc', _⟩
    · exact hM.homedOn (hD.queuedRunnable c' x h).activeAt (hD.queuedHome c' x h)
    · rw [hc']; exact hM.homedOn (hD.currentActive c x hx) (hD.currentHome c x hx)
  · rw [hC] at h1
    obtain ⟨hNo, hU, hRun⟩ := hD.current c1 t h1
    refine ⟨fun c' hq => ?_, fun c' hc' => hU c' (by rw [← hC]; exact hc'),
      hRun.imp_right (hM t).1⟩
    rcases hQ c' t hq with h | ⟨h, hc', _⟩
    · exact hNo c' h
    · have h0 := hU c h
      subst h0; exact ⟨rfl, hc'⟩
  · cases hq : st'.queuedOn c' t
    · rfl
    · rcases hQ c' t hq with h | ⟨_, _, h⟩
      · rw [hD.idleOff t ht c'] at h; cases h
      · rw [ht] at h; cases h
  · rcases hQ c' x hq with h | ⟨hx, _, _⟩
    · exact (hM x).1 (hD.queuedRunnable c' x h)
    · exact (hM x).1 ((hD.current c x hx).2.2.resolve_left (fun h => by cases h))

/-- **A block on core `c`** — a write that leaves every current slot and every
run-queue entry alone and changes the state fields of `c`'s current thread `t`
only, leaving it coherent — keeps `c`'s block point open when `t` is no idle
thread: a blocked current thread is the exception a block point allows, and
the point already keeps `t` off the queues. -/
theorem currentDequeuedUniqueExcept_of_block {st st' : SystemState} {c : CoreId}
    {t : SeLe4n.ThreadId}
    (hD : st.currentDequeuedUniqueExcept (some (.block c)))
    (ht : st.scheduler.currentOnCore c = some t)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hL : ∀ c u, st'.runLinkOn c u = st.runLinkOn c u)
    (hNI : Kernel.isIdleThreadId t = false)
    (hM : ∀ u, u ≠ t → (st.runnable u → st'.runnable u) ∧ (st.coherentAt u → st'.coherentAt u) ∧
      (st.activeAt u → st'.activeAt u))
    (hH : ∀ u c', st.homedOn u c' → st'.homedOn u c')
    (hA : st'.activeAt t) :
    st'.currentDequeuedUniqueExcept (some (.block c)) := by
  have hNQ : ∀ c', st.queuedOn c' t = false := fun c' => by
    cases hq : st.queuedOn c' t
    · rfl
    · cases ((hD.current c t ht).1 c' hq).1
  have hCur : ∀ c', st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := fun c' => by
    unfold SchedulerState.currentOnCore; rw [hC]
  have hQ : ∀ c' u, st'.queuedOn c' u = st.queuedOn c' u := fun c' u => by
    rw [queuedOn_eq_runLinkOn, hL, ← queuedOn_eq_runLinkOn]
  refine ⟨fun c1 u h1 => ?_, fun u hu c' => by rw [hQ]; exact hD.idleOff u hu c',
    fun c0 c' h' => hD.idleHome c0 c' (by rw [← hCur]; exact h'), fun c' u hq => ?_,
    fun u => ?_, fun c0 => ?_, fun c1 u h1 => ?_,
    fun c1 u h1 => hH u c1 (hD.currentHome c1 u (by rw [← hCur]; exact h1)),
    fun c' u hq => hH u c' (hD.queuedHome c' u (by rw [← hQ]; exact hq)),
    fun c0 => hH _ c0 (hD.idleHomed c0)⟩
  · rw [hCur] at h1
    obtain ⟨hNo, hU, hRun⟩ := hD.current c1 u h1
    refine ⟨fun c' hq => hNo c' (by rw [← hQ]; exact hq),
      fun c' hc' => hU c' (by rw [← hCur]; exact hc'), ?_⟩
    by_cases hc : c1 = c
    · exact .inl (by rw [hc])
    · have hne : u ≠ t := fun h => hc (by subst h; exact (hD.current c u ht).2.1 c1 h1)
      rcases hRun with h | h
      · cases h; exact absurd rfl hc
      · exact .inr ((hM u hne).1 h)
  · rw [hQ] at hq
    have hne : u ≠ t := fun h => by subst h; rw [hNQ c'] at hq; cases hq
    exact (hM u hne).1 (hD.queuedRunnable c' u hq)
  · by_cases hu : u = t
    · subst hu; exact hA.coherentAt
    · exact (hM u hu).2.1 (hD.coherent u)
  · have hne : Kernel.idleThreadId c0 ≠ t := fun h => by
      rw [← h, Kernel.isIdleThreadId_idleThreadId] at hNI; cases hNI
    exact (hM _ hne).1 (hD.idleRunnable c0)
  · rw [hCur] at h1
    by_cases hu : u = t
    · subst hu; exact hA
    · exact (hM u hu).2.2 (hD.currentActive c1 u h1)

/-- **A write to a thread off every core and every queue** — one that leaves
every current slot and run-queue entry alone, changes the state fields of a
thread `t` no core runs and no queue holds, and leaves `t` coherent — keeps
the property whatever point is open, `t` being no idle thread.  The fault
suspend's `.Inactive` mark after the deschedule is one. -/
theorem currentDequeuedUniqueExcept_of_offWrite {st st' : SystemState} {e : Option SchedPoint}
    {t : SeLe4n.ThreadId}
    (hD : st.currentDequeuedUniqueExcept e) (hNC : st.currentNowhere t)
    (hNQ : ∀ c, st.queuedOn c t = false)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hL : ∀ c u, st'.runLinkOn c u = st.runLinkOn c u) (hNI : Kernel.isIdleThreadId t = false)
    (hM : ∀ u, u ≠ t → (st.runnable u → st'.runnable u) ∧ (st.coherentAt u → st'.coherentAt u) ∧
      (st.activeAt u → st'.activeAt u))
    (hH : ∀ u c', u ≠ t → st.homedOn u c' → st'.homedOn u c')
    (hCo : st'.coherentAt t) : st'.currentDequeuedUniqueExcept e := by
  have hCur : ∀ c', st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := fun c' => by
    unfold SchedulerState.currentOnCore; rw [hC]
  have hQ : ∀ c' u, st'.queuedOn c' u = st.queuedOn c' u := fun c' u => by
    rw [queuedOn_eq_runLinkOn, hL, ← queuedOn_eq_runLinkOn]
  have hNe : ∀ c u, st.scheduler.currentOnCore c = some u → u ≠ t := fun c u h hu => by
    subst hu; exact hNC c h
  refine ⟨fun c1 u h1 => ?_, fun u hu c' => by rw [hQ]; exact hD.idleOff u hu c',
    fun c0 c' h' => hD.idleHome c0 c' (by rw [← hCur]; exact h'), fun c' u hq => ?_,
    fun u => ?_, fun c0 => ?_, fun c1 u h1 => ?_,
    fun c1 u h1 => hH u c1 (hNe c1 u (by rw [← hCur]; exact h1))
      (hD.currentHome c1 u (by rw [← hCur]; exact h1)),
    fun c' u hq => hH u c' (fun h => by subst h; rw [hQ, hNQ c'] at hq; cases hq)
      (hD.queuedHome c' u (by rw [← hQ]; exact hq)),
    fun c0 => hH _ c0 (fun h => by rw [← h, Kernel.isIdleThreadId_idleThreadId] at hNI; cases hNI)
      (hD.idleHomed c0)⟩
  · rw [hCur] at h1
    obtain ⟨hNo, hU, hRun⟩ := hD.current c1 u h1
    exact ⟨fun c' hq => hNo c' (by rw [← hQ]; exact hq),
      fun c' hc' => hU c' (by rw [← hCur]; exact hc'), hRun.imp_right (hM u (hNe c1 u h1)).1⟩
  · rw [hQ] at hq
    have hne : u ≠ t := fun h => by subst h; rw [hNQ c'] at hq; cases hq
    exact (hM u hne).1 (hD.queuedRunnable c' u hq)
  · by_cases hu : u = t
    · subst hu; exact hCo
    · exact (hM u hu).2.1 (hD.coherent u)
  · have hne : Kernel.idleThreadId c0 ≠ t := fun h => by
      rw [← h, Kernel.isIdleThreadId_idleThreadId] at hNI; cases hNI
    exact (hM _ hne).1 (hD.idleRunnable c0)
  · rw [hCur] at h1
    exact (hM u (hNe c1 u h1)).2.2 (hD.currentActive c1 u h1)

-- ============================================================================
-- Stages
-- ============================================================================

/-- WS-ZA ZA4.5: **a step that keeps the run queues in agreement with the
threads' links** — from a state whose object store keeps its table invariant
and whose queues agree with the links, it reaches such a state (`links`, the
stage read as a function) — **and keeps the table references recorded**
(`tables`, `SystemState.tableReferencesRecorded`): every write primitive a stage
is built from proves both (its table half a `TableReferenceFrame`, or a
registry writer's preservation theorem), so every kernel entry's stage proof is
also its proof that the references stay recorded. -/
structure RunQueueLinkStageOn (L : SeLe4n.ObjId → Prop) (st st' : SystemState) : Prop where
  links : st.objects.invExt → st.runQueueRefined → st'.objects.invExt ∧ st'.runQueueRefined
  tables : st.objects.invExt → st.runQueueRefined → st.tableReferencesRecorded →
    st'.tableReferencesRecorded
  release : st.objects.invExt → st.runQueueRefined → st.releaseQueueRefined →
    st'.releaseQueueRefined
  /-- WS-ZA ZA6.4: the refill state stays sound off every set of contexts
  (`refillsSoundExcept`): every context well formed, its refills conserved, no
  bound context's pending refill stranded off the release queues, and every
  queued context bound — for the contexts off `S`, whatever `S`, so a write to
  one context composes with the stages around it. -/
  refills : ∀ S, st.objects.invExt → st.runQueueRefined → st.releaseQueueRefined →
    st.refillsSoundExcept S → st'.refillsSoundExcept S
  /-- WS-ZA ZA6.6: the yield link stays in agreement (`yieldLinksAgree`): each
  end names the other. -/
  yield : st.objects.invExt → st.runQueueRefined → st.yieldLinksAgree → st'.yieldLinksAgree
  /-- WS-ZA ZA6.8: the step links no thread off `L` and makes no linked thread
  off `L` resident (`YieldLinkLiveFrameOn`); `L` is empty but for the yieldTo
  invocation's link of its caller (WS-ZA ZA6.10). -/
  live : st.objects.invExt → st.runQueueRefined → YieldLinkLiveFrameOn L st' st

/-- A link stage that links no thread: `RunQueueLinkStageOn` with `L` empty. -/
abbrev RunQueueLinkStage (st st' : SystemState) : Prop :=
  RunQueueLinkStageOn (fun _ => False) st st'

/-- WS-ZA ZA6.4: **a link stage off the contexts `P`** — the link agreement,
the table references and the release queues, with the refill state kept sound
only off sets holding `P`.  A step that writes context `s`'s refills before a
later step re-places it (the charge, then the postpone) is a frame off `s` and
a stage only with the step after it: frames compose
(`RunQueueLinkFrame.trans`), and the composite is closed once
(`RunQueueLinkFrame.withRefills`). -/
structure RunQueueLinkFrameOn (L : SeLe4n.ObjId → Prop) (P : SeLe4n.SchedContextId → Prop)
    (st st' : SystemState) : Prop where
  links : st.objects.invExt → st.runQueueRefined → st'.objects.invExt ∧ st'.runQueueRefined
  tables : st.objects.invExt → st.runQueueRefined → st.tableReferencesRecorded →
    st'.tableReferencesRecorded
  release : st.objects.invExt → st.runQueueRefined → st.releaseQueueRefined →
    st'.releaseQueueRefined
  refills : ∀ S, (∀ x, P x → S x) → st.objects.invExt → st.runQueueRefined →
    st.releaseQueueRefined → st.refillsSoundExcept S → st'.refillsSoundExcept S
  yield : st.objects.invExt → st.runQueueRefined → st.yieldLinksAgree → st'.yieldLinksAgree
  /-- WS-ZA ZA6.8: the step links no thread off `L` and makes no linked thread
  off `L` resident (`YieldLinkLiveFrameOn`). -/
  live : st.objects.invExt → st.runQueueRefined → YieldLinkLiveFrameOn L st' st

/-- A link frame that links no thread: `RunQueueLinkFrameOn` with `L` empty. -/
abbrev RunQueueLinkFrame (P : SeLe4n.SchedContextId → Prop) (st st' : SystemState) : Prop :=
  RunQueueLinkFrameOn (fun _ => False) P st st'

/-- A link stage is a frame off any contexts. -/
theorem RunQueueLinkStage.toFrame {st st' : SystemState} (h : RunQueueLinkStage st st')
    (P : SeLe4n.SchedContextId → Prop) : RunQueueLinkFrame P st st' :=
  ⟨h.links, h.tables, h.release, fun S _ => h.refills S, h.yield, h.live⟩

/-- **Closing a frame off `s`**: a frame off `s` whose end is sound off `S`
whenever it is sound off `S` and `s` (the written context placed) is a link
stage. -/
theorem RunQueueLinkFrame.withRefills {s : SeLe4n.SchedContextId} {st st' : SystemState}
    (h : RunQueueLinkFrame (· = s) st st')
    (hF : ∀ S, ¬ S s → st.objects.invExt → st.runQueueRefined → st.releaseQueueRefined →
      st'.objects.invExt → st'.releaseQueueRefined →
      st.refillsSoundExcept S → st'.refillsSoundExcept (fun x => S x ∨ x = s) →
      st'.refillsSoundExcept S) : RunQueueLinkStage st st' :=
  ⟨h.links, h.tables, h.release, fun S hI hR hQ hS => by
    by_cases hs : S s
    · exact h.refills S (fun x hx => hx ▸ hs) hI hR hQ hS
    · exact hF S hs hI hR hQ (h.links hI hR).1 (h.release hI hR hQ) hS
        (h.refills _ (fun x hx => Or.inr hx) hI hR hQ (hS.mono fun x hx => Or.inl hx)), h.yield, h.live⟩

theorem RunQueueLinkFrame.mono {P P' : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hP : ∀ x, P x → P' x) (h : RunQueueLinkFrame P st st') : RunQueueLinkFrame P' st st' :=
  ⟨h.links, h.tables, h.release, fun S hS => h.refills S (fun x hx => hS x (hP x hx)), h.yield, h.live⟩

theorem RunQueueLinkFrame.refl (P : SeLe4n.SchedContextId → Prop) (st : SystemState) :
    RunQueueLinkFrame P st st :=
  ⟨fun h r => ⟨h, r⟩, fun _ _ t => t, fun _ _ r => r, fun _ _ _ _ _ s => s, fun _ _ y => y,
    fun _ _ => .refl st⟩

theorem RunQueueLinkFrame.trans {P : SeLe4n.SchedContextId → Prop} {st st' st'' : SystemState}
    (h1 : RunQueueLinkFrame P st st') (h2 : RunQueueLinkFrame P st' st'') :
    RunQueueLinkFrame P st st'' :=
  ⟨fun h r => (h1.links h r).elim h2.links,
    fun h r t => let ⟨h', r'⟩ := h1.links h r; h2.tables h' r' (h1.tables h r t),
    fun h r q => let ⟨h', r'⟩ := h1.links h r; h2.release h' r' (h1.release h r q),
    fun S hS h r q x => let ⟨h', r'⟩ := h1.links h r
      h2.refills S hS h' r' (h1.release h r q) (h1.refills S hS h r q x),
    fun h r y => let ⟨h', r'⟩ := h1.links h r; h2.yield h' r' (h1.yield h r y),
    fun h r => let ⟨h', r'⟩ := h1.links h r; (h2.live h' r').trans (h1.live h r)⟩

instance {st st' : SystemState} : CoeFun (RunQueueLinkStage st st')
    (fun _ => st.objects.invExt → st.runQueueRefined →
      st'.objects.invExt ∧ st'.runQueueRefined) := ⟨RunQueueLinkStageOn.links⟩

instance {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState} :
    CoeFun (RunQueueLinkFrame P st st')
    (fun _ => st.objects.invExt → st.runQueueRefined →
      st'.objects.invExt ∧ st'.runQueueRefined) := ⟨RunQueueLinkFrameOn.links⟩

/-- WS-ZA ZA4.5: **a step that keeps the run-queue placement invariants** —
the link agreement, `currentDequeuedUniqueExcept` whichever scheduling point
is open, and the state fields monotone (`StateMono`: a stage blocks and
suspends no thread).  Stages compose (`RunQueueStage.trans`), so a transition's proof is the
composition of its steps' stages. -/
def RunQueueStage (st st' : SystemState) : Prop :=
  RunQueueLinkStage st st' ∧
  (∀ e, st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept e → st'.currentDequeuedUniqueExcept e) ∧
  (st.objects.invExt → st.runQueueRefined → StateMono st st')

/-- WS-ZA ZA6.4: **a stage off the contexts `P`** — a stage whose refill
state is kept sound only off sets holding `P` (`RunQueueLinkFrame`).  The steps
of a write that rewrites context `s`'s refills and re-places it after (the
charge and its postpone, a drain's refill and its re-place, the configure's
purge, store and place, the bind's store and place, the unbind's store and
purge) are frame stages off `s`; every stage is one
(`RunQueueStage.toFrame`), and the composite is closed once
(`RunQueueFrameStage.withRefills`). -/
def RunQueueFrameStage (P : SeLe4n.SchedContextId → Prop) (st st' : SystemState) : Prop :=
  RunQueueLinkFrame P st st' ∧
  (∀ e, st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept e → st'.currentDequeuedUniqueExcept e) ∧
  (st.objects.invExt → st.runQueueRefined → StateMono st st')

/-- A stage is a frame stage off any contexts. -/
theorem RunQueueStage.toFrame {st st' : SystemState} (h : RunQueueStage st st')
    (P : SeLe4n.SchedContextId → Prop) : RunQueueFrameStage P st st' := ⟨h.1.toFrame P, h.2⟩

theorem RunQueueFrameStage.trans {P : SeLe4n.SchedContextId → Prop} {st st' st'' : SystemState}
    (h1 : RunQueueFrameStage P st st') (h2 : RunQueueFrameStage P st' st'') :
    RunQueueFrameStage P st st'' :=
  ⟨h1.1.trans h2.1, fun e h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 e h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

theorem RunQueueFrameStage.mono {P P' : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hP : ∀ x, P x → P' x) (h : RunQueueFrameStage P st st') : RunQueueFrameStage P' st st' :=
  ⟨h.1.mono hP, h.2⟩

/-- **Closing a frame stage off `s`** (`RunQueueLinkFrame.withRefills`). -/
theorem RunQueueFrameStage.withRefills {s : SeLe4n.SchedContextId} {st st' : SystemState}
    (h : RunQueueFrameStage (· = s) st st')
    (hF : ∀ S, ¬ S s → st.objects.invExt → st.runQueueRefined → st.releaseQueueRefined →
      st'.objects.invExt → st'.releaseQueueRefined →
      st.refillsSoundExcept S → st'.refillsSoundExcept (fun x => S x ∨ x = s) →
      st'.refillsSoundExcept S) : RunQueueStage st st' :=
  ⟨h.1.withRefills hF, h.2⟩

/-- A frame stage that holds from a state whose object store keeps its
invariant. -/
theorem RunQueueFrameStage.of_invExt {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (H : st.objects.invExt → RunQueueFrameStage P st st') : RunQueueFrameStage P st st' :=
  ⟨⟨fun h r => (H h).1 h r, fun h r t => (H h).1.tables h r t, fun h r q => (H h).1.release h r q,
      fun S hS h r q x => (H h).1.refills S hS h r q x, fun h r y => (H h).1.yield h r y,
      fun h r => (H h).1.live h r⟩,
    fun e h r r' d => (H h).2.1 e h r r' d,
    fun h r => (H h).2.2 h r⟩

/-- **A step inside core `c`'s scheduling point**: it keeps the link agreement
and keeps the point open.  A preemption's requeue of `c`'s outgoing thread is
one; so is every stage. -/
def RunQueueWindowStage (p : SchedPoint) (st st' : SystemState) : Prop :=
  RunQueueLinkStage st st' ∧
  (st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept (some p) → st'.currentDequeuedUniqueExcept (some p))

/-- **A dispatch on core `c`**: it keeps the link agreement and closes `c`'s
scheduling point, leaving any other core's open. -/
def RunQueueDispatchStage (c : CoreId) (st st' : SystemState) : Prop :=
  RunQueueLinkStage st st' ∧
  (∀ e e', (∀ p, e = some p → p.core ≠ c → e' = some p) →
    st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept e → st'.currentDequeuedUniqueExcept e') ∧
  (st.objects.invExt → st.runQueueRefined → StateMono st st')

/-- **A whole kernel entry**: from a state between scheduling points to one. -/
def RunQueueEntryStage (st st' : SystemState) : Prop :=
  RunQueueLinkStage st st' ∧
  (st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUnique → st'.currentDequeuedUnique)

/-- **A kernel entry keeps the table references recorded**: its link half
carries them (`RunQueueLinkStage.tables`). -/
theorem RunQueueEntryStage.tableReferencesRecorded {st st' : SystemState}
    (h : RunQueueEntryStage st st') (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hT : st.tableReferencesRecorded) : st'.tableReferencesRecorded :=
  h.1.tables hInv hR hT

/-- A link half, a table frame, a release frame and a refill frame make a
link stage: the release frame holds every context's release link and every
release-queue slot (`releaseStateAgree`), so the release queues stay refined;
the refill frame holds every context's refill view (`RefillViewsKept`), so with
the queues' entries the refill state stays sound; the yield frame holds every
slot's yield codes (`YieldLinksKept`), so the yield link stays in agreement. -/
theorem RunQueueLinkStage.of_tableFrame {st st' : SystemState}
    (hL : st.objects.invExt → st.runQueueRefined → st'.objects.invExt ∧ st'.runQueueRefined)
    (hF : st.objects.invExt → TableReferenceFrame st st')
    (hRel : st.objects.invExt → releaseStateAgree st' st)
    (hV : st.objects.invExt → RefillViewsKept st' st)
    (hY : st.objects.invExt → YieldLinksKept st' st)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueLinkStage st st' :=
  ⟨hL, fun h _ t => (hF h).preserves t, fun h _ r => (hRel h).refined r,
    fun _ h _ q s => refillsSoundExcept_of_kept (hV h)
      (fun c => by rw [(hRel h).replenishQueueOnCore c]) ((hRel h).refined q) s,
    fun h _ y => yieldLinksAgree_of_kept (hY h) y, fun h _ => .of_kept (hY h) hRes⟩

/-- A link half and a table frame, with the release queues carried by `hRel`
and the refill state by `hRef`: a step that edits a release queue. -/
theorem RunQueueLinkStage.of_tableFrameWith {st st' : SystemState}
    (hL : st.objects.invExt → st.runQueueRefined → st'.objects.invExt ∧ st'.runQueueRefined)
    (hF : st.objects.invExt → TableReferenceFrame st st')
    (hRel : st.objects.invExt → st.releaseQueueRefined → st'.releaseQueueRefined)
    (hRef : ∀ S, st.objects.invExt → st.releaseQueueRefined → st.refillsSoundExcept S →
      st'.refillsSoundExcept S)
    (hY : st.objects.invExt → YieldLinksKept st' st)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueLinkStage st st' :=
  ⟨hL, fun h _ t => (hF h).preserves t, fun h _ r => hRel h r, fun S h _ q s => hRef S h q s,
    fun h _ y => yieldLinksAgree_of_kept (hY h) y, fun h _ => .of_kept (hY h) hRes⟩

theorem RunQueueLinkStage.refl (st : SystemState) : RunQueueLinkStage st st :=
  ⟨fun h r => ⟨h, r⟩, fun _ _ t => t, fun _ _ r => r, fun _ _ _ _ s => s, fun _ _ y => y,
    fun _ _ => .refl st⟩

theorem RunQueueLinkStage.trans {st st' st'' : SystemState}
    (h1 : RunQueueLinkStage st st') (h2 : RunQueueLinkStage st' st'') :
    RunQueueLinkStage st st'' :=
  ⟨fun h r => (h1 h r).elim h2.links,
    fun h r t => let ⟨h', r'⟩ := h1 h r; h2.tables h' r' (h1.tables h r t),
    fun h r q => let ⟨h', r'⟩ := h1 h r; h2.release h' r' (h1.release h r q),
    fun S h r q s => let ⟨h', r'⟩ := h1 h r
      h2.refills S h' r' (h1.release h r q) (h1.refills S h r q s),
    fun h r y => let ⟨h', r'⟩ := h1 h r; h2.yield h' r' (h1.yield h r y),
    fun h r => let ⟨h', r'⟩ := h1 h r; (h2.live h' r').trans (h1.live h r)⟩

theorem RunQueueStage.refl (st : SystemState) : RunQueueStage st st :=
  ⟨RunQueueLinkStage.refl st, fun _ _ _ _ d => d, fun _ _ => StateMono.refl st⟩

/-- A stage keeps the state fields monotone. -/
theorem RunQueueStage.mono {st st' : SystemState} (h : RunQueueStage st st')
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) : StateMono st st' :=
  h.2.2 hInv hR

/-- A step that writes neither the objects nor the run queues and their ends
keeps the link agreement, whatever it does to the current slots. -/
theorem RunQueueLinkStage.of_frame {st st' : SystemState} (hO : st'.objects = st.objects)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueLinkStage st st' :=
  .of_tableFrame
    (fun h r => ⟨hO ▸ h, runQueueRefined_of_frame (fun c t => runLinkOn_of_objects hO c t) hQ hE r⟩)
    (fun _ => .of_objects_eq hO hT) (fun _ => .of_objects_eq hO hS)
    (fun _ => .of_objects_eq hO) (fun _ => .of_objects_eq hO) hRes

/-- A stage's link half. -/
theorem RunQueueLinkStage.of_stage {st st' : SystemState} (h : RunQueueStage st st') :
    RunQueueLinkStage st st' := h.1

/-- A stage is a step inside any core's scheduling point. -/
theorem RunQueueStage.window {st st' : SystemState} (h : RunQueueStage st st') (p : SchedPoint) :
    RunQueueWindowStage p st st' :=
  ⟨h.1, h.2.1 (some p)⟩

/-- A stage is a kernel entry. -/
theorem RunQueueStage.entry {st st' : SystemState} (h : RunQueueStage st st') :
    RunQueueEntryStage st st' :=
  ⟨h.1, h.2.1 none⟩

/-- A dispatch is a stage: an open point it closes reads as still open. -/
theorem RunQueueDispatchStage.stage {st st' : SystemState} {c : CoreId}
    (h : RunQueueDispatchStage c st st') : RunQueueStage st st' :=
  ⟨h.1, fun e => h.2.1 e e (fun _ he _ => he), h.2.2⟩

theorem RunQueueWindowStage.refl (p : SchedPoint) (st : SystemState) : RunQueueWindowStage p st st :=
  (RunQueueStage.refl st).window p

theorem RunQueueWindowStage.trans {p : SchedPoint} {st st' st'' : SystemState}
    (h1 : RunQueueWindowStage p st st') (h2 : RunQueueWindowStage p st' st'') :
    RunQueueWindowStage p st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2 h' r' r'' (h1.2 h r r' d)⟩

/-- A step inside a point that holds from a state whose object store keeps its
invariant. -/
theorem RunQueueWindowStage.of_invExt {p : SchedPoint} {st st' : SystemState}
    (H : st.objects.invExt → RunQueueWindowStage p st st') : RunQueueWindowStage p st st' :=
  ⟨⟨fun h r => (H h).1 h r, fun h r t => (H h).1.tables h r t, fun h r q => (H h).1.release h r q,
      fun S h r q s => (H h).1.refills S h r q s, fun h r y => (H h).1.yield h r y,
      fun h r => (H h).1.live h r⟩,
    fun h r r' d => (H h).2 h r r' d⟩

theorem RunQueueEntryStage.trans {st st' st'' : SystemState}
    (h1 : RunQueueEntryStage st st') (h2 : RunQueueEntryStage st' st'') :
    RunQueueEntryStage st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2 h' r' r'' (h1.2 h r r' d)⟩

/-- **A scheduling point**: steps inside core `c`'s point, then the dispatch
that closes it, make a kernel entry's worth of steps. -/
theorem RunQueueWindowStage.dispatch {p : SchedPoint} {st st' st'' : SystemState}
    (h1 : RunQueueWindowStage p st st') (h2 : RunQueueDispatchStage p.core st' st'') :
    RunQueueEntryStage st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 (some p) none (fun _ he hne => absurd (by cases he; rfl) hne) h' r' r''
      (h1.2 h r r' (d.except _))⟩

/-- A stage before a dispatch is part of it. -/
theorem RunQueueStage.dispatch {c : CoreId} {st st' st'' : SystemState}
    (h1 : RunQueueStage st st') (h2 : RunQueueDispatchStage c st' st'') :
    RunQueueDispatchStage c st st'' :=
  ⟨h1.1.trans h2.1, fun e e' he h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 e e' he h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

/-- A stage after a dispatch is part of it. -/
theorem RunQueueDispatchStage.trans_stage {c : CoreId} {st st' st'' : SystemState}
    (h1 : RunQueueDispatchStage c st st') (h2 : RunQueueStage st' st'') :
    RunQueueDispatchStage c st st'' :=
  ⟨h1.1.trans h2.1, fun e e' he h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 e' h' r' r'' (h1.2.1 e e' he h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

/-- **A switch on core `c`**: a dispatch on `c` that first puts `c`'s outgoing
thread back on `c`'s queue.  It closes any point but a block on `c`, whose
outgoing thread is blocked and must not be queued; the block path closes its
point with the deschedule (`RunQueueDispatchStage.descheduleCurrent`) instead. -/
def RunQueueSwitchStage (c : CoreId) (st st' : SystemState) : Prop :=
  RunQueueLinkStage st st' ∧
  (∀ e e', (∀ p, e = some p → p.core ≠ c → e' = some p) → e ≠ some (.block c) →
    st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept e → st'.currentDequeuedUniqueExcept e') ∧
  (st.objects.invExt → st.runQueueRefined → StateMono st st')

/-- A dispatch is a switch. -/
theorem RunQueueDispatchStage.switch {c : CoreId} {st st' : SystemState}
    (h : RunQueueDispatchStage c st st') : RunQueueSwitchStage c st st' :=
  ⟨h.1, fun e e' he _ => h.2.1 e e' he, h.2.2⟩

/-- A stage before a switch is part of it. -/
theorem RunQueueStage.switch {c : CoreId} {st st' st'' : SystemState}
    (h1 : RunQueueStage st st') (h2 : RunQueueSwitchStage c st' st'') :
    RunQueueSwitchStage c st st'' :=
  ⟨h1.1.trans h2.1, fun e e' he hb h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 e e' he hb h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

/-- A stage after a switch is part of it. -/
theorem RunQueueSwitchStage.trans_stage {c : CoreId} {st st' st'' : SystemState}
    (h1 : RunQueueSwitchStage c st st') (h2 : RunQueueStage st' st'') :
    RunQueueSwitchStage c st st'' :=
  ⟨h1.1.trans h2.1, fun e e' he hb h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 e' h' r' r'' (h1.2.1 e e' he hb h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

/-- A switch is a kernel entry. -/
theorem RunQueueSwitchStage.entry {c : CoreId} {st st' : SystemState}
    (h : RunQueueSwitchStage c st st') : RunQueueEntryStage st st' :=
  ⟨h.1, h.2.1 none none (fun _ h => by cases h) (fun h => by cases h)⟩

/-- **A preemption point**: steps inside core `c`'s preemption point, then the
switch that closes it, make a kernel entry's worth of steps. -/
theorem RunQueueWindowStage.switch {c : CoreId} {st st' st'' : SystemState}
    (h1 : RunQueueWindowStage (.preempt c) st st') (h2 : RunQueueSwitchStage c st' st'') :
    RunQueueEntryStage st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 (some (.preempt c)) none (fun _ he hne => absurd (by cases he; rfl) hne)
      (fun h => by cases h) h' r' r'' (h1.2 h r r' (d.except _))⟩

/-- A kernel entry run from a state that has all three properties. -/
theorem RunQueueEntryStage.run {st st' : SystemState} (h : RunQueueEntryStage st st')
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hD : st.currentDequeuedUnique) :
    st'.objects.invExt ∧ st'.runQueueRefined ∧ st'.currentDequeuedUnique :=
  let ⟨h', r'⟩ := h.1 hInv hR
  ⟨h', r', h.2 hInv hR r' hD⟩

/-- A stage run from a state that has all three properties. -/
theorem RunQueueStage.run {st st' : SystemState} (h : RunQueueStage st st')
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hD : st.currentDequeuedUnique) :
    st'.objects.invExt ∧ st'.runQueueRefined ∧ st'.currentDequeuedUnique :=
  h.entry.run hInv hR hD

/-- A link stage that keeps every current slot or empties it, and takes no
current thread and no idle thread onto a queue, is a stage. -/
theorem RunQueueStage.of_link' {st st' : SystemState} (hL : RunQueueLinkStage st st')
    (hC : ∀ c t, st'.scheduler.currentOnCore c = some t → st.scheduler.currentOnCore c = some t)
    (hQ : ∀ c t, st.scheduler.currentOnCore c = some t → ∀ c',
      st'.queuedOn c' t = true → st.queuedOn c' t = true)
    (hI : ∀ t, Kernel.isIdleThreadId t = true → ∀ c',
      st'.queuedOn c' t = true → st.queuedOn c' t = true)
    (hN : ∀ c t, st'.queuedOn c t = true →
      st.queuedOn c t = true ∨ (st'.runnable t ∧ st'.homedOn t c))
    (hM : StateMono st st') : RunQueueStage st st' :=
  ⟨hL, fun _ _ _ _ d => currentDequeuedUniqueExcept_of_frame hC hQ hI hN hM d, fun _ _ => hM⟩

/-- A link stage that is a stage from a state between scheduling points is a
kernel entry. -/
theorem RunQueueEntryStage.of_cond {st st' : SystemState} (hL : RunQueueLinkStage st st')
    (H : st.currentDequeuedUnique → RunQueueStage st st') : RunQueueEntryStage st st' :=
  ⟨hL, fun h r r' d => (H d).2.1 none h r r' d⟩

/-- A link stage that is a kernel entry from a state with all three
properties is a kernel entry. -/
theorem RunQueueEntryStage.of_inv {st st' : SystemState} (hL : RunQueueLinkStage st st')
    (H : st.objects.invExt → st.runQueueRefined → st.currentDequeuedUnique →
      RunQueueEntryStage st st') : RunQueueEntryStage st st' :=
  ⟨hL, fun h r r' d => (H h r d).2 h r r' d⟩

/-- A stage that holds from a state whose object store keeps its invariant. -/
theorem RunQueueStage.of_invExt {st st' : SystemState}
    (H : st.objects.invExt → RunQueueStage st st') : RunQueueStage st st' :=
  ⟨⟨fun h r => (H h).1 h r, fun h r t => (H h).1.tables h r t, fun h r q => (H h).1.release h r q,
      fun S h r q s => (H h).1.refills S h r q s, fun h r y => (H h).1.yield h r y,
      fun h r => (H h).1.live h r⟩,
    fun e h r r' d => (H h).2.1 e h r r' d,
    fun h r => (H h).2.2 h r⟩

/-- A link stage that gives no thread a current slot and whose queues only
lose threads is a stage. -/
theorem RunQueueStage.of_link {st st' : SystemState} (hL : RunQueueLinkStage st st')
    (hC : ∀ c t, st'.scheduler.currentOnCore c = some t → st.scheduler.currentOnCore c = some t)
    (hQ : ∀ c t, st'.queuedOn c t = true → st.queuedOn c t = true)
    (hM : StateMono st st') : RunQueueStage st st' :=
  ⟨hL, fun _ _ _ _ d => currentDequeuedUniqueExcept_of_shrink hC hQ hM d, fun _ _ => hM⟩

/-- Under the link agreement, a thread its links queue on `c` is on `c`'s
queue, and conversely. -/
theorem mem_runQueueOnCore_of_queuedOn {st : SystemState} (hR : st.runQueueRefined)
    {c : CoreId} {t : SeLe4n.ThreadId} (h : st.queuedOn c t = true) :
    t ∈ st.scheduler.runQueueOnCore c := by
  rw [(hR c).queuedOn] at h; exact RunQueue.mem_iff_contains.mpr h

theorem queuedOn_of_mem_runQueueOnCore {st : SystemState} (hR : st.runQueueRefined)
    {c : CoreId} {t : SeLe4n.ThreadId} (h : t ∈ st.scheduler.runQueueOnCore c) :
    st.queuedOn c t = true := by
  rw [(hR c).queuedOn]; exact RunQueue.mem_iff_contains.mp h

/-- Across a step whose two ends both agree with their links, a thread's
membership read off its links moves exactly as the queue's does. -/
theorem queuedOn_congr_of_refined {st st' : SystemState} (hR : st.runQueueRefined)
    (hR' : st'.runQueueRefined) (c : CoreId) (u : SeLe4n.ThreadId)
    (hQ : u ∈ st'.scheduler.runQueueOnCore c ↔ u ∈ st.scheduler.runQueueOnCore c) :
    st'.queuedOn c u = st.queuedOn c u := by
  rw [(hR' c).queuedOn, (hR c).queuedOn]
  exact Bool.eq_iff_iff.mpr hQ

theorem RunQueueStage.trans {st st' st'' : SystemState}
    (h1 : RunQueueStage st st') (h2 : RunQueueStage st' st'') : RunQueueStage st st'' :=
  ⟨h1.1.trans h2.1, fun e h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    h2.2.1 e h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1 h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

theorem RunQueueStage.of_eq {st st' : SystemState} (h : st' = st) : RunQueueStage st st' :=
  h ▸ RunQueueStage.refl st

/-- A step that writes neither the objects, the run queues and their ends, nor
any core's current slot. -/
theorem RunQueueStage.of_frame {st st' : SystemState} (hO : st'.objects = st.objects)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  ⟨RunQueueLinkStage.of_frame hO hQ hE hT hS hRes,
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq hC (fun c t => runLinkOn_of_objects hO c t)
      (StateMono.of_objects hO) d, fun _ _ => StateMono.of_objects hO⟩

/-- WS-ZA ZA6.8: a step writing no object, no run queue and no current slot
whose residency writes are carried by `hLive`: the release of a destroyed
thread's cores, which clears residents and sets none. -/
theorem RunQueueStage.of_frameLive {st st' : SystemState} (hO : st'.objects = st.objects)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hLive : Kernel.ResidentsRecordUnlinked st' st)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame) :
    RunQueueStage st st' :=
  ⟨⟨fun h r => ⟨hO ▸ h, runQueueRefined_of_frame (fun c t => runLinkOn_of_objects hO c t) hQ hE r⟩,
    fun _ _ t => (TableReferenceFrame.of_objects_eq hO hT).preserves t,
    fun _ _ q => (releaseStateAgree.of_objects_eq hO hS).refined q,
    fun _ _ _ q s => refillsSoundExcept_of_kept (.of_objects_eq hO)
      (fun c => by rw [(releaseStateAgree.of_objects_eq hO hS).replenishQueueOnCore c])
      ((releaseStateAgree.of_objects_eq hO hS).refined q) s,
    fun _ _ y => yieldLinksAgree_of_kept (.of_objects_eq hO) y,
    fun _ _ => ⟨.of_kept (.of_objects_eq hO), hLive⟩⟩,
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq hC (fun c t => runLinkOn_of_objects hO c t)
      (StateMono.of_objects hO) d, fun _ _ => StateMono.of_objects hO⟩

/-- WS-ZA ZA6.8: **a frame step, then a kernel entry's worth of steps, with the
residency frame stated for the whole**: a step writing no object, no run queue
and no current slot (the residency record, which may make a linked current
thread resident) followed by an entry whose end leaves that resident unlinked
(the activation).  The record alone has no `live` frame; the pair has `hLive`. -/
theorem RunQueueEntryStage.of_frameThen {st m st' : SystemState} (hO : m.objects = st.objects)
    (hQ : m.scheduler.runQueue = st.scheduler.runQueue)
    (hE : m.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hC : m.scheduler.currentCode = st.scheduler.currentCode)
    (hT : m.referenceTables = st.referenceTables)
    (hS : m.scheduler.releaseSlots = st.scheduler.releaseSlots)
    (h2 : RunQueueEntryStage m st')
    (hLive : st.objects.invExt → st.runQueueRefined → Kernel.YieldLinkLiveFrame st' st) :
    RunQueueEntryStage st st' :=
  have P : st.objects.invExt → st.runQueueRefined → m.objects.invExt ∧ m.runQueueRefined :=
    fun h r => ⟨hO ▸ h, runQueueRefined_of_frame (fun c t => runLinkOn_of_objects hO c t) hQ hE r⟩
  have hRel := releaseStateAgree.of_objects_eq (st := st) hO hS
  ⟨⟨fun h r => let ⟨h', r'⟩ := P h r; h2.1.links h' r',
    fun h r t => let ⟨h', r'⟩ := P h r
      h2.1.tables h' r' ((TableReferenceFrame.of_objects_eq hO hT).preserves t),
    fun h r q => let ⟨h', r'⟩ := P h r; h2.1.release h' r' (hRel.refined q),
    fun S h r q x => let ⟨h', r'⟩ := P h r
      h2.1.refills S h' r' (hRel.refined q) (refillsSoundExcept_of_kept (.of_objects_eq hO)
        (fun c => by rw [hRel.replenishQueueOnCore c]) (hRel.refined q) x),
    fun h r y => let ⟨h', r'⟩ := P h r; h2.1.yield h' r' (yieldLinksAgree_of_kept (.of_objects_eq hO) y),
    hLive⟩,
    fun h r r'' d => let ⟨h', r'⟩ := P h r
      h2.2 h' r' r'' (currentDequeuedUniqueExcept_of_eq hC (fun c t => runLinkOn_of_objects hO c t)
        (StateMono.of_objects hO) d)⟩

/-- A step that writes neither the objects, the run queues and their ends, nor
any core's current slot, with the table references carried by `hTab`: a
registry writer that writes no object. -/
theorem RunQueueStage.of_frameWith {st st' : SystemState} (hO : st'.objects = st.objects)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hTab : st.objects.invExt → st.tableReferencesRecorded → st'.tableReferencesRecorded)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  ⟨⟨fun h r => ⟨hO ▸ h, runQueueRefined_of_frame (fun c t => runLinkOn_of_objects hO c t) hQ hE r⟩,
    fun h _ t => hTab h t, fun _ _ q => (releaseStateAgree.of_objects_eq hO hS).refined q,
    fun _ _ _ q s => refillsSoundExcept_of_kept (.of_objects_eq hO)
      (fun c => by rw [(releaseStateAgree.of_objects_eq hO hS).replenishQueueOnCore c])
      ((releaseStateAgree.of_objects_eq hO hS).refined q) s,
    fun _ _ y => yieldLinksAgree_of_kept (.of_objects_eq hO) y,
    fun _ _ => .of_kept (.of_objects_eq hO) hRes⟩,
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq hC (fun c t => runLinkOn_of_objects hO c t)
      (StateMono.of_objects hO) d, fun _ _ => StateMono.of_objects hO⟩

/-- WS-ZA ZA5.11: **a word write is a stage** — a step whose store agrees with
the pre-state's off the taint words, keeping the run queues, their ends and every
core's current slot: no thread's links or state fields are taint words. -/
theorem RunQueueStage.of_objectsAgreeOffTaint {st st' : SystemState}
    (hA : st.objectsAgreeOffTaint st')
    (hI : st.objects.invExt → st'.objects.invExt)
    (hTab : st.objects.invExt → st.tableReferencesRecorded → st'.tableReferencesRecorded)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' := by
  have hRel : releaseStateAgree st' st :=
    ⟨.of_map KernelObject.eraseTaint (fun o _ => by cases o <;> rfl) hA, hS⟩
  have hL : ∀ c t, st'.runLinkOn c t = st.runLinkOn c t := fun c t => by
    have e := getTcb?_map_of_objectsAgreeOffTaint hA (fun x => x.runLinkOn c) (fun _ => rfl) t
    unfold runLinkOn
    cases h2 : st'.getTcb? t <;> cases h1 : st.getTcb? t <;> rw [h1, h2] at e <;>
      first | rfl | cases e | exact Option.some.inj e
  have hM : StateMono st st' := StateMono.of_stateFields
    (getTcb?_map_of_objectsAgreeOffTaint hA _ (fun _ => rfl))
  have hV : RefillViewsKept st' st :=
    .of_map KernelObject.eraseTaint (fun o => by cases o <;> rfl) hA
  have hY : YieldLinksKept st' st :=
    .of_map KernelObject.eraseTaint (fun o => by cases o <;> rfl) hA
  exact ⟨⟨fun h r => ⟨hI h, runQueueRefined_of_frame hL hQ hE r⟩, fun h _ t => hTab h t,
      fun _ _ q => hRel.refined q,
      fun _ _ _ q s => refillsSoundExcept_of_kept hV (fun c => by rw [hRel.replenishQueueOnCore c])
        (hRel.refined q) s, fun _ _ y => yieldLinksAgree_of_kept hY y, fun _ _ => .of_kept hY hRes⟩,
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq hC hL hM d, fun _ _ => hM⟩

/-- WS-ZA ZA6.3: **a step that keeps every thread's TCB is a stage** — it
writes only objects no thread is (a release-queue edit writes contexts' links),
keeping every slot's back-links, the run queues, their ends and every core's
current slot. -/
theorem RunQueueFrameStage.of_tcbFrame {st st' : SystemState}
    (hG : ∀ t, st'.getTcb? t = st.getTcb? t)
    (hB : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map KernelObject.tableBackLinks =
      (st.objects[k]?).map KernelObject.tableBackLinks)
    (hI : st.objects.invExt → st'.objects.invExt)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hT : st'.referenceTables = st.referenceTables)
    (hRel : st.objects.invExt → st.releaseQueueRefined → st'.releaseQueueRefined)
    {P : SeLe4n.SchedContextId → Prop}
    (hRef : ∀ S, (∀ x, P x → S x) → st.objects.invExt → st.releaseQueueRefined →
      st.refillsSoundExcept S → st'.refillsSoundExcept S)
    (hY : st.objects.invExt → YieldLinksKept st' st)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueFrameStage P st st' := by
  have hL : ∀ c t, st'.runLinkOn c t = st.runLinkOn c t := fun c t => runLinkOn_of_getTcb? (hG t) c
  have hM : StateMono st st' := StateMono.of_getTcb hG
  exact ⟨⟨fun h r => ⟨hI h, runQueueRefined_of_frame hL hQ hE r⟩,
      fun h _ t => (TableReferenceFrame.of_map_tableBackLinks hT hB).preserves t,
      fun h _ q => hRel h q, fun S hS h _ q x => hRef S hS h q x,
      fun h _ y => yieldLinksAgree_of_kept (hY h) y, fun h _ => .of_kept (hY h) hRes⟩,
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq hC hL hM d, fun _ _ => hM⟩

/-- ...with the refill state carried by `hRef`. -/
theorem RunQueueStage.of_tcbFrame {st st' : SystemState}
    (hG : ∀ t, st'.getTcb? t = st.getTcb? t)
    (hB : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map KernelObject.tableBackLinks =
      (st.objects[k]?).map KernelObject.tableBackLinks)
    (hI : st.objects.invExt → st'.objects.invExt)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hT : st'.referenceTables = st.referenceTables)
    (hRel : st.objects.invExt → st.releaseQueueRefined → st'.releaseQueueRefined)
    (hRef : ∀ S, st.objects.invExt → st.releaseQueueRefined → st.refillsSoundExcept S →
      st'.refillsSoundExcept S)
    (hY : st.objects.invExt → YieldLinksKept st' st)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  let h := RunQueueFrameStage.of_tcbFrame (P := fun _ => False) hG hB hI hQ hE hC hT hRel
    (fun S _ => hRef S) hY hRes
  ⟨⟨h.1.links, h.1.tables, h.1.release, fun S => h.1.refills S (fun _ h => h.elim), h.1.yield,
      h.1.live⟩,
    h.2⟩

/-- A step that writes neither the objects nor the run queues and their ends,
and only empties or keeps each core's current slot. -/
theorem RunQueueStage.of_frame_vacate {st st' : SystemState} (hO : st'.objects = st.objects)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hC : ∀ c t, st'.scheduler.currentOnCore c = some t →
      st.scheduler.currentOnCore c = some t)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  RunQueueStage.of_link (RunQueueLinkStage.of_frame hO hQ hE hT hS hRes)
    hC (fun c t h' => by
      rw [queuedOn_eq_runLinkOn, runLinkOn_of_objects hO, ← queuedOn_eq_runLinkOn] at h'
      exact h') (StateMono.of_objects hO)

/-- A TCB write that keeps the run-queue fields keeps the link agreement. -/
theorem RunQueueLinkStage.updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hW : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hY : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    RunQueueLinkStage st (st.updateTcb tid f) :=
  .of_tableFrame
    (fun h r => ⟨updateTcb_preserves_objects_invExt st tid f h, updateTcb_runQueueRefined h hf r⟩)
    (fun h => TableReferenceFrame.updateTcb st tid f h hW)
    (fun h => .of_getSchedContext? (updateTcb_getSchedContext? st tid f h)
      (by rw [updateTcb_scheduler]))
    (fun h => .of_getSchedContext?_eq (updateTcb_getSchedContext? st tid f h))
    (fun h => .updateTcb st tid f h hY)

theorem RunQueueStage.updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hm : TCB.StateMono f := by tcb_state_mono)
    (hW : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hY : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    RunQueueStage st (st.updateTcb tid f) :=
  ⟨RunQueueLinkStage.updateTcb st tid hf hW hY,
    fun _ h _ _ d => currentDequeuedUniqueExcept_of_eq (by rw [updateTcb_scheduler]) (fun c x => by
      unfold SystemState.updateTcb; split
      · rename_i t hT _; exact runLinkOn_rewriteObject_tcb _ h hT (hf t) c x
      · rfl) (StateMono.updateTcb h tid hm) d, fun h _ => StateMono.updateTcb h tid hm⟩

/-- A typed read-modify-write of a thread off every core and every queue,
leaving it coherent: the property holds whatever point is open. -/
theorem currentDequeuedUniqueExcept_updateTcb_offWrite {st : SystemState} {e : Option SchedPoint}
    {tid : SeLe4n.ThreadId} {f : TCB → TCB} (hInv : st.objects.invExt)
    (hD : st.currentDequeuedUniqueExcept e) (hNC : st.currentNowhere tid)
    (hNQ : ∀ c, st.queuedOn c tid = false) (hNI : Kernel.isIdleThreadId tid = false)
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hCo : ∀ x, st.getTcb? tid = some x → (f x).Coherent) :
    (st.updateTcb tid f).currentDequeuedUniqueExcept e := by
  have hNe : ∀ u, u ≠ tid → (st.updateTcb tid f).getTcb? u = st.getTcb? u := fun u hu =>
    updateTcb_getTcb?_ne _ _ _ hInv u (fun h => hu (ThreadId.toObjId_injective _ _ h).symm)
  refine currentDequeuedUniqueExcept_of_offWrite hD hNC hNQ (by rw [updateTcb_scheduler])
    (fun c x => by
      unfold SystemState.updateTcb; split
      · rename_i t hT _; exact runLinkOn_rewriteObject_tcb _ hInv hT (hf t) c x
      · rfl) hNI (fun u hu => ?_) (fun u c' hu hh y hy => hh y (by rw [← hNe u hu]; exact hy)) (fun y hy => ?_)
  · refine ⟨fun ⟨x, hx, hr⟩ => ⟨x, by rw [hNe u hu]; exact hx, hr⟩,
      fun hc x hx => hc x (by rw [← hNe u hu]; exact hx),
      fun ⟨x, hx, ha⟩ => ⟨x, by rw [hNe u hu]; exact hx, ha⟩⟩
  · rw [updateTcb_getTcb?_self _ _ _ hInv] at hy
    cases hT : st.getTcb? tid with
    | none => rw [hT] at hy; cases hy
    | some x => rw [hT] at hy; cases hy; exact hCo x hT

/-- **An object stored over a thread no core runs and no queue holds** — the
destroy path's retype of a descheduled thread: the thread is gone, every other
thread keeps its TCB, and a TCB stored in its place is coherent.  The property
holds whatever point is open, the destroyed thread being no idle thread. -/
theorem currentDequeuedUniqueExcept_insert_offTcb {st st' : SystemState}
    {e : Option SchedPoint} {k : SeLe4n.ObjId} {obj : KernelObject} {x : TCB}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k obj)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode)
    (hL : ∀ c u, st'.runLinkOn c u = st.runLinkOn c u)
    (hk : x.tid.toObjId = k)
    (hD : st.currentDequeuedUniqueExcept e) (hNC : st.currentNowhere x.tid)
    (hNQ : ∀ c, st.queuedOn c x.tid = false) (hNI : Kernel.isIdleThreadId x.tid = false)
    (hNew : ∀ y, objTcb? (some obj) = some y → y.Coherent) :
    st'.currentDequeuedUniqueExcept e := by
  have key : ∀ t, st'.getTcb? t =
      if k = t.toObjId then objTcb? (some obj) else st.getTcb? t := fun t => by
    rw [getTcb?_eq_objTcb?, getTcb?_eq_objTcb?, hO]
    simp only [RHTable_getElem?_eq_get?]
    split
    · rename_i hk; subst hk; rw [RHTable.getElem?_insert_self st.objects _ obj hInv]
    · rename_i hk
      rw [RHTable.getElem?_insert_ne st.objects _ _ obj (fun hb => hk (eq_of_beq hb)) hInv]
  have hNe : ∀ u, u ≠ x.tid → st'.getTcb? u = st.getTcb? u := fun u hu => by
    rw [key, if_neg (fun h => hu (ThreadId.toObjId_injective _ _ (hk.trans h)).symm)]
  refine currentDequeuedUniqueExcept_of_offWrite hD hNC hNQ hC hL hNI (fun u hu => ?_)
    (fun u c' hu hh y hy => hh y (by rw [← hNe u hu]; exact hy)) (fun y hy => ?_)
  · refine ⟨fun ⟨z, hz, hr⟩ => ⟨z, by rw [hNe u hu]; exact hz, hr⟩,
      fun hc z hz => hc z (by rw [← hNe u hu]; exact hz),
      fun ⟨z, hz, ha⟩ => ⟨z, by rw [hNe u hu]; exact hz, ha⟩⟩
  · rw [key, if_pos hk.symm] at hy
    exact hNew y hy

/-- A typed read-modify-write keeping a thread's run-queue entries keeps
every thread's. -/
theorem updateTcb_runLinkOn {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (c : CoreId) (x : SeLe4n.ThreadId) :
    (st.updateTcb tid f).runLinkOn c x = st.runLinkOn c x := by
  unfold SystemState.updateTcb; split
  · rename_i t hT _; exact runLinkOn_rewriteObject_tcb _ hInv hT (hf t) c x
  · rfl

/-- Two typed read-modify-writes of a thread off every core and every queue,
leaving it coherent: the property holds whatever point is open.  The suspend's
pending-state clear and `.Inactive` mark are one. -/
theorem currentDequeuedUniqueExcept_updateTcb₂_offWrite {st : SystemState}
    {e : Option SchedPoint} {tid : SeLe4n.ThreadId} {f g : TCB → TCB}
    (hInv : st.objects.invExt) (hD : st.currentDequeuedUniqueExcept e)
    (hNC : st.currentNowhere tid) (hNQ : ∀ c, st.queuedOn c tid = false)
    (hNI : Kernel.isIdleThreadId tid = false)
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hg : ∀ x c, (g x).runLinkOn c = x.runLinkOn c)
    (hCo : ∀ x, st.getTcb? tid = some x → (g (f x)).Coherent) :
    ((st.updateTcb tid f).updateTcb tid g).currentDequeuedUniqueExcept e := by
  have hInv1 := updateTcb_preserves_objects_invExt st tid f hInv
  have hNe : ∀ u, u ≠ tid → ((st.updateTcb tid f).updateTcb tid g).getTcb? u = st.getTcb? u :=
    fun u hu => by
      have hne : tid.toObjId ≠ u.toObjId := fun h => hu (ThreadId.toObjId_injective _ _ h).symm
      rw [updateTcb_getTcb?_ne _ _ _ hInv1 u hne, updateTcb_getTcb?_ne _ _ _ hInv u hne]
  refine currentDequeuedUniqueExcept_of_offWrite hD hNC hNQ
    (by rw [updateTcb_scheduler, updateTcb_scheduler])
    (fun c x => by rw [updateTcb_runLinkOn hInv1 hg, updateTcb_runLinkOn hInv hf]) hNI
    (fun u hu => ?_) (fun u c' hu hh y hy => hh y (by rw [← hNe u hu]; exact hy)) (fun y hy => ?_)
  · refine ⟨fun ⟨x, hx, hr⟩ => ⟨x, by rw [hNe u hu]; exact hx, hr⟩,
      fun hc x hx => hc x (by rw [← hNe u hu]; exact hx),
      fun ⟨x, hx, ha⟩ => ⟨x, by rw [hNe u hu]; exact hx, ha⟩⟩
  · rw [updateTcb_getTcb?_self _ _ _ hInv1, updateTcb_getTcb?_self _ _ _ hInv] at hy
    cases hT : st.getTcb? tid with
    | none => rw [hT] at hy; cases hy
    | some x => rw [hT] at hy; cases hy; exact hCo x hT

theorem runRemoveOnCore_current (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).scheduler.currentCode = st.scheduler.currentCode := by
  unfold runRemoveOnCore; dsimp only; split <;>
    simp [runUnlinkLinks_scheduler, SchedulerState.setRunQueueOnCore,
      SchedulerState.setRunQueueEndsOnCore]

/-- The run-queue entry an object slot gives a thread on core `c`: a TCB's, or
the empty entry for any other slot. -/
def objRunLinkOn : Option KernelObject → CoreId → RunQueueLink
  | some (.tcb t), c => t.runLinkOn c
  | _, _ => RunQueue.RunQueueLink.none

theorem runLinkOn_eq_objRunLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    st.runLinkOn c t = objRunLinkOn st.objects[t.toObjId]? c := by
  unfold runLinkOn getTcb?
  cases h : st.objects[t.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- **One object write keeps every thread's run-queue entry** when the object
stored gives the same entries as the one it replaces: a TCB whose run-queue
fields are the old TCB's, or any other object over any other object. -/
theorem runLinkOn_insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k obj)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (c : CoreId) (t : SeLe4n.ThreadId) : st'.runLinkOn c t = st.runLinkOn c t := by
  rw [runLinkOn_eq_objRunLinkOn, runLinkOn_eq_objRunLinkOn, hO]
  by_cases hk : k = t.toObjId
  · subst hk
    simp only [RHTable_getElem?_eq_get?] at h ⊢
    rw [RHTable.getElem?_insert_self st.objects _ obj hInv]
    exact h c
  · simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne st.objects _ _ obj (fun hb => hk (eq_of_beq hb)) hInv]

/-- The link half of a one-object write giving the same run-queue entries, and
no run queue or end, with the table references carried by `hTab` — whatever the
object's state fields, so it holds of a write that moves a thread's home too
(the affinity change). -/
theorem RunQueueLinkStage.insertWith {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject}
    (hO : st'.objects = st.objects.insert k obj)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hTab : st.objects.invExt → st.tableReferencesRecorded → st'.tableReferencesRecorded)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hV : objRefillView (some obj) = objRefillView st.objects[k]? := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueLinkStage st st' :=
  ⟨fun hInv r => ⟨hO ▸ RHTable_insert_preserves_invExt st.objects k obj hInv,
    runQueueRefined_of_frame (runLinkOn_insert hInv hO h) hQ hE r⟩, fun hInv _ t => hTab hInv t,
    fun hInv _ q => (show releaseStateAgree st' st from ⟨.insert hInv hO hR, hS⟩).refined q,
    fun _ hInv _ q s => refillsSoundExcept_of_kept (.insert hInv hO hV)
      (fun c => by rw [(show releaseStateAgree st' st from ⟨.insert hInv hO hR, hS⟩).replenishQueueOnCore c])
      ((show releaseStateAgree st' st from ⟨.insert hInv hO hR, hS⟩).refined q) s,
    fun hInv _ y => yieldLinksAgree_of_kept (.insert hInv hO hY) y,
    fun hInv _ => .of_kept (.insert hInv hO hY) hRes⟩

/-- ...holding the slot's table back-links and every reference table. -/
theorem RunQueueLinkStage.insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hO : st'.objects = st.objects.insert k obj)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]? := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hV : objRefillView (some obj) = objRefillView st.objects[k]? := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueLinkStage st st' :=
  .insertWith hO hQ hE h (fun hInv t => (TableReferenceFrame.insert hInv hO hT hB).preserves t)
    hR hV hY hS hRes

/-- A step that writes one object giving the same run-queue entries, and no
run queue or end, with the table references carried by `hTab`: the store
primitive both the frame (`RunQueueStage.insert`) and a registry writer, which
writes an endpoint's back-link, are built on. -/
theorem RunQueueStage.insertWith {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hO : st'.objects = st.objects.insert k obj)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hm : objStateMono st.objects[k]? obj)
    (hTab : st.objects.invExt → st.tableReferencesRecorded → st'.tableReferencesRecorded)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hV : objRefillView (some obj) = objRefillView st.objects[k]? := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  ⟨RunQueueLinkStage.insertWith hO hQ hE h hTab hR hV hY hS hRes,
    fun _ hInv _ _ d => currentDequeuedUniqueExcept_of_eq hC (runLinkOn_insert hInv hO h)
      (StateMono.insert hInv hO hm) d, fun hInv _ => StateMono.insert hInv hO hm⟩

/-- A step that writes one object giving the same run-queue entries and holding
the slot's table back-links, and no run queue, end or reference table. -/
theorem RunQueueStage.insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hO : st'.objects = st.objects.insert k obj)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hm : objStateMono st.objects[k]? obj)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]? := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hV : objRefillView (some obj) = objRefillView st.objects[k]? := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  .insertWith hO hQ hE h hm (fun hInv t => (TableReferenceFrame.insert hInv hO hT hB).preserves t) hC
    hR hV hY hS hRes

/-- WS-ZA ZA6.4: **a one-object write that may change a context's refills is
a frame stage** — the store of `RunQueueStage.insert` with no claim on the refill
view: a context's charge, bind, unbind or configure, whose composite proves its
refills (`RunQueueFrameStage.withRefills`). -/
theorem RunQueueFrameStage.insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hO : st'.objects = st.objects.insert k obj)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hm : objStateMono st.objects[k]? obj)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]? := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueFrameStage (· = SeLe4n.SchedContextId.ofObjId k) st st' :=
  ⟨⟨fun hInv r => ⟨hO ▸ RHTable_insert_preserves_invExt st.objects k obj hInv,
      runQueueRefined_of_frame (runLinkOn_insert hInv hO h) hQ hE r⟩,
    fun hInv _ t => (TableReferenceFrame.insert hInv hO hT hB).preserves t,
    fun hInv _ q => (show releaseStateAgree st' st from ⟨.insert hInv hO hR, hS⟩).refined q,
    fun S hP hInv _ q x => refillsSoundExcept_of_keptOff
      (RefillsKeptOff.of_insert (s := SeLe4n.SchedContextId.ofObjId k) hInv
        (by rw [SeLe4n.SchedContextId.toObjId_ofObjId]; exact hO)
        (fun c => by rw [(show releaseStateAgree st' st from ⟨.insert hInv hO hR, hS⟩).replenishQueueOnCore c]))
      hP ((show releaseStateAgree st' st from ⟨.insert hInv hO hR, hS⟩).refined q) x,
    fun hInv _ y => yieldLinksAgree_of_kept (.insert hInv hO hY) y,
    fun hInv _ => .of_kept (.insert hInv hO hY) hRes⟩,
    fun _ hInv _ _ d => currentDequeuedUniqueExcept_of_eq hC (runLinkOn_insert hInv hO h)
      (StateMono.insert hInv hO hm) d, fun hInv _ => StateMono.insert hInv hO hm⟩

/-- A store keeping the slot's run-queue entries and release links is a frame
stage off the slot's context: its refills are closed by a later step. -/
theorem RunQueueFrameStage.storeObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hm : objStateMono st.objects[k]? obj)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]? := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes) :
    RunQueueFrameStage (· = SeLe4n.SchedContextId.ofObjId k) st st' := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact RunQueueFrameStage.insert rfl rfl rfl h hm rfl rfl hB hR hY

/-- WS-ZA ZA6.4: **a context created in an empty slot** — unbound and well
formed — is a stage: no entry names the slot (its pre-state holds no context),
and an unbound context strands no refill. -/
theorem RunQueueStage.insert_freshContext {st st' : SystemState} {k : SeLe4n.ObjId}
    {u : SchedContext} (hO : st'.objects = st.objects.insert k (.schedContext u))
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hNone : st.objects[k]? = none)
    (hU : u.boundThread.isSome = false) (hWF : schedContextWellFormed u)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hT : st'.referenceTables = st.referenceTables := by table_frame)
    (hB : (KernelObject.schedContext u).tableBackLinks = objTableBackLinks st.objects[k]? := by
      table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some (.schedContext u)) c = objReleaseLinkOn st.objects[k]? c := by
      release_links)
    (hY : u.yieldFromCode = 0 := by first | rfl | assumption)
    (hS : st'.scheduler.releaseSlots = st.scheduler.releaseSlots := by release_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  (RunQueueFrameStage.insert hO hQ hE (fun c => by rw [hNone]; rfl)
    (by rw [hNone]; exact objStateMono_nonTcb rfl rfl) hC hT hB hR
    (by rw [hNone]; simp only [objYieldCodes, hY]) hS hRes).withRefills
    fun _ _ hI _ hRel _ _ _ h4 => refillsSoundExcept_close_unbound h4
      (fun a ha => by
        have e : (st.objects.insert k (.schedContext u))[k]? = some (.schedContext u) :=
          RobinHood.RHTable.getElem?_insert_self st.objects k _ hI
        rw [getSchedContext?_eq_some_iff, SeLe4n.SchedContextId.toObjId_ofObjId, hO, e] at ha
        cases ha; rfl)
      hU hWF (fun c e he hs => by
        rw [(show releaseStateAgree st' st from ⟨.insert hI hO hR, hS⟩).replenishQueueOnCore c] at he
        obtain ⟨a, ha⟩ := releaseQueueRefined_getSchedContext?_of_mem hRel he
        rw [hs, getSchedContext?_eq_some_iff, SeLe4n.SchedContextId.toObjId_ofObjId, hNone] at ha
        cases ha)

/-- A TCB's run-queue entries are read off its placement fields. -/
theorem _root_.SeLe4n.Model.TCB.runLinkOn_of_placement {a b : TCB}
    (h : a.placement = b.placement) (c : CoreId) : a.runLinkOn c = b.runLinkOn c := by
  simp only [TCB.placement, TcbPlacement.mk.injEq] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  unfold TCB.runLinkOn TCB.runLink
  rw [h1, h2, h3, h4, h5, h6]

/-- A placement frame (`TCB.placement`) keeps every thread's run-queue entries. -/
theorem runLinkOn_of_placement {st st' : SystemState}
    (h : ∀ x, (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement)
    (c : CoreId) (t : SeLe4n.ThreadId) : st'.runLinkOn c t = st.runLinkOn c t := by
  have ht := h t
  unfold runLinkOn
  cases h1 : st'.getTcb? t <;> cases h2 : st.getTcb? t <;>
    simp only [h1, h2, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at ht ⊢
  exact TCB.runLinkOn_of_placement ht c

/-- **A step that writes no run queue and moves no thread** — every TCB write a
record update outside the placement fields — keeps the agreement.  The
IPC teardowns, the donation hand-backs and the pending-state clears are of this
shape; their placement frames are the cancellation path's
(`cancelIpcBlocking_placement_frame`). -/
theorem RunQueueStage.of_placement {st st' : SystemState}
    (hInv : st.objects.invExt → st'.objects.invExt)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hP : st.objects.invExt → ∀ x,
      (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement)
    (hM : st.objects.invExt → StateMono st st')
    (hF : st.objects.invExt → TableReferenceFrame st st')
    (hRel : st.objects.invExt → releaseStateAgree st' st)
    (hV : st.objects.invExt → RefillViewsKept st' st)
    (hY : st.objects.invExt → YieldLinksKept st' st)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueStage st st' :=
  ⟨.of_tableFrame
    (fun h r => ⟨hInv h, runQueueRefined_of_frame (runLinkOn_of_placement (hP h)) hQ hE r⟩) hF hRel
    hV hY hRes,
    fun _ h _ _ d => currentDequeuedUniqueExcept_of_eq hC (runLinkOn_of_placement (hP h)) (hM h) d,
    fun h _ => hM h⟩

/-- `RunQueueStage.of_placement` for a step that writes the contexts in `P`:
the refills are kept off `P` only, so the step is a frame stage off `P`. -/
theorem RunQueueFrameStage.of_placement {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (hInv : st.objects.invExt → st'.objects.invExt)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (hP : st.objects.invExt → ∀ x,
      (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement)
    (hM : st.objects.invExt → StateMono st st')
    (hF : st.objects.invExt → TableReferenceFrame st st')
    (hRel : st.objects.invExt → releaseStateAgree st' st)
    (hK : st.objects.invExt → RefillsKeptOff P st' st)
    (hY : st.objects.invExt → YieldLinksKept st' st)
    (hC : st'.scheduler.currentCode = st.scheduler.currentCode := by current_frame)
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame) :
    RunQueueFrameStage P st st' :=
  ⟨⟨fun h r => ⟨hInv h, runQueueRefined_of_frame (runLinkOn_of_placement (hP h)) hQ hE r⟩,
    fun h _ t => (hF h).preserves t, fun h _ r => (hRel h).refined r,
    fun _ hS h _ q x => refillsSoundExcept_of_keptOff (hK h) hS ((hRel h).refined q) x,
    fun h _ y => yieldLinksAgree_of_kept (hY h) y, fun h _ => .of_kept (hY h) hRes⟩,
    fun _ h _ _ d => currentDequeuedUniqueExcept_of_eq hC (runLinkOn_of_placement (hP h)) (hM h) d,
    fun h _ => hM h⟩

/-- **One object store that gives every thread the run-queue entries the
replaced slot gave** keeps the agreement: a TCB stored over a TCB with the same
run-queue fields, or any other object stored over any other object. -/
theorem RunQueueStage.storeObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hm : objStateMono st.objects[k]? obj)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]? := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hV : objRefillView (some obj) = objRefillView st.objects[k]? := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes) :
    RunQueueStage st st' := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact RunQueueStage.insert rfl rfl rfl h hm rfl rfl hB hR hV hY

/-- A store keeping the run-queue entry its slot gives keeps the link agreement. -/
theorem RunQueueLinkStage.storeObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c)
    (hB : obj.tableBackLinks = objTableBackLinks st.objects[k]? := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn st.objects[k]? c := by release_links)
    (hV : objRefillView (some obj) = objRefillView st.objects[k]? := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes st.objects[k]? := by yield_codes) :
    RunQueueLinkStage st st' := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact .of_tableFrame (fun hInv r => ⟨RHTable_insert_preserves_invExt st.objects k obj hInv,
    runQueueRefined_of_frame (runLinkOn_insert hInv rfl h) rfl rfl r⟩)
    (fun hInv => .insert hInv rfl rfl hB) (fun hInv => ⟨.insert hInv rfl hR, rfl⟩)
    (fun hInv => .insert hInv rfl hV) fun hInv => .insert hInv rfl hY

/-- The store of an object other than a TCB over an object other than a TCB. -/
theorem RunQueueStage.storeObject_nonTcb {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj old : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (hOld : st.objects[k]? = some old)
    (hObj : ∀ t, obj ≠ .tcb t) (hOldT : ∀ t, old ≠ .tcb t)
    (hB : obj.tableBackLinks = old.tableBackLinks := by table_backlinks)
    (hR : ∀ c, objReleaseLinkOn (some obj) c = objReleaseLinkOn (some old) c := by release_links)
    (hV : objRefillView (some obj) = objRefillView (some old) := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes (some old) := by yield_codes) :
    RunQueueStage st st' :=
  RunQueueStage.storeObject (hB := by rw [hOld]; exact hB) (hR := by rw [hOld]; exact hR)
    (hV := by rw [hOld]; exact hV) (hY := by rw [hOld]; exact hY) hS (fun c => by
    rw [hOld]
    cases obj <;> cases old <;> first | rfl | exact absurd rfl (hObj _) | exact absurd rfl (hOldT _))
    (objStateMono_nonTcb (by rw [hOld]; cases old <;> first | rfl | exact absurd rfl (hOldT _))
      (by cases obj <;> first | rfl | exact absurd rfl (hObj _)))

/-- The store of a TCB over a TCB with the same run-queue fields. -/
theorem RunQueueStage.storeObject_tcb {st st' : SystemState} {k : SeLe4n.ObjId}
    {t old : TCB} (hS : SeLe4n.Model.storeObject k (.tcb t) st = .ok ((), st'))
    (hOld : st.objects[k]? = some (.tcb old)) (h : ∀ c, t.runLinkOn c = old.runLinkOn c)
    (hm : objStateMono (some (.tcb old)) (.tcb t) := by obj_state_mono)
    (hW : t.taintWords = old.taintWords := by taint_words_kept)
    (hYc : t.yieldToCode = old.yieldToCode := by first | rfl | simp_all) :
    RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by rw [hOld]; exact h c) (by rw [hOld]; exact hm)
    (by rw [hOld]; simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hW])
    (fun _ => by rw [hOld]; rfl) (by rw [hOld]; rfl) (by rw [hOld]; simp only [objYieldCodes, hYc])


/-- **The block write**: a TCB stored over core `c`'s current thread `t` that
keeps its run-queue links and its thread state — the IPC state store that
blocks it — keeps `c`'s block point open, `t` being no idle thread. -/
theorem RunQueueWindowStage.storeObject_block {st st' : SystemState} {c : CoreId}
    {t : SeLe4n.ThreadId} {old new : TCB}
    (hS : SeLe4n.Model.storeObject t.toObjId (.tcb new) st = .ok ((), st'))
    (hOld : st.getTcb? t = some old) (h : ∀ c, new.runLinkOn c = old.runLinkOn c)
    (hT : new.threadState = old.threadState)
    (hCur : st.scheduler.currentOnCore c = some t) (hNI : Kernel.isIdleThreadId t = false)
    (hW : new.taintWords = old.taintWords := by taint_words_kept)
    (hAff : new.cpuAffinity = old.cpuAffinity := by first | rfl | simp_all)
    (hYc : new.yieldToCode = old.yieldToCode := by first | rfl | simp_all) :
    RunQueueWindowStage (.block c) st st' := by
  have hO : st'.objects = st.objects.insert t.toObjId (.tcb new) := by
    unfold SeLe4n.Model.storeObject at hS; cases hS; rfl
  have hSc : st'.scheduler = st.scheduler := by
    unfold SeLe4n.Model.storeObject at hS; cases hS; rfl
  have hRaw : st.objects[t.toObjId]? = some (.tcb old) := (getTcb?_eq_some_iff st t old).mp hOld
  have hLk : ∀ c, objRunLinkOn (some (KernelObject.tcb new)) c =
      objRunLinkOn st.objects[t.toObjId]? c := fun c => by rw [hRaw]; exact h c
  have hTb : st'.referenceTables = st.referenceTables := by
    unfold SeLe4n.Model.storeObject at hS; cases hS; rfl
  refine ⟨.of_tableFrame (fun hInv r => ⟨hO ▸ RHTable_insert_preserves_invExt st.objects _ _ hInv,
    runQueueRefined_of_frame (runLinkOn_insert hInv hO hLk) (by rw [hSc]) (by rw [hSc]) r⟩)
    (fun hInv => .insert hInv hO hTb (by
      rw [hRaw]; simp only [objTableBackLinks_some, KernelObject.tableBackLinks, hW]))
    (fun hInv => ⟨.insert hInv hO (fun _ => by rw [hRaw]; rfl), by rw [hSc]⟩)
    (fun hInv => .insert hInv hO (by rw [hRaw]; rfl))
    (fun hInv => .insert hInv hO (by rw [hRaw]; simp only [objYieldCodes, hYc]))
    (by unfold SeLe4n.Model.storeObject at hS; cases hS; rfl),
    fun hInv _ _ d => ?_⟩
  have hGet : ∀ u, st'.getTcb? u = if u = t then some new else st.getTcb? u := fun u => by
    rw [getTcb?_eq_objTcb?, getTcb?_eq_objTcb? st u, hO]
    simp only [RHTable_getElem?_eq_get?]
    split
    · rename_i hu; subst hu; rw [RHTable.getElem?_insert_self st.objects _ _ hInv]; rfl
    · rename_i hu
      rw [RHTable.getElem?_insert_ne st.objects _ _ _ (fun hb => hu
        (ThreadId.toObjId_injective _ _ (eq_of_beq hb)).symm) hInv]
  refine currentDequeuedUniqueExcept_of_block d hCur (by rw [hSc]) (runLinkOn_insert hInv hO hLk)
    hNI (fun u hu => ?_) (fun u c' hh y hy => ?_) ?_
  · have e : st'.getTcb? u = st.getTcb? u := by rw [hGet, if_neg hu]
    refine ⟨fun ⟨x, hx, hr⟩ => ⟨x, by rw [e]; exact hx, hr⟩,
      fun hc x hx => hc x (by rw [← e]; exact hx),
      fun ⟨x, hx, ha⟩ => ⟨x, by rw [e]; exact hx, ha⟩⟩
  · rw [hGet] at hy
    split at hy
    · rename_i hu; subst hu; cases hy; rw [hAff]; exact hh old hOld
    · exact hh y hy
  · obtain ⟨x, hx, ha⟩ := d.currentActive c t hCur
    rw [hOld] at hx; cases hx
    exact ⟨new, by rw [hGet, if_pos rfl], by unfold TCB.Active; rw [hT]; exact ha⟩

end SeLe4n.Model.SystemState
