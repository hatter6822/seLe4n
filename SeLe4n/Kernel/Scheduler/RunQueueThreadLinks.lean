-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAt

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

theorem TCB.runLinkOn_clearCore (tcb : TCB) (c : CoreId) :
    ({ tcb with runCoreCode := 0 } : TCB).runLinkOn c = RunQueue.RunQueueLink.none := by
  unfold TCB.runLinkOn; rw [if_neg (fun h => by simp at h)]

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
def _root_.SeLe4n.Model.KernelObject.mapTcb (g : TCB → TCB) : KernelObject → KernelObject
  | .tcb x => .tcb (g x)
  | o => o

/-- WS-ZA ZA4.5: rewrite thread `t`'s TCB through `g` **in its slot**
(`RHTable.mapValueAt`): no probe, no resize, no key moved, so the frame holds
on every object table (`objects_mapTcbInPlace`).  The run queue's link writes
go through it; a key holding no TCB is left as it is. -/
def mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) : SystemState :=
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
def updateTcbAtCode (st : SystemState) (k : Nat) (g : TCB → TCB) : SystemState :=
  if k = 0 then st else st.mapTcbInPlace (decode k) g

theorem updateTcbAtCode_objects_invExt (st : SystemState) (k : Nat) (g : TCB → TCB)
    (hInv : st.objects.invExt) : (st.updateTcbAtCode k g).objects.invExt := by
  unfold updateTcbAtCode; split
  · exact hInv
  · exact mapTcbInPlace_objects_invExt _ _ _ hInv

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

/-- WS-ZA ZA4.5: thread `t` joins the back of core `c`'s queue at priority `p`,
as the threads and the core hold it (`runAppendLinks`, `RunQueueEnds.append`). -/
def runAppendOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st3 := st.runAppendLinks c t p
  let e' := (st3.scheduler.runQueueEndsOnCore c).append t p
  { st3 with scheduler := st3.scheduler.setRunQueueEndsOnCore c e' }

/-- WS-ZA ZA4.5: enqueue `t` on core `c` at priority `p` — `RunQueue.insert` on
the core's queue, written through the threads; a thread already queued there is
left where it is. -/
def runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st' := if (st.runLinkOn c t).queued then st else st.runAppendOnCore c t p
  let rq := (st'.scheduler.runQueueOnCore c).insert t p
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

theorem runAppendLinks_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runAppendLinks c t p).scheduler = st.scheduler := by
  simp only [runAppendLinks, updateTcbAtCode_scheduler, mapTcbInPlace_scheduler]

theorem runAppendOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runAppendOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runAppendOnCore
  rw [SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runAppendLinks_scheduler]

theorem runEnqueueOnCore_runQueueOnCore_self (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c =
      (st.scheduler.runQueueOnCore c).insert t p := by
  unfold runEnqueueOnCore
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  split
  · rfl
  · rw [runAppendOnCore_runQueueOnCore]

theorem runEnqueueOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (h : c ≠ c') :
    (st.runEnqueueOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runEnqueueOnCore
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
  split
  · rfl
  · rw [runAppendOnCore_runQueueOnCore]

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
  cases s; simp [Vector.get]

/-- WS-ZA ZA4.5: enqueueing a TCB that is on no other core's queue keeps every
core's queue in agreement with the threads. -/
theorem runEnqueueOnCore_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (hR : st.runQueueRefined) 
    (hT : (st.getTcb? t).isSome)
    (hOther : ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false) :
    (st.runEnqueueOnCore c t p).runQueueRefined := by
  unfold runEnqueueOnCore
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
towards the other, and `t` is marked on no core.  As `RunQueue.unlinkLinks`. -/
def runUnlinkLinks (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) : SystemState :=
  let st1 := st.updateTcbAtCode pv (fun y => { y with runNextCode := nx })
  let st2 := st1.updateTcbAtCode nx (fun y => { y with runPrevCode := pv })
  let st3 := st2.updateTcbAtCode bpv (fun y => { y with runBucketNextCode := bnx })
  let st4 := st3.updateTcbAtCode bnx (fun y => { y with runBucketPrevCode := bpv })
  st4.mapTcbInPlace t (fun y => { y with runCoreCode := 0 })

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
      (fun tcb => TCB.runLinkOn_clearCore tcb c) rfl,
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

-- ============================================================================
-- Stages
-- ============================================================================

/-- WS-ZA ZA4.5: **a step that keeps the run queues in agreement with the
threads' links** — from a state whose object store keeps its table invariant
and whose queues agree with the links, it reaches such a state.  Stages compose
(`RunQueueStage.trans`), so a transition's agreement proof is the composition
of its steps' stages. -/
def RunQueueStage (st st' : SystemState) : Prop :=
  st.objects.invExt → st.runQueueRefined → st'.objects.invExt ∧ st'.runQueueRefined

theorem RunQueueStage.refl (st : SystemState) : RunQueueStage st st := fun h r => ⟨h, r⟩

theorem RunQueueStage.trans {st st' st'' : SystemState}
    (h1 : RunQueueStage st st') (h2 : RunQueueStage st' st'') : RunQueueStage st st'' :=
  fun h r => (h1 h r).elim h2

theorem RunQueueStage.of_eq {st st' : SystemState} (h : st' = st) : RunQueueStage st st' :=
  h ▸ RunQueueStage.refl st

/-- A step that writes neither the objects nor the run queues and their ends. -/
theorem RunQueueStage.of_frame {st st' : SystemState} (hO : st'.objects = st.objects)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds) : RunQueueStage st st' :=
  fun h r => ⟨hO ▸ h, runQueueRefined_of_frame (fun c t => runLinkOn_of_objects hO c t) hQ hE r⟩

theorem RunQueueStage.updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c) : RunQueueStage st (st.updateTcb tid f) :=
  fun h r => ⟨updateTcb_preserves_objects_invExt st tid f h, updateTcb_runQueueRefined h hf r⟩

theorem RunQueueStage.runRemoveOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    RunQueueStage st (st.runRemoveOnCore c t) :=
  fun h r => ⟨runRemoveOnCore_objects_invExt st c t h, runRemoveOnCore_refined r⟩

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

/-- A step that writes one object giving the same run-queue entries, and no
run queue or end. -/
theorem RunQueueStage.insert {st st' : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hO : st'.objects = st.objects.insert k obj)
    (hQ : st'.scheduler.runQueue = st.scheduler.runQueue)
    (hE : st'.scheduler.runQueueEnds = st.scheduler.runQueueEnds)
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c) :
    RunQueueStage st st' :=
  fun hInv r => ⟨hO ▸ RHTable_insert_preserves_invExt st.objects k obj hInv,
    runQueueRefined_of_frame (runLinkOn_insert hInv hO h) hQ hE r⟩

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
      (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement) :
    RunQueueStage st st' :=
  fun h r => ⟨hInv h, runQueueRefined_of_frame (runLinkOn_of_placement (hP h)) hQ hE r⟩

/-- **One object store that gives every thread the run-queue entries the
replaced slot gave** keeps the agreement: a TCB stored over a TCB with the same
run-queue fields, or any other object stored over any other object. -/
theorem RunQueueStage.storeObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (h : ∀ c, objRunLinkOn (some obj) c = objRunLinkOn st.objects[k]? c) :
    RunQueueStage st st' := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact RunQueueStage.insert rfl rfl rfl h

/-- The store of an object other than a TCB over an object other than a TCB. -/
theorem RunQueueStage.storeObject_nonTcb {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj old : KernelObject} (hS : SeLe4n.Model.storeObject k obj st = .ok ((), st'))
    (hOld : st.objects[k]? = some old)
    (hObj : ∀ t, obj ≠ .tcb t) (hOldT : ∀ t, old ≠ .tcb t) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by
    rw [hOld]
    cases obj <;> cases old <;> first | rfl | exact absurd rfl (hObj _) | exact absurd rfl (hOldT _))

/-- The store of a TCB over a TCB with the same run-queue fields. -/
theorem RunQueueStage.storeObject_tcb {st st' : SystemState} {k : SeLe4n.ObjId}
    {t old : TCB} (hS : SeLe4n.Model.storeObject k (.tcb t) st = .ok ((), st'))
    (hOld : st.objects[k]? = some (.tcb old)) (h : ∀ c, t.runLinkOn c = old.runLinkOn c) :
    RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by rw [hOld]; exact h c)

end SeLe4n.Model.SystemState
