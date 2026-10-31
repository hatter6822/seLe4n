/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame

/-!
# The run queue's head enqueue (WS-ZA ZA6.9)

seL4 has two run-queue inserts: `tcbSchedAppend` puts a thread at the back of
its priority band and `tcbSchedEnqueue` at the front.  `runEnqueueOnCore` is
the first; this module adds the second, `runEnqueueHeadOnCore`, which
`seL4_SchedContext_YieldTo` uses to put the context's thread (and, when it
yields, the caller behind it) ahead of the band.

The thread joins ahead of its core's first queued thread and ahead of its
bucket's first (`runPrependLinks`), the core's ends move
(`RunQueueEnds.prepend`), and the queue the scheduler carries is
`RunQueue.insertHead`.  The admission guard is the append's
(`runEnqueueAdmits`): a thread on another core's queue, an idle thread and a
non-thread are not queued, and a thread already queued here is left where it
is, as seL4's `tcbSchedEnqueue` leaves a thread whose `tcbQueued` bit is set.
-/

namespace SeLe4n.Model.SystemState
open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.LinkedQueue
open SeLe4n.Kernel.Concurrency (CoreId)

/-- Thread `t` joins the front of core `c`'s queue at priority `p`, as the
threads hold it: `t`'s TCB takes the core, the bucket and its links (ahead of
the queue's first thread and its bucket's first), and those two point back at
`t`.  For a thread on no queue; `runEnqueueHeadOnCore` is the guarded form. -/
def runPrependLinks (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let e := st.scheduler.runQueueEndsOnCore c
  let bhead := (RunQueue.endsOf e.buckets p).head
  let st1 := st.mapTcbInPlace t (fun x => { x with
    runCoreCode := c.val + 1, runPrio := p, runPrevCode := 0, runNextCode := e.head,
    runBucketPrevCode := 0, runBucketNextCode := bhead })
  let st2 := st1.updateTcbAtCode e.head (fun x => { x with runPrevCode := code t })
  st2.updateTcbAtCode bhead (fun x => { x with runBucketPrevCode := code t })

/-- The code of the first thread in a queue's bucket for priority `p`. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.bucketHead (e : RunQueueEnds) (p : SeLe4n.Priority) : Nat :=
  (RunQueue.endsOf e.buckets p).head

/-- `runPrependLinks`'s three TCB writes, on the object table alone, given the
queue's and the bucket's first codes. -/
def prependLinkObjects (o : RHTable SeLe4n.ObjId KernelObject) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (qhead bhead : Nat) : RHTable SeLe4n.ObjId KernelObject :=
  let o1 := o.mapValueAt t.toObjId (KernelObject.mapTcb fun x => { x with
    runCoreCode := c.val + 1, runPrio := p, runPrevCode := 0, runNextCode := qhead,
    runBucketPrevCode := 0, runBucketNextCode := bhead })
  let o2 := if qhead = 0 then o1 else
    o1.mapValueAt (decode qhead).toObjId (KernelObject.mapTcb fun x => { x with runPrevCode := code t })
  if bhead = 0 then o2 else
    o2.mapValueAt (decode bhead).toObjId
      (KernelObject.mapTcb fun x => { x with runBucketPrevCode := code t })

/-- The compiled `runPrependLinks`: the two first codes are read first, then the
state record is rebuilt once around the table writes, so an exclusive state is
rewritten in place (the append's `runAppendLinksImpl` shape). -/
def runPrependLinksImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let e := st.scheduler.runQueueEndsOnCore c
  let qhead := e.head
  let bhead := e.bucketHead p
  { st with objects := prependLinkObjects st.objects c t p qhead bhead }

@[csimp] theorem runPrependLinks_eq_impl : @runPrependLinks = @runPrependLinksImpl := by
  funext st c t p
  unfold runPrependLinks runPrependLinksImpl prependLinkObjects RunQueueEnds.bucketHead
    updateTcbAtCode mapTcbInPlace
  dsimp only
  split <;> split <;> rfl

/-- The ends of a queue once `t` joins its front at priority `p`:
`RunQueue.insertHead`'s ends, read off the old ones. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.prepend (e : RunQueueEnds) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : RunQueueEnds :=
  let bhead := (RunQueue.endsOf e.buckets p).head
  { buckets := RunQueue.setEnds e.buckets p (RunQueue.prependEnds t bhead)
    head := code t
    tail := if e.head = 0 then code t else e.tail
    size := e.size + 1
    maxCode := max e.maxCode (p.val + 1) }

/-- The compiled `RunQueueEnds.prepend`: the ends taken apart before the bucket
table is rewritten, so exclusively owned ends are rewritten in place. -/
def _root_.SeLe4n.Kernel.RunQueueEnds.prependImpl (e : RunQueueEnds) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : RunQueueEnds :=
  match e with
  | ⟨b, h, tl, s, m⟩ =>
    let bhead := (RunQueue.endsOf b p).head
    ⟨RunQueue.setEnds b p (RunQueue.prependEnds t bhead), code t, if h = 0 then code t else tl,
      s + 1, max m (p.val + 1)⟩

@[csimp] theorem _root_.SeLe4n.Kernel.RunQueueEnds.prepend_eq_impl :
    @RunQueueEnds.prepend = @RunQueueEnds.prependImpl := by
  funext e t p; cases e; rfl

/-- Thread `t` joins the front of core `c`'s queue at priority `p`, as the
threads and the core hold it. -/
def runPrependOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st3 := st.runPrependLinks c t p
  let e' := (st3.scheduler.runQueueEndsOnCore c).prepend t p
  { st3 with scheduler := st3.scheduler.setRunQueueEndsOnCore c e' }

/-- The compiled `runPrependOnCore`: the core's ends rewritten in their slot. -/
def runPrependOnCoreImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st3 := st.runPrependLinks c t p
  { st3 with scheduler := st3.scheduler.modifyRunQueueEndsOnCore c (·.prepend t p) }

@[csimp] theorem runPrependOnCore_eq_impl : @runPrependOnCore = @runPrependOnCoreImpl := by
  funext st c t p
  simp only [runPrependOnCore, runPrependOnCoreImpl, SchedulerState.modifyRunQueueEndsOnCore_eq]

/-- The head enqueue of an admitted thread — `RunQueue.insertHead` on the
core's queue, written through the threads; a thread already queued there is
left where it is. -/
def runEnqueueHeadAdmitted (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st' := if (st.runLinkOn c t).queued then st else st.runPrependOnCore c t p
  let rq := (st'.scheduler.runQueueOnCore c).insertHead t p
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

/-- The compiled `runEnqueueHeadAdmitted`: membership read as the run-core
field (`queuedOn`), with no link record built. -/
def runEnqueueHeadAdmittedImpl (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  let st' := if st.queuedOn c t then st else st.runPrependOnCore c t p
  let rq := (st'.scheduler.runQueueOnCore c).insertHead t p
  { st' with scheduler := st'.scheduler.setRunQueueOnCore c rq }

@[csimp] theorem runEnqueueHeadAdmitted_eq_impl :
    @runEnqueueHeadAdmitted = @runEnqueueHeadAdmittedImpl := by
  funext st c t p
  simp only [runEnqueueHeadAdmitted, runEnqueueHeadAdmittedImpl, queuedOn_eq_runLinkOn]

/-- **seL4's `tcbSchedEnqueue`** (WS-ZA ZA6.9): enqueue `t` at the front of its
band on core `c` at priority `p`.  Admission is the append's
(`runEnqueueAdmits`): a thread queued on another core stays there, a
non-thread and an idle thread are not queued, and a thread already queued here
keeps its place. -/
def runEnqueueHeadOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : SystemState :=
  if st.runEnqueueAdmits c t then st.runEnqueueHeadAdmitted c t p else st

theorem runEnqueueHeadOnCore_of_admits {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = true) :
    st.runEnqueueHeadOnCore c t p = st.runEnqueueHeadAdmitted c t p := by
  unfold runEnqueueHeadOnCore; rw [if_pos h]

theorem runEnqueueHeadOnCore_of_not_admits {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    (p : SeLe4n.Priority) (h : st.runEnqueueAdmits c t = false) :
    st.runEnqueueHeadOnCore c t p = st := by
  unfold runEnqueueHeadOnCore; rw [if_neg (by simp [h])]


-- ============================================================================
-- Frames
-- ============================================================================

theorem runPrependLinks_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runPrependLinks c t p).scheduler = st.scheduler := by
  simp only [runPrependLinks, updateTcbAtCode_scheduler, mapTcbInPlace_scheduler]

theorem runPrependLinks_machine (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runPrependLinks c t p).machine = st.machine := by
  unfold runPrependLinks updateTcbAtCode mapTcbInPlace; dsimp only; split <;> split <;> rfl

theorem runPrependLinks_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    (st.runPrependLinks c t p).objects.invExt :=
  updateTcbAtCode_objects_invExt _ _ _ (updateTcbAtCode_objects_invExt _ _ _
    (mapTcbInPlace_objects_invExt _ _ _ hInv))

theorem runPrependLinks_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hK : st.objects.invExtK) :
    (st.runPrependLinks c t p).objects.invExtK :=
  updateTcbAtCode_objects_invExtK _ _ _ (updateTcbAtCode_objects_invExtK _ _ _
    (mapTcbInPlace_objects_invExtK _ _ _ hK))

theorem runPrependLinks_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runPrependLinks c t p) st := by
  unfold runPrependLinks
  exact .trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
      (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl)))

theorem runPrependLinks_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runPrependLinks c t p) st := by
  unfold runPrependLinks
  exact .trans (.updateTcbAtCode _ _ _) (.trans (.updateTcbAtCode _ _ _) (.mapTcbInPlace _ _ _))

theorem runEnqueueHeadAdmitted_objects (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueHeadAdmitted c t p).objects =
      if (st.runLinkOn c t).queued then st.objects else (st.runPrependLinks c t p).objects := by
  unfold runEnqueueHeadAdmitted runPrependOnCore; dsimp only; split <;> rfl

theorem runEnqueueHeadAdmitted_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runEnqueueHeadAdmitted c t p) st := by
  have h := runEnqueueHeadAdmitted_objects st c t p
  split at h
  · exact .of_objects_eq h
  · exact .congr h rfl (runPrependLinks_objectsAgreeOffRunLinks st c t p)

theorem runEnqueueHeadOnCore_objectsAgreeOffRunLinks (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    objectsAgreeOffRunLinks (st.runEnqueueHeadOnCore c t p) st := by
  unfold runEnqueueHeadOnCore; split
  · exact runEnqueueHeadAdmitted_objectsAgreeOffRunLinks st c t p
  · exact .of_objects_eq rfl

theorem runEnqueueHeadOnCore_objects_invExt (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    (st.runEnqueueHeadOnCore c t p).objects.invExt := by
  unfold runEnqueueHeadOnCore; split
  · rw [runEnqueueHeadAdmitted_objects]; split
    · exact hInv
    · exact runPrependLinks_objects_invExt _ _ _ _ hInv
  · exact hInv

theorem runEnqueueHeadOnCore_objects_invExtK (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hK : st.objects.invExtK) :
    (st.runEnqueueHeadOnCore c t p).objects.invExtK := by
  unfold runEnqueueHeadOnCore; split
  · rw [runEnqueueHeadAdmitted_objects]; split
    · exact hK
    · exact runPrependLinks_objects_invExtK _ _ _ _ hK
  · exact hK

theorem runEnqueueHeadAdmitted_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runEnqueueHeadAdmitted c t p) st := by
  unfold runEnqueueHeadAdmitted runPrependOnCore; dsimp only; split
  · exact .withScheduler (.refl _) _
  · exact .withScheduler (.withScheduler (runPrependLinks_onlyObjectsSchedulerDiffer _ _ _ _) _) _

theorem runEnqueueHeadOnCore_onlyObjectsSchedulerDiffer (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    onlyObjectsSchedulerDiffer (st.runEnqueueHeadOnCore c t p) st := by
  unfold runEnqueueHeadOnCore; split
  · exact runEnqueueHeadAdmitted_onlyObjectsSchedulerDiffer st c t p
  · exact .refl _

@[simp] theorem runEnqueueHeadOnCore_referenceTables (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueHeadOnCore c t p).referenceTables = st.referenceTables :=
  (runEnqueueHeadOnCore_onlyObjectsSchedulerDiffer st c t p).referenceTables

@[simp] theorem runEnqueueHeadOnCore_machine (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueHeadOnCore c t p).machine = st.machine := by
  have h := runEnqueueHeadOnCore_onlyObjectsSchedulerDiffer st c t p
  unfold onlyObjectsSchedulerDiffer at h; rw [h]

/-- Core `c`'s ends once `t` is head-enqueued there at `p`. -/
def runEnqueueHeadEnds (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : RunQueueEnds :=
  if (st.runLinkOn c t).queued then st.scheduler.runQueueEndsOnCore c
  else (st.scheduler.runQueueEndsOnCore c).prepend t p

theorem runEnqueueHeadAdmitted_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueHeadAdmitted c t p).scheduler =
      (st.scheduler.setRunQueueEndsOnCore c (st.runEnqueueHeadEnds c t p)).setRunQueueOnCore c
        ((st.scheduler.runQueueOnCore c).insertHead t p) := by
  unfold runEnqueueHeadAdmitted runEnqueueHeadEnds runPrependOnCore
  by_cases hq : (st.runLinkOn c t).queued = true
  · simp only [hq, if_true, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_get]
  · simp only [hq, if_false, Bool.false_eq_true, runPrependLinks_scheduler,
      SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]

theorem runEnqueueHeadOnCore_scheduler (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueHeadOnCore c t p).scheduler =
      if st.runEnqueueAdmits c t then
        (st.scheduler.setRunQueueEndsOnCore c (st.runEnqueueHeadEnds c t p)).setRunQueueOnCore c
          ((st.scheduler.runQueueOnCore c).insertHead t p)
      else st.scheduler := by
  unfold runEnqueueHeadOnCore; split
  · exact runEnqueueHeadAdmitted_scheduler st c t p
  · rfl

theorem runEnqueueHeadOnCore_current (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueHeadOnCore c t p).scheduler.currentCode = st.scheduler.currentCode := by
  rw [runEnqueueHeadOnCore_scheduler]
  split <;> simp [SchedulerState.setRunQueueOnCore, SchedulerState.setRunQueueEndsOnCore]

theorem runEnqueueHeadOnCore_currentOnCore (st : SystemState) (c c' : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueHeadOnCore c t p).scheduler.currentOnCore c' = st.scheduler.currentOnCore c' := by
  unfold SchedulerState.currentOnCore; rw [runEnqueueHeadOnCore_current]

-- ============================================================================
-- Agreement with the queue
-- ============================================================================

theorem runPrependOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runPrependOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runPrependOnCore
  rw [SchedulerState.setRunQueueEndsOnCore_runQueueOnCore, runPrependLinks_scheduler]

theorem runPrependOnCore_runQueueEndsOnCore (st : SystemState) (c c' : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runPrependOnCore c t p).scheduler.runQueueEndsOnCore c' =
      if c' = c then (st.scheduler.runQueueEndsOnCore c).prepend t p
      else st.scheduler.runQueueEndsOnCore c' := by
  unfold runPrependOnCore
  by_cases h : c' = c
  · subst h; rw [if_pos rfl, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_self,
      runPrependLinks_scheduler]
  · rw [if_neg h, SchedulerState.setRunQueueEndsOnCore_runQueueEndsOnCore_ne _ _ _ _ (Ne.symm h),
      runPrependLinks_scheduler]

/-- The entry every core's queue reads for every thread after the prepend: the
joining thread's TCB entry, then the backward links of the queue's and the
bucket's old first threads. -/
theorem runPrependLinks_runLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (x : SeLe4n.ThreadId) :
    (st.runPrependLinks c t p).runLinkOn c' x =
      let e := st.scheduler.runQueueEndsOnCore c
      let bhead := (RunQueue.endsOf e.buckets p).head
      let L1 := if x = t then
          (match st.getTcb? t with
           | some tcb => ({ tcb with
              runCoreCode := c.val + 1, runPrio := p, runPrevCode := 0, runNextCode := e.head,
              runBucketPrevCode := 0, runBucketNextCode := bhead } : TCB).runLinkOn c'
           | none => RunQueue.RunQueueLink.none)
        else st.runLinkOn c' x
      let L2 := if code x = e.head then RunQueueLink.withPrevIfQueued (code t) L1 else L1
      if code x = bhead then RunQueueLink.withBucketPrevIfQueued (code t) L2 else L2 := by
  unfold runPrependLinks
  rw [runLinkOn_updateTcbAtCode_map _ _ _ c' _ (fun tcb => TCB.runLinkOn_setBucketPrev tcb _ c')
      (RunQueueLink.withBucketPrevIfQueued_none _),
    runLinkOn_updateTcbAtCode_map _ _ _ c' _ (fun tcb => TCB.runLinkOn_setPrev tcb _ c')
      (RunQueueLink.withPrevIfQueued_none _)]
  by_cases hx : x = t
  · subst hx; rw [runLinkOn_mapTcbInPlace_self _ _ _]; simp only [if_true]; rfl
  · rw [runLinkOn_mapTcbInPlace_ne _ _ _ _ hx]; simp only [hx, if_false]

theorem runPrependOnCore_runLinkOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (x : SeLe4n.ThreadId) :
    (st.runPrependOnCore c t p).runLinkOn c' x = (st.runPrependLinks c t p).runLinkOn c' x := rfl

/-- Head-enqueueing a TCB that is on no other core's queue keeps every core's
queue in agreement with the threads. -/
theorem runEnqueueHeadAdmitted_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (hR : st.runQueueRefined)
    (hT : (st.getTcb? t).isSome)
    (hOther : ∀ c', c' ≠ c → (st.scheduler.runQueueOnCore c').contains t = false) :
    (st.runEnqueueHeadAdmitted c t p).runQueueRefined := by
  unfold runEnqueueHeadAdmitted
  by_cases hq : (st.runLinkOn c t).queued = true
  · have hc : (st.scheduler.runQueueOnCore c).contains t = true := by
      rw [← (hR c).contains]; exact hq
    simp only [hq, if_true]
    rw [RunQueue.insertHead_of_mem _ _ _ hc, SchedulerState.setRunQueueOnCore_runQueueOnCore]
    exact hR
  · simp only [hq, if_false, Bool.false_eq_true]
    have hc : (st.scheduler.runQueueOnCore c).contains t = false := by
      rw [← (hR c).contains]; simpa using hq
    obtain ⟨tcb, hTcb⟩ := Option.isSome_iff_exists.mp hT
    intro c'
    refine ⟨?_, fun x => ?_⟩
    · rw [SchedulerState.setRunQueueOnCore_runQueueEndsOnCore, runPrependOnCore_runQueueEndsOnCore]
      by_cases h : c' = c
      · subst h
        rw [if_pos rfl, SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
          runPrependOnCore_runQueueOnCore, (hR c').1]
        unfold RunQueueEnds.prepend RunQueue.insertHead
        rw [dif_neg (by rw [hc]; decide)]
        rfl
      · rw [if_neg h, SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm h),
          runPrependOnCore_runQueueOnCore]
        exact (hR c').1
    · rw [runLinkOn_withScheduler, runPrependOnCore_runLinkOn,
        runPrependLinks_runLinkOn st c t p c' x]
      have hE := (hR c).1
      have hH0 : (st.scheduler.runQueueEndsOnCore c).head = (st.scheduler.runQueueOnCore c).head := by
        rw [hE]; rfl
      have hB0 : (st.scheduler.runQueueEndsOnCore c).buckets = (st.scheduler.runQueueOnCore c).buckets := by
        rw [hE]; rfl
      dsimp only
      rw [hH0, hB0, hTcb]
      have htT := RunQueue.code_ne_queue_head hc
      have htB := RunQueue.code_ne_bucket_head hc p
      by_cases h : c' = c
      · subst h
        rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, runPrependOnCore_runQueueOnCore]
        unfold RunQueue.queuedLink
        rw [RunQueue.links_insertHead_of_not_contains hc,
          RunQueue.linkOf_prependLinks (st.scheduler.runQueueOnCore c').links_invExtK _ _ _ _ htT htB]
        by_cases hx : x = t
        · subst hx
          simp only [if_true, if_neg htT, if_neg htB, TCB.runLinkOn, TCB.runLink]
        · simp only [if_neg hx]
          rw [(hR c').2 x]
          unfold RunQueue.queuedLink
          by_cases hLq : (RunQueue.linkOf (st.scheduler.runQueueOnCore c').links x).queued = true
          · by_cases e1 : code x = (st.scheduler.runQueueOnCore c').head <;>
            by_cases e2 : code x = (RunQueue.endsOf (st.scheduler.runQueueOnCore c').buckets p).head
            · simp only [hLq, if_pos e1, if_pos e2, if_true, RunQueueLink.withPrevIfQueued,
                RunQueueLink.withBucketPrevIfQueued]
            · simp only [hLq, if_pos e1, if_neg e2, if_true, RunQueueLink.withPrevIfQueued]
            · simp only [hLq, if_neg e1, if_pos e2, if_true, RunQueueLink.withBucketPrevIfQueued]
            · simp only [hLq, if_neg e1, if_neg e2, if_true]
              generalize RunQueue.linkOf (st.scheduler.runQueueOnCore c').links x = L at hLq ⊢
              cases L; simp_all
          · have hLq' : (RunQueue.linkOf (st.scheduler.runQueueOnCore c').links x).queued = false := by
              simpa using hLq
            simp [hLq']
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm h),
          runPrependOnCore_runQueueOnCore, ← (hR c').2 x]
        have hL1 : (if x = t then (({ tcb with
              runCoreCode := c.val + 1, runPrio := p, runPrevCode := 0,
              runNextCode := (st.scheduler.runQueueOnCore c).head,
              runBucketPrevCode := 0,
              runBucketNextCode := (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).head } : TCB).runLinkOn c') else st.runLinkOn c' x) = st.runLinkOn c' x := by
          by_cases hx : x = t
          · subst hx
            rw [if_pos rfl, (hR c').2 x, RunQueue.queuedLink_of_not_contains (hOther c' h)]
            unfold TCB.runLinkOn
            rw [if_neg (fun e => h (Fin.ext (by simp at e; omega)))]
          · rw [if_neg hx]
        rw [hL1]
        have hoff : ∀ {k : Nat}, k = (st.scheduler.runQueueOnCore c).head ∨
            k = (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).head →
            code x = k → (st.runLinkOn c' x).queued = false := by
          intro k hk e
          have hcx : (st.scheduler.runQueueOnCore c).contains x = true := by
            rcases hk with hk | hk
            · exact RunQueue.contains_of_code_eq_head (e.trans hk)
            · exact RunQueue.contains_of_code_eq_bucket_head (e.trans hk)
          have hq1 : (st.runLinkOn c x).queued = true := by rw [(hR c).contains]; exact hcx
          cases hq2 : (st.runLinkOn c' x).queued
          · rfl
          · exact absurd (runLinkOn_queued_unique hq1 hq2).symm h
        by_cases e1 : code x = (st.scheduler.runQueueOnCore c).head
        · rw [if_pos e1, RunQueueLink.withPrevIfQueued_of_not_queued (hoff (Or.inl rfl) e1)]
          by_cases e2 : code x = (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).head
          · rw [if_pos e2, RunQueueLink.withBucketPrevIfQueued_of_not_queued (hoff (Or.inr rfl) e2)]
          · rw [if_neg e2]
        · rw [if_neg e1]
          by_cases e2 : code x = (RunQueue.endsOf (st.scheduler.runQueueOnCore c).buckets p).head
          · rw [if_pos e2, RunQueueLink.withBucketPrevIfQueued_of_not_queued (hoff (Or.inr rfl) e2)]
          · rw [if_neg e2]

/-- Every head enqueue keeps every core's queue in agreement with the threads. -/
theorem runEnqueueHeadOnCore_refined {st : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (hR : st.runQueueRefined) :
    (st.runEnqueueHeadOnCore c t p).runQueueRefined := by
  unfold runEnqueueHeadOnCore
  split
  · next h =>
    exact runEnqueueHeadAdmitted_refined hR (runEnqueueAdmits_isSome h)
      (runEnqueueAdmits_not_contains hR h)
  · exact hR

-- ============================================================================
-- Membership
-- ============================================================================

/-- An admitted head enqueue of `t` moves no other thread's core code. -/
theorem runEnqueueHeadAdmitted_runCoreCode_ne (st : SystemState) (c : CoreId)
    (t y : SeLe4n.ThreadId) (p : SeLe4n.Priority) (hy : y ≠ t) :
    ((st.runEnqueueHeadAdmitted c t p).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  unfold runEnqueueHeadAdmitted; dsimp only
  split
  · rfl
  · show ((st.runPrependLinks c t p).getTcb? y).map TCB.runCoreCode = _
    unfold runPrependLinks; dsimp only
    refine (updateTcbAtCode_runCoreCode _ _ (fun x => { x with runBucketPrevCode := code t })
      (fun _ => rfl) y).trans ?_
    refine (updateTcbAtCode_runCoreCode _ _ (fun x => { x with runPrevCode := code t })
      (fun _ => rfl) y).trans ?_
    exact mapTcbInPlace_runCoreCode _ _ _ _ (fun _ => Or.inr (Ne.symm hy))

/-- The prepend's TCB writes give `t` core `c`'s code. -/
theorem runPrependLinks_runCoresAgree_self (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    ((st.runPrependLinks c t p).getTcb? t).map TCB.runCoreCode =
      (st.getTcb? t).map (fun _ => c.val + 1) := by
  unfold runPrependLinks; dsimp only
  rw [updateTcbAtCode_runCoreCode _ _ (fun x => { x with runBucketPrevCode := code t })
      (fun _ => rfl) t,
    updateTcbAtCode_runCoreCode _ _ (fun x => { x with runPrevCode := code t }) (fun _ => rfl) t,
    mapTcbInPlace_getTcb?_self, Option.map_map]
  rfl

/-- After the admitted head enqueue of `t` on core `c`, `t` — when it is a
thread — is queued on `c` and on no other core, and no other thread moves on
or off a queue. -/
theorem runEnqueueHeadAdmitted_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runEnqueueHeadAdmitted c t p).queuedOn c' y =
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
    unfold runEnqueueHeadAdmitted; dsimp only
    split
    · next hq =>
      show st.queuedOn c' y = _
      obtain ⟨tcb, hT, hC⟩ := (runLinkOn_queued_iff st c y).mp hq
      unfold queuedOn; rw [hT]
      simp only [Option.isSome_some, Bool.true_and]
      exact hcode tcb hC
    · show (st.runPrependLinks c y p).queuedOn c' y = _
      have h := runPrependLinks_runCoresAgree_self st c y p
      unfold queuedOn
      cases h1 : (st.runPrependLinks c y p).getTcb? y <;> cases h2 : st.getTcb? y <;>
        rw [h1, h2] at h <;>
        simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h
      · rfl
      · simp only [Option.isSome_some, Bool.true_and]; exact hcode _ h
  · rw [if_neg hy]
    have h := runEnqueueHeadAdmitted_runCoreCode_ne st c t y p hy
    unfold queuedOn
    cases h1 : (st.runEnqueueHeadAdmitted c t p).getTcb? y <;> cases h2 : st.getTcb? y <;>
      rw [h1, h2] at h <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h <;>
      simp only [h]

theorem runEnqueueHeadOnCore_queuedOn (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c' : CoreId) (y : SeLe4n.ThreadId) :
    (st.runEnqueueHeadOnCore c t p).queuedOn c' y =
      if y = t ∧ st.runEnqueueAdmits c t = true then decide (c' = c)
      else st.queuedOn c' y := by
  unfold runEnqueueHeadOnCore
  split
  · next hA =>
    rw [runEnqueueHeadAdmitted_queuedOn]
    by_cases hy : y = t
    · subst hy
      rw [if_pos rfl, if_pos ⟨rfl, hA⟩, runEnqueueAdmits_isSome hA, Bool.true_and]
    · rw [if_neg hy, if_neg (fun h => hy h.1)]
  · next hA =>
    rw [if_neg (fun h => hA h.2)]

/-- A head enqueue of `t` moves no other thread's core code. -/
theorem runEnqueueHeadOnCore_runCoreCode_ne (st : SystemState) (c : CoreId) (t y : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hy : y ≠ t) :
    ((st.runEnqueueHeadOnCore c t p).getTcb? y).map TCB.runCoreCode =
      (st.getTcb? y).map TCB.runCoreCode := by
  unfold runEnqueueHeadOnCore; split
  · exact runEnqueueHeadAdmitted_runCoreCode_ne st c t y p hy
  · rfl

theorem runEnqueueHeadAdmitted_runQueueOnCore_self (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueHeadAdmitted c t p).scheduler.runQueueOnCore c =
      (st.scheduler.runQueueOnCore c).insertHead t p := by
  unfold runEnqueueHeadAdmitted
  dsimp only
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  split
  · rfl
  · rw [runPrependOnCore_runQueueOnCore]

theorem runEnqueueHeadOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) (h : c ≠ c') :
    (st.runEnqueueHeadOnCore c t p).scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold runEnqueueHeadOnCore runEnqueueHeadAdmitted
  split
  · dsimp only
    rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ h]
    split
    · rfl
    · rw [runPrependOnCore_runQueueOnCore]
  · rfl

-- ============================================================================
-- Stages
-- ============================================================================

/-- The guarded head enqueue keeps the link agreement whichever thread it places. -/
theorem RunQueueLinkStage.runEnqueueHeadOnCore (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    RunQueueLinkStage st (st.runEnqueueHeadOnCore c t p) :=
  .of_tableFrame (fun h r =>
      ⟨runEnqueueHeadOnCore_objects_invExt st c t p h, runEnqueueHeadOnCore_refined r⟩)
    (fun _ => .of_agreeOffRunLinks (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p)
      (runEnqueueHeadOnCore_onlyObjectsSchedulerDiffer st c t p).referenceTables)
    (fun _ => .of_agreeOffRunLinks (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p)
      (by rw [runEnqueueHeadOnCore_scheduler]; split <;> rfl))
    (fun _ => .of_agreeOffRunLinks (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p))
    fun _ => .of_agreeOffRunLinks (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p)

/-- The guarded head enqueue of a runnable thread current on no core, on its
home core, is a stage. -/
theorem RunQueueStage.runEnqueueHeadOnCore (st : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) (hNC : ∀ c', st.scheduler.currentOnCore c' ≠ some t)
    (hRun : st.runnable t) (hHome : st.homedOn t c) :
    RunQueueStage st (st.runEnqueueHeadOnCore c t p) :=
  RunQueueStage.of_link' (RunQueueLinkStage.runEnqueueHeadOnCore st c t p)
    (fun c' y h' => by rwa [runEnqueueHeadOnCore_currentOnCore] at h')
    (fun c' y hy c'' h' => by
      rw [runEnqueueHeadOnCore_queuedOn, if_neg (fun h => hNC _ (h.1 ▸ hy))] at h'
      exact h')
    (fun y hy c'' h' => by
      rw [runEnqueueHeadOnCore_queuedOn] at h'
      split at h'
      · rename_i h; obtain ⟨rfl, hA⟩ := h
        rw [runEnqueueAdmits_not_idle hA] at hy; cases hy
      · exact h')
    (fun c' y h' => by
      rw [runEnqueueHeadOnCore_queuedOn] at h'
      split at h'
      · rename_i h; obtain ⟨rfl, -⟩ := h
        exact .inr ⟨(StateMono.of_agreeOffRunLinks
          (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c y p) y).1 hRun,
          (of_decide_eq_true h') ▸
            (StateMono.of_agreeOffRunLinks
              (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c y p)).homedOn hRun.activeAt hHome⟩
      · exact .inl h')
    (StateMono.of_agreeOffRunLinks (runEnqueueHeadOnCore_objectsAgreeOffRunLinks st c t p))

/-- A stage, then the head enqueue of a thread runnable before it and current
nowhere after it, on its home core. -/
theorem RunQueueStage.then_enqueueHead {st s : SystemState} {c : CoreId} {t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (h1 : RunQueueStage st s)
    (hNC : ∀ c', s.scheduler.currentOnCore c' ≠ some t) (hRun : st.runnable t)
    (hHome : s.homedOn t c) :
    RunQueueStage st (s.runEnqueueHeadOnCore c t p) :=
  ⟨h1.1.trans (RunQueueLinkStage.runEnqueueHeadOnCore s c t p), fun e h r r'' d =>
    let ⟨h', r'⟩ := h1.1 h r
    (RunQueueStage.runEnqueueHeadOnCore s c t p hNC ((h1.2.2 h r).runnable hRun)
      hHome).2.1 e h' r' r''
      (h1.2.1 e h r r' d),
    fun h r =>
      let ⟨h', r'⟩ := h1.1 h r
      (h1.2.2 h r).trans
        ((RunQueueStage.runEnqueueHeadOnCore s c t p hNC ((h1.2.2 h r).runnable hRun)
          hHome).2.2 h' r')⟩

end SeLe4n.Model.SystemState
