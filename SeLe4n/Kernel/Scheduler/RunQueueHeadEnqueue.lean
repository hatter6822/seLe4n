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

end SeLe4n.Model.SystemState
