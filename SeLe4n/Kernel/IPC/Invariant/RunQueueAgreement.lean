/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.CrossCore.Fault

/-!
# IPC steps keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  Every core's run queue is read through the threads' TCB
run-queue links, and `SystemState.runQueueRefined` says the links agree with the
abstract queue.  This module proves the agreement is a stage
(`SystemState.RunQueueStage`) of every IPC step: the object writes that leave
every TCB's run-queue fields alone, and the scheduler writes that move a thread
on or off a queue through the link-writing primitives.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

/-- A TCB write through `modifyTcb` that keeps the run-queue fields. -/
theorem modifyTcb_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (h : modifyTcb st tid f = .ok st')
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hm : TCB.StateMono f := by tcb_state_mono)
    (hW : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hY : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    RunQueueStage st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact RunQueueStage.storeObject_tcb hS (lookupTcb_some_objects st tid tcb hL) (hf tcb)
    (SystemState.objStateMono_tcb (hm tcb)) (hW tcb) (hY tcb)

theorem storeTcbQueueLinks_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (h : storeTcbQueueLinks st tid prev pprev next = .ok st') : RunQueueStage st st' :=
  modifyTcb_runQueueStage h (fun _ _ => rfl)

/-- The `.ready` mark. -/
theorem storeTcbIpcState_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {s : ThreadIpcState} (h : storeTcbIpcState st tid s = .ok st') (hs : s = .ready) :
    RunQueueStage st st' := by
  subst hs; exact modifyTcb_runQueueStage h (fun _ _ => rfl)

theorem storeTcbIpcStateAndMessage_runQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage}
    (h : storeTcbIpcStateAndMessage st tid s m = .ok st') (hs : s = .ready) :
    RunQueueStage st st' := by
  subst hs; exact modifyTcb_runQueueStage h (fun _ _ => rfl)

/-- WS-ZA ZA4.7: the send-cap record of a blocking sender writes a badge word
and two flags: no run link, thread state or scheduler field. -/
theorem recordSendCap_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (grant : Bool) :
    RunQueueStage st (recordSendCap st tid badge grant) := by
  have hG : ∀ {β : Type} (p : TCB → β), (∀ x, p (x.setSendCap badge grant) = p x) →
      ∀ t, ((recordSendCap st tid badge grant).getTcb? t).map p = (st.getTcb? t).map p := by
    intro β p hp t
    unfold recordSendCap
    by_cases h : t = tid
    · subst h; rw [SystemState.mapTcbInPlace_getTcb?_self]
      cases st.getTcb? t <;> simp [hp]
    · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _
        (fun e => h (SeLe4n.ThreadId.toObjId_injective _ _ e).symm)]
  have hL : ∀ c t, (recordSendCap st tid badge grant).runLinkOn c t = st.runLinkOn c t := by
    intro c t
    have e := hG (fun x => x.runLinkOn c) (fun _ => rfl) t
    unfold SystemState.runLinkOn
    cases h1 : (recordSendCap st tid badge grant).getTcb? t <;> cases h2 : st.getTcb? t <;>
      rw [h1, h2] at e <;> first | rfl | cases e | exact Option.some.inj e
  have hM : SystemState.StateMono st (recordSendCap st tid badge grant) :=
    SystemState.StateMono.of_stateFields (hG _ (fun _ => rfl))
  exact ⟨.of_tableFrame (fun h r => ⟨recordSendCap_objects_invExt st tid badge grant h,
      SystemState.runQueueRefined_of_frame hL rfl rfl r⟩)
      (fun _ => by unfold recordSendCap; exact .mapTcbInPlace _ _ _)
      (fun _ => by unfold recordSendCap; exact .mapTcbInPlace _ _ _)
      (fun _ => by unfold recordSendCap; exact .mapTcbInPlace _ _ _)
      (fun _ => by unfold recordSendCap; exact .mapTcbInPlace _ _ _ fun _ => rfl),
    fun _ _ _ _ d => SystemState.currentDequeuedUniqueExcept_of_eq (st := st)
      (st' := recordSendCap st tid badge grant) rfl hL hM d, fun _ _ => hM⟩

/-- **The block write** of core `c`'s current thread through `modifyTcb`. -/
theorem modifyTcb_runQueueBlockStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} {c : Concurrency.CoreId} (h : modifyTcb st tid f = .ok st')
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c) (hT : ∀ x, (f x).threadState = x.threadState)
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false)
    (hW : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hAf : ∀ x, (f x).cpuAffinity = x.cpuAffinity := by intro _; rfl)
    (hY : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    SystemState.RunQueueWindowStage (.block c) st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact SystemState.RunQueueWindowStage.storeObject_block hS (getTcb?_of_lookupTcb st tid tcb hL)
    (hf tcb) (hT tcb) hCur hNI (hW tcb) (hAf tcb) (hY tcb)

theorem storeTcbIpcState_runQueueBlockStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {s : ThreadIpcState} {c : Concurrency.CoreId} (h : storeTcbIpcState st tid s = .ok st')
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueWindowStage (.block c) st st' :=
  modifyTcb_runQueueBlockStage h (fun _ _ => rfl) (fun _ => rfl) hCur hNI

theorem storeTcbIpcStateAndMessage_runQueueBlockStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage} {c : Concurrency.CoreId}
    (h : storeTcbIpcStateAndMessage st tid s m = .ok st')
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueWindowStage (.block c) st st' :=
  modifyTcb_runQueueBlockStage h (fun _ _ => rfl) (fun _ => rfl) hCur hNI

/-- A TCB write through `modifyTcb` over a thread **already blocked** (`hB`)
that keeps its run-queue links and its thread state: the thread was ready
before neither write, so the step is monotone whatever IPC state it stores. -/
theorem modifyTcb_blockedRunQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (h : modifyTcb st tid f = .ok st')
    (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c) (hT : ∀ x, (f x).threadState = x.threadState)
    (hB : ∀ x, lookupTcb st tid = some x → x.ipcState ≠ .ready)
    (hW : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hAf : ∀ x, (f x).cpuAffinity = x.cpuAffinity := by intro _; rfl)
    (hY : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) : RunQueueStage st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact RunQueueStage.storeObject_tcb hS (lookupTcb_some_objects st tid tcb hL) (hf tcb)
    (SystemState.objStateMono_tcb ⟨fun hr => absurd hr (hB tcb hL),
      fun ha => by unfold TCB.Active; rw [hT]; exact ha, hAf tcb⟩) (hW tcb) (hY tcb)

theorem storeTcbIpcStateAndMessage_blockedRunQueueStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage}
    (h : storeTcbIpcStateAndMessage st tid s m = .ok st')
    (hB : ∀ x, lookupTcb st tid = some x → x.ipcState ≠ .ready) : RunQueueStage st st' :=
  modifyTcb_blockedRunQueueStage h (fun _ _ => rfl) (fun _ => rfl) hB

/-- An endpoint stored over an endpoint. -/
theorem storeObject_endpoint_runQueueStage {st st' : SystemState} {k : SeLe4n.ObjId}
    {ep ep' : Endpoint} (hOld : st.objects[k]? = some (.endpoint ep))
    (hS : storeObject k (.endpoint ep') st = .ok ((), st'))
    (hC : ep'.service = ep.service := by
      first
        | rfl
        | (split <;> rfl)
        | (rw [apply_ite Endpoint.service]; split <;> rfl)
        | simp_all) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by rw [hOld]; rfl)
    (SystemState.objStateMono_nonTcb (by rw [hOld]; rfl) rfl)
    (by rw [hOld]; simp only [objTableBackLinks_some, KernelObject.tableBackLinks, ← Endpoint.service_registered, hC])

/-- A TCB stored over the thread's TCB with the same run-queue fields. -/
theorem storeObject_tcbOver_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {t old : TCB} (hOld : st.getTcb? tid = some old)
    (hS : storeObject tid.toObjId (.tcb t) st = .ok ((), st'))
    (h : ∀ c, t.runLinkOn c = old.runLinkOn c)
    (hm : TCB.StepMono old t := by exact ⟨id, id, by first | rfl | simp_all⟩)
    (hW : t.taintWords = old.taintWords := by taint_words_kept)
    (hY : t.yieldToCode = old.yieldToCode := by first | rfl | simp_all) : RunQueueStage st st' :=
  RunQueueStage.storeObject_tcb hS ((SystemState.getTcb?_eq_some_iff st tid old).mp hOld) h
    (SystemState.objStateMono_tcb hm) hW hY

/-- A Reply stored over a Reply. -/
theorem storeObject_replyOver_runQueueStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {r r' : SeLe4n.Kernel.Reply} (hOld : st.getReply? rid = some r)
    (hS : storeObject rid.toObjId (.reply r') st = .ok ((), st')) : RunQueueStage st st' :=
  RunQueueStage.storeObject hS (fun c => by
    rw [(SystemState.getReply?_eq_some_iff st rid r).mp hOld]; rfl)
    (SystemState.objStateMono_nonTcb
      (by rw [(SystemState.getReply?_eq_some_iff st rid r).mp hOld]; rfl) rfl)

/-- Recording a Reply's stasher is nothing or one Reply stored over a Reply. -/
theorem recordReplyStasher_runQueueStage (st : SystemState) (code : Nat)
    (recv : SeLe4n.ThreadId) : RunQueueStage st (st.recordReplyStasher code recv) := by
  rcases SystemState.recordReplyStasher_eq_or st code recv with h | ⟨_, _, _, hR, hS⟩
  · rw [h]; exact RunQueueStage.refl _
  · exact storeObject_replyOver_runQueueStage ((SystemState.getReply?_eq_some_iff _ _ _).mpr hR) hS

theorem linkReply_runQueueStage {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId}
    {st st' : SystemState} (h : SystemState.linkReply rid caller st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.linkReply at h
  split at h
  · rename_i r hR
    split at h
    · exact storeObject_replyOver_runQueueStage hR h
    · cases h
  · cases h

theorem consumeReply_runQueueStage {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : SystemState.consumeReply rid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.consumeReply at h
  split at h
  · rename_i r hR
    exact storeObject_replyOver_runQueueStage hR h
  · cases h; exact RunQueueStage.refl _

theorem linkCallerReply_runQueueStage {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.linkCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    split at h
    · cases h
    · rename_i tcb hT
      split at h
      · exact (linkReply_runQueueStage h1).trans
          (storeObject_tcbOver_runQueueStage hT h (fun _ => rfl))
      · cases h

theorem consumeCallerReply_runQueueStage {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.consumeCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    split at h
    · cases h; exact consumeReply_runQueueStage h1
    · rename_i tcb hT
      exact (consumeReply_runQueueStage h1).trans
        (storeObject_tcbOver_runQueueStage hT h (fun _ => rfl))

theorem linkServerStashedReply_runQueueStage {caller server : SeLe4n.ThreadId}
    {st st' : SystemState}
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold SystemState.linkServerStashedReply at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i st1 h1
      split at h
      · cases h; exact linkCallerReply_runQueueStage h1
      · rename_i tcb hT
        exact (linkCallerReply_runQueueStage h1).trans
          (storeObject_tcbOver_runQueueStage hT h (fun _ => rfl))

/-- The head pop: an endpoint store and queue-link writes. -/
theorem endpointQueuePopHead_runQueueStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (h : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, tcb, st')) :
    RunQueueStage st st' := by
  unfold endpointQueuePopHead SystemState.getObject? at h
  dsimp only at h
  split at h
  · rename_i ep hEp
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i st1 hS1
          have s1 := storeObject_endpoint_runQueueStage hEp hS1
          split at h
          · cases h
          · rename_i st2 hS2
            have s2 : RunQueueStage st1 st2 := by
              split at hS2
              · cases hS2; exact RunQueueStage.refl _
              · split at hS2
                · cases hS2
                · exact storeTcbQueueLinks_runQueueStage hS2
            split at h
            · cases h
            · rename_i st3 hS3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, -, rfl⟩ := h
              exact (s1.trans s2).trans (storeTcbQueueLinks_runQueueStage hS3)
  · cases h
  · cases h

/-- The enqueue: an endpoint store and queue-link writes. -/
theorem endpointQueueEnqueue_runQueueStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    RunQueueStage st st' := by
  unfold endpointQueueEnqueue SystemState.getObject? at h
  dsimp only at h
  split at h
  · rename_i ep hEp
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · rename_i st1 hS1
              exact (storeObject_endpoint_runQueueStage hEp hS1).trans
                (storeTcbQueueLinks_runQueueStage h)
          · split at h
            · cases h
            · split at h
              · cases h
              · rename_i st1 hS1
                split at h
                · cases h
                · rename_i st2 hS2
                  exact ((storeObject_endpoint_runQueueStage hEp hS1).trans
                    (storeTcbQueueLinks_runQueueStage hS2)).trans
                    (storeTcbQueueLinks_runQueueStage h)
  · cases h
  · cases h

-- ============================================================================
-- Wake and deschedule
-- ============================================================================

/-- The wake keeps the link agreement whichever thread it wakes. -/
theorem enqueueRunnableOnCore_runQueueLinkStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : SystemState.RunQueueLinkStage st (enqueueRunnableOnCore st c tid) :=
  .of_tableFrame (fun h r => ⟨enqueueRunnableOnCore_preserves_objects_invExt st c tid h,
    enqueueRunnableOnCore_runQueueRefined c tid h r⟩)
    (fun h => .of_kindPreservingWrite (enqueueRunnableOnCore_kindPreservingWrite st c tid h)
      (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid).referenceTables)
    (fun h => enqueueRunnableOnCore_releaseStateAgree st c tid h)
    (fun h => enqueueRunnableOnCore_refillViewsKept st c tid h)
    (fun h => enqueueRunnableOnCore_yieldLinksKept st c tid h)
    (by have h := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c tid
        unfold SystemState.onlyObjectsSchedulerDiffer at h; rw [h])

/-- The wake marks one thread ready and moves run-queue links: every runnable
thread stays runnable. -/
theorem enqueueRunnableOnCore_stateMono (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.StateMono st (enqueueRunnableOnCore st c tid) := by
  cases hT : st.getTcb? tid with
  | none =>
    have hW : st.getTcbWitnessed? tid = none := by
      unfold SystemState.getTcbWitnessed?; split <;> simp_all [SystemState.getTcb?]
    simp only [enqueueRunnableOnCore, hW]; exact .refl st
  | some tcb =>
    cases hD : wakeDeclines st c tid
    · have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT
      have h1 : SystemState.StateMono st { st with objects := (st.objects.insert
          tid.toObjId (.tcb (tcb.setIpcState .ready))) } :=
        SystemState.StateMono.insert hInv rfl
          (by rw [hRaw]; exact SystemState.objStateMono_tcb ⟨fun _ => rfl, id, rfl⟩)
      exact h1.trans (SystemState.StateMono.of_agreeOffRunLinks
        (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hT hD))
    · have : enqueueRunnableOnCore st c tid = st := by
        simp [enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD]
      rw [this]; exact .refl st

/-- The thread a wake places is runnable afterwards, when it was not
suspended. -/
theorem enqueueRunnableOnCore_runnable (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hA : st.activeAt tid)
    (hD : wakeDeclines st c tid = false) : (enqueueRunnableOnCore st c tid).runnable tid := by
  obtain ⟨tcb, hT, ha⟩ := hA
  have hM := SystemState.StateMono.of_agreeOffRunLinks
    (enqueueRunnableOnCore_objectsAgree_marked st c tid tcb hT hD)
  refine hM.runnable ⟨(tcb.setIpcState .ready), ?_, rfl, ha⟩
  unfold SystemState.getTcb?
  simp only [RHTable_getElem?_eq_get?]
  rw [RobinHood.RHTable.getElem?_insert_self st.objects _ _ hInv]

/-- A thread no core runs is no core's current thread. -/
theorem currentNowhere_of_runningOnSomeCore_false {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : runningOnSomeCore st tid = false) (c : Concurrency.CoreId) :
    st.scheduler.currentOnCore c ≠ some tid := by
  simp only [runningOnSomeCore, SeLe4n.Kernel.Concurrency.allCores, List.any_eq_false] at h
  intro hc
  have hcc := h c (List.mem_finRange c)
  rw [hc] at hcc
  simp at hcc

/-- The wake of an active thread current on no core, on its home core: the
`.ready` mark and the link-writing enqueue keep every current thread off the
queues, queue only the now-runnable thread, on its home, and the enqueue guard
admits no idle thread. -/
theorem enqueueRunnableOnCore_runQueueStage (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (hNC : st.currentNowhere tid) (hA : st.activeAt tid)
    (hHome : st.homedOn tid c) :
    RunQueueStage st (enqueueRunnableOnCore st c tid) :=
  RunQueueStage.of_invExt fun hInv =>
    RunQueueStage.of_link' (enqueueRunnableOnCore_runQueueLinkStage st c tid)
      (fun c' y h' => by rwa [enqueueRunnableOnCore_currentOnCore] at h')
      (fun c' y hy c'' h' => by
        rw [enqueueRunnableOnCore_queuedOn st c tid hInv] at h'
        split at h'
        · rename_i h; exact absurd (h.1 ▸ hy) (hNC c')
        · exact h')
      (fun y hy c'' h' => by
        rw [enqueueRunnableOnCore_queuedOn st c tid hInv] at h'
        split at h'
        · rename_i h; obtain ⟨rfl, -, hD⟩ := h
          rw [SystemState.runEnqueueAdmits_not_idle (wakeDeclines_eq_false_iff.mp hD).2] at hy
          cases hy
        · exact h')
      (fun c' y h' => by
        rw [enqueueRunnableOnCore_queuedOn st c tid hInv] at h'
        split at h'
        · rename_i h; obtain ⟨rfl, -, hD⟩ := h
          exact .inr ⟨enqueueRunnableOnCore_runnable st c y hInv hA hD,
            (of_decide_eq_true h') ▸ (enqueueRunnableOnCore_stateMono st c y hInv).homedOn hA hHome⟩
        · exact .inl h')
      (enqueueRunnableOnCore_stateMono st c tid hInv)

theorem wakeThread_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) (hNC : st.currentNowhere tid) (hA : st.activeAt tid) :
    RunQueueStage st (wakeThread st tid c).1 :=
  enqueueRunnableOnCore_runQueueStage st _ tid hNC hA (homedOn_determineTargetCore st tid)

/-- `t`'s TCB is blocked in IPC (not `.ready`): a thread a wake may target. -/
def blockedAt (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∃ tcb, st.getTcb? t = some tcb ∧ tcb.ipcState ≠ .ready

/-- **The steps up to a wake, then the wake**: the woken thread was blocked when
the steps began, so it was active (the state fields agree), and the steps kept
it active. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.then_wake {st st1 : SystemState} {w : SeLe4n.ThreadId}
    (pre : RunQueueStage st st1) (c : Concurrency.CoreId) (hNC : st1.currentNowhere w)
    (hB : blockedAt st w) : RunQueueStage st (wakeThread st1 w c).1 :=
  ⟨pre.1.trans (enqueueRunnableOnCore_runQueueLinkStage st1 _ w), fun e h r r'' d =>
    let ⟨h1, r1⟩ := pre.1 h r
    have hA : st.activeAt w := by
      obtain ⟨x, hx, hb⟩ := hB
      exact ⟨x, hx, (d.coherent w x hx).resolve_left hb⟩
    (wakeThread_runQueueStage st1 w c hNC ((pre.mono h r).activeAt hA)).2.1 e h1 r1 r''
      (pre.2.1 e h r r1 d),
    fun h r => let ⟨h1, _⟩ := pre.1 h r
      (pre.mono h r).trans (enqueueRunnableOnCore_stateMono st1 _ w h1)⟩

/-- **The steps up to a wake, then the wake, inside a scheduling point other
than a block**: there every current thread is runnable, so a thread blocked when
the steps began is no core's current thread; the steps keep it off every core. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueWindowStage.then_wake {p : SchedPoint}
    (hp : ∀ c, p ≠ .block c) {st st1 : SystemState} {w : SeLe4n.ThreadId}
    (pre : RunQueueStage st st1) (c : Concurrency.CoreId)
    (hC : ∀ c', st1.scheduler.currentOnCore c' = some w → st.scheduler.currentOnCore c' = some w)
    (hB : blockedAt st w) : SystemState.RunQueueWindowStage p st (wakeThread st1 w c).1 :=
  ⟨pre.1.trans (enqueueRunnableOnCore_runQueueLinkStage st1 _ w), fun h r r'' d => by
    have hNC : st.currentNowhere w := fun c' hc => by
      rcases (d.current c' w hc).2.2 with hb | hr
      · exact hp c' (Option.some.inj hb)
      · obtain ⟨x, hx, hb⟩ := hB
        obtain ⟨y, hy, hry⟩ := hr
        rw [hx] at hy; cases hy; exact hb hry.1
    exact (RunQueueStage.then_wake pre c (fun c' h => hNC c' (hC c' h)) hB).2.1 (some p) h r
      r'' d,
    fun _ _ h r => let ⟨h1, _⟩ := pre.1 h r
      (pre.2.2 h r).trans (enqueueRunnableOnCore_stateMono st1 _ w h1)⟩

/-- **The block of core `c`'s current thread `t`**: stages, the IPC-state store
that blocks `t`, more stages, then `t`'s deschedule — a scheduling point opened
and closed, `t` being current on `c` throughout and no idle thread. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.blockThenDeschedule
    {st st1 st2 st3 : SystemState} {t : SeLe4n.ThreadId} {s : ThreadIpcState}
    {m : Option IpcMessage} {c : Concurrency.CoreId}
    (pre : RunQueueStage st st1) (hS : storeTcbIpcStateAndMessage st1 t s m = .ok st2)
    (post : RunQueueStage st2 st3) (hC1 : st1.scheduler.currentOnCore c = some t)
    (hC3 : st3.scheduler.currentOnCore c = some t) (hNI : isIdleThreadId t = false) :
    SystemState.RunQueueEntryStage st (removeRunnableOnCore st3 t c) :=
  (((pre.window (.block c)).trans (storeTcbIpcStateAndMessage_runQueueBlockStage hS hC1 hNI)).trans
    (post.window _)).dispatch (SystemState.RunQueueDispatchStage.descheduleCurrent st3 c t hC3)

/-- **The block of a sender**: `blockThenDeschedule`, then the send-cap record
(`recordSendCap`) that keeps the sender's badge and grant bit on its TCB. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.blockThenDescheduleRecord
    {st st1 st2 st3 : SystemState} {t : SeLe4n.ThreadId} {s : ThreadIpcState}
    {m : Option IpcMessage} {c : Concurrency.CoreId}
    (pre : RunQueueStage st st1) (hS : storeTcbIpcStateAndMessage st1 t s m = .ok st2)
    (post : RunQueueStage st2 st3) (hC1 : st1.scheduler.currentOnCore c = some t)
    (hC3 : st3.scheduler.currentOnCore c = some t) (hNI : isIdleThreadId t = false)
    (badge : Option SeLe4n.Badge) (grant : Bool) :
    SystemState.RunQueueEntryStage st
      (recordSendCap (removeRunnableOnCore st3 t c) t badge grant) :=
  (((pre.window (.block c)).trans (storeTcbIpcStateAndMessage_runQueueBlockStage hS hC1 hNI)).trans
    (post.window _)).dispatch
    ((SystemState.RunQueueDispatchStage.descheduleCurrent st3 c t hC3).trans_stage
      (recordSendCap_runQueueStage _ t badge grant))

-- ============================================================================
-- Call
-- ============================================================================

/-- `t`'s TCB, if it has one, is blocked in IPC. -/
def blockedIfTcb (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ tcb, st.getTcb? t = some tcb → tcb.ipcState ≠ .ready

/-- Between scheduling points a thread whose TCB, if any, is blocked is current
nowhere: a current thread is runnable. -/
theorem currentNowhere_of_blockedIfTcb {st : SystemState} {t : SeLe4n.ThreadId}
    (hD : st.currentDequeuedUnique) (h : blockedIfTcb st t) : st.currentNowhere t :=
  fun _ hc => let ⟨x, hx, hr⟩ := hD.runnable hc; h x hx hr.1

/-- Between scheduling points a thread blocked in IPC is no idle thread: every
idle thread is runnable. -/
theorem notIdle_of_blocked {st : SystemState} (hD : st.currentDequeuedUnique)
    {t : SeLe4n.ThreadId} {tcb : TCB} (hT : st.getTcb? t = some tcb)
    (hB : tcb.ipcState ≠ .ready) : isIdleThreadId t = false := by
  cases h : isIdleThreadId t
  · rfl
  · obtain ⟨c, rfl⟩ := (isIdleThreadId_iff _).mp h
    obtain ⟨x, hx, hr⟩ := hD.idleRunnable c
    rw [hT] at hx; cases hx; exact absurd hr.1 hB

/-- Every endpoint queue's head is current nowhere and blocked: the thread a
send, a call or a receive pops and wakes. -/
def endpointHeadsWakeable (st : SystemState) : Prop :=
  ∀ epId ep, st.getEndpoint? epId = some ep → ∀ r,
    ep.receiveQ.head = some r ∨ ep.sendQ.head = some r → st.currentNowhere r ∧ blockedIfTcb st r

/-- Between scheduling points every endpoint head is wakeable: a head is blocked
(`queueHeadBlockedConsistent`), so no core runs it. -/
theorem endpointHeadsWakeable_of {st : SystemState} (hD : st.currentDequeuedUnique)
    (hQ : queueHeadBlockedConsistent st) : endpointHeadsWakeable st := by
  intro epId ep hE r hr
  have hB : blockedIfTcb st r := fun tcb hT => by
    have hEo := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE
    have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rcases hr with hr | hr
    · rw [(hQ epId ep r tcb hEo hTo).1 hr]; exact fun h => by cases h
    · rcases (hQ epId ep r tcb hEo hTo).2 hr with h | h <;> rw [h] <;> exact fun h => by cases h
  exact ⟨currentNowhere_of_blockedIfTcb hD hB, hB⟩

/-- A step that adds no endpoint and keeps every current slot keeps every endpoint
head current nowhere; one whose post-state heads are blocked
(`queueHeadBlockedConsistent`) keeps them wakeable. -/
theorem endpointHeadsWakeable.of_frame {st st' : SystemState} (h : endpointHeadsWakeable st)
    (hE : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint), st'.objects[oid]? = some (.endpoint ep) →
      st.objects[oid]? = some (.endpoint ep))
    (hC : ∀ c, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hQ : queueHeadBlockedConsistent st') : endpointHeadsWakeable st' := by
  intro epId ep hEp r hr
  have hEo := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
  obtain ⟨hN, -⟩ := h epId ep ((SystemState.getEndpoint?_eq_some_iff _ _ _).mpr (hE _ _ hEo)) r hr
  refine ⟨fun c => by rw [hC c]; exact hN c, fun tcb hT => ?_⟩
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  rcases hr with hr | hr
  · rw [(hQ epId ep r tcb hEo hTo).1 hr]; exact fun h => by cases h
  · rcases (hQ epId ep r tcb hEo hTo).2 hr with h | h <;> rw [h] <;> exact fun h => by cases h

/-- Every thread not `.ready` is current nowhere: seL4's `ct_in_state
activatable` read backwards, the premise of a wake of a blocked thread. -/
def blockedCurrentNowhere (st : SystemState) : Prop :=
  ∀ t tcb, st.getTcb? t = some tcb → tcb.ipcState ≠ .ready → st.currentNowhere t

/-- Between scheduling points a thread not `.ready` is current nowhere. -/
theorem blockedCurrentNowhere_of_currentDequeuedUnique {st : SystemState}
    (hD : st.currentDequeuedUnique) : blockedCurrentNowhere st := fun t tcb hT hB c hc => by
  obtain ⟨x, hx, hr⟩ := hD.runnable hc
  rw [hT] at hx; cases hx; exact hB hr.1

/-- Every notification's head waiter is current nowhere and blocked: the thread
a signal wakes. -/
def notificationHeadsWakeable (st : SystemState) : Prop :=
  ∀ nid ntfn, st.getNotification? nid = some ntfn → ∀ w, ntfn.waitHead = some w →
    st.currentNowhere w ∧ blockedAt st w

theorem notificationHeadsWakeable.head {st : SystemState}
    (h : notificationHeadsWakeable st) {nid : SeLe4n.ObjId} {ntfn : Notification}
    {w : SeLe4n.ThreadId} (hN : st.getNotification? nid = some ntfn)
    (hW : ntfn.waitHead = some w) : st.currentNowhere w :=
  (h nid ntfn hN w hW).1

theorem notificationHeadsWakeable.blocked {st : SystemState}
    (h : notificationHeadsWakeable st) {nid : SeLe4n.ObjId} {ntfn : Notification}
    {w : SeLe4n.ThreadId} (hN : st.getNotification? nid = some ntfn)
    (hW : ntfn.waitHead = some w) : blockedAt st w :=
  (h nid ntfn hN w hW).2

/-- A TCB read after a write to `tid`'s TCB: `f` applied where the two threads
share an object slot. -/
theorem updateTcb_getTcb?_eq {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (w : SeLe4n.ThreadId) :
    (st.updateTcb tid f).getTcb? w =
      if tid.toObjId = w.toObjId then (st.getTcb? w).map f else st.getTcb? w := by
  split
  · rename_i h
    have hk : ∀ s : SystemState, s.getTcb? w = s.getTcb? tid := fun s => by
      unfold SystemState.getTcb?; rw [h]
    rw [hk, hk st, SystemState.updateTcb_getTcb?_self _ _ _ hInv]
  · exact SystemState.updateTcb_getTcb?_ne _ _ _ hInv w ‹_›

/-- A write to one TCB that keeps its IPC state: every TCB after it has a TCB
before it in the same IPC state. -/
theorem updateTcb_getTcb?_back {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).ipcState = x.ipcState) {w : SeLe4n.ThreadId}
    {t' : TCB} (h : (st.updateTcb tid f).getTcb? w = some t') :
    ∃ t, st.getTcb? w = some t ∧ t.ipcState = t'.ipcState := by
  rw [updateTcb_getTcb?_eq hInv] at h
  split at h
  · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨t, ht, (hf t).symm⟩
  · exact ⟨t', h, rfl⟩

/-- …and every TCB before it has one after it in the same IPC state. -/
theorem updateTcb_getTcb?_fwd {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).ipcState = x.ipcState) {w : SeLe4n.ThreadId}
    {t : TCB} (h : st.getTcb? w = some t) :
    ∃ t', (st.updateTcb tid f).getTcb? w = some t' ∧ t'.ipcState = t.ipcState := by
  rw [updateTcb_getTcb?_eq hInv]
  split
  · exact ⟨f t, by rw [h]; rfl, hf t⟩
  · exact ⟨t, h, rfl⟩

/-- A TCB write leaves every object that is no TCB where it was. -/
theorem updateTcb_objects_back_nonTcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (hInv : st.objects.invExt) {k : SeLe4n.ObjId} {o : KernelObject}
    (ho : ∀ t, o ≠ .tcb t) (h : (st.updateTcb tid f).objects[k]? = some o) :
    st.objects[k]? = some o := by
  by_cases hk : tid.toObjId = k
  · subst hk
    cases hT : st.getTcb? tid with
    | none => rwa [SystemState.updateTcb_eq_self_of_none hT] at h
    | some t =>
      have h1 := SystemState.updateTcb_getTcb?_self st tid f hInv
      rw [hT] at h1
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h1] at h
      exact absurd (Option.some.inj h).symm (ho _)
  · rwa [SystemState.updateTcb_objects_ne _ _ _ _ hk hInv] at h

/-- A TCB write that keeps the thread's IPC state keeps every endpoint head
wakeable. -/
theorem endpointHeadsWakeable.updateTcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (h : endpointHeadsWakeable st) (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).ipcState = x.ipcState) : endpointHeadsWakeable (st.updateTcb tid f) := by
  intro epId ep hE r hr
  have hE0 : st.getEndpoint? epId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr (updateTcb_objects_back_nonTcb hInv
      (fun _ h => by cases h) ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE))
  obtain ⟨hN, hB⟩ := h epId ep hE0 r hr
  refine ⟨fun c => by rw [SystemState.updateTcb_scheduler]; exact hN c, fun t' hT => ?_⟩
  obtain ⟨t, ht, hs⟩ := updateTcb_getTcb?_back hInv hf hT
  rw [← hs]; exact hB t ht

/-- A thread blocked on a reply is current nowhere. -/
theorem blockedCurrentNowhere.blockedOnReply {st : SystemState}
    (h : blockedCurrentNowhere st) {t : SeLe4n.ThreadId} {tcb : TCB}
    {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId} (hT : lookupTcb st t = some tcb)
    (hS : tcb.ipcState = .blockedOnReply e r) : st.currentNowhere t :=
  h t tcb (getTcb?_of_lookupTcb st t tcb hT) (by rw [hS]; exact fun h => by cases h)

/-- A thread blocked in a receive is current nowhere. -/
theorem blockedCurrentNowhere.blockedOnReceive {st : SystemState}
    (h : blockedCurrentNowhere st) {t : SeLe4n.ThreadId} {tcb : TCB}
    {e : SeLe4n.ObjId} (hT : st.getTcb? t = some tcb)
    (hS : tcb.ipcState = .blockedOnReceive e) : st.currentNowhere t :=
  h t tcb hT (by rw [hS]; exact fun h => by cases h)

/-- The head a pop returns was a head before it. -/
theorem endpointHeadsWakeable.popped_head {st st' : SystemState}
    (hHeads : endpointHeadsWakeable st) {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {r : SeLe4n.ThreadId} {tcb : TCB}
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (r, tcb, st')) :
    st.currentNowhere r ∧ blockedAt st r := by
  have hE : ∃ ep, st.objects[endpointId]? = some (.endpoint ep) := by
    unfold endpointQueuePopHead SystemState.getObject? at hPop
    split at hPop
    · exact ⟨_, ‹_›⟩
    all_goals cases hPop
  obtain ⟨ep, hObj⟩ := hE
  have hH := endpointQueuePopHead_returns_head _ _ _ ep r st' hObj hPop
  have hT : st.getTcb? r = some tcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr
    (endpointQueuePopHead_returns_pre_tcb _ _ _ ep r tcb st' hObj hPop)
  have h := hHeads endpointId ep ((SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hObj) r
    (by cases isReceiveQ
        · exact .inr hH
        · exact .inl hH)
  exact ⟨h.1, tcb, hT, h.2 tcb hT⟩

/-- The thread a head pop returns is current nowhere after the pop. -/
theorem endpointHeadsWakeable.popped {st st' : SystemState}
    (hHeads : endpointHeadsWakeable st) {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {r : SeLe4n.ThreadId} {tcb : TCB}
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (r, tcb, st')) :
    st'.currentNowhere r :=
  (hHeads.popped_head hPop).1.of_scheduler_eq (endpointQueuePopHead_scheduler_eq _ _ _ _ _ hPop)

/-- The thread a head pop returns was blocked before the pop. -/
theorem endpointHeadsWakeable.popped_blocked {st st' : SystemState}
    (hHeads : endpointHeadsWakeable st) {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {r : SeLe4n.ThreadId} {tcb : TCB}
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (r, tcb, st')) :
    blockedAt st r :=
  (hHeads.popped_head hPop).2

/-- **A head pop, then an IPC-state store over the popped thread, which was
blocked** (`hB`, read off the TCB the pop returns): the receive's hand-over of
a calling sender to `.blockedOnReply`. -/
theorem endpointQueuePopHead_then_blockedStore_runQueueStage {st st1 st2 : SystemState}
    {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool} {r : SeLe4n.ThreadId} {rTcb : TCB}
    {s : ThreadIpcState} {m : Option IpcMessage}
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (r, rTcb, st1))
    (hS : storeTcbIpcStateAndMessage st1 r s m = .ok st2) (hB : rTcb.ipcState ≠ .ready) :
    RunQueueStage st st2 := by
  have hE : ∃ ep, st.objects[endpointId]? = some (.endpoint ep) := by
    unfold endpointQueuePopHead SystemState.getObject? at hPop
    split at hPop
    · exact ⟨_, ‹_›⟩
    all_goals cases hPop
  obtain ⟨ep, hObj⟩ := hE
  have hPre := endpointQueuePopHead_returns_pre_tcb _ _ _ ep r rTcb st1 hObj hPop
  refine RunQueueStage.of_invExt fun hInv => (endpointQueuePopHead_runQueueStage hPop).trans
    (storeTcbIpcStateAndMessage_blockedRunQueueStage hS fun x hx => ?_)
  obtain ⟨y, hy, he⟩ := endpointQueuePopHead_tcb_ipcState_backward _ _ _ _ r r x hInv hPop
    (lookupTcb_some_objects st1 r x hx)
  rw [hPre] at hy; cases hy; rw [← he]; exact hB

/-- A step that keeps the scheduler keeps core `c`'s current thread. -/
theorem currentOnCore_of_scheduler_eq {st st' : SystemState} {c : Concurrency.CoreId}
    {t : SeLe4n.ThreadId} (h : st'.scheduler = st.scheduler)
    (hCur : st.scheduler.currentOnCore c = some t) : st'.scheduler.currentOnCore c = some t := by
  rw [h]; exact hCur

/-- **The cross-core call** of core `c`'s current thread: queue operations,
IPC-state stores, the receiver's wake and the reply link, then the block of the
caller and its deschedule — a scheduling point opened and closed.  The receiver
it wakes is the endpoint's receive-queue head (`hHeads`); the caller is no idle
thread (an idle thread runs in the kernel and makes no call). -/
theorem endpointCallOnCore_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload) (c : Concurrency.CoreId)
    (st : SystemState) (hHeads : endpointHeadsWakeable st)
    (hCur : st.scheduler.currentOnCore c = some caller) (hNI : isIdleThreadId caller = false) :
    SystemState.RunQueueEntryStage st (endpointCallOnCore endpointId caller payload c st).1 := by
  unfold endpointCallOnCore
  split
  · rename_i ep hEp
    split
    · rename_i r hHead
      split
      · exact (RunQueueStage.refl _).entry
      · rename_i receiver tcb st1 hPop
        split
        · exact (RunQueueStage.refl _).entry
        · rename_i st2 hS2
          have hN : st2.currentNowhere receiver := (hHeads.popped hPop).of_scheduler_eq
            (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2)
          have hC2 : st2.scheduler.currentOnCore c = some caller :=
            currentOnCore_of_scheduler_eq (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2)
              (currentOnCore_of_scheduler_eq (endpointQueuePopHead_scheduler_eq _ _ _ _ _ hPop) hCur)
          have hC3 : (wakeThread st2 receiver c).1.scheduler.currentOnCore c = some caller := by
            show (enqueueRunnableOnCore st2 _ receiver).scheduler.currentOnCore c = _
            rw [enqueueRunnableOnCore_currentOnCore]; exact hC2
          split
          · exact (RunQueueStage.refl _).entry
          · rename_i st4 hS4
            split
            · exact (RunQueueStage.refl _).entry
            · rename_i st5 hS5
              have hC5 : st5.scheduler.currentOnCore c = some caller :=
                currentOnCore_of_scheduler_eq (linkServerStashedReply_scheduler_eq _ _ _ _ hS5)
                  (currentOnCore_of_scheduler_eq
                    (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS4) hC3)
              exact ((((endpointQueuePopHead_runQueueStage hPop).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS2 rfl)).then_wake c hN
                (hHeads.popped_blocked hPop)).window (.block c) |>.trans
                ((storeTcbIpcStateAndMessage_runQueueBlockStage hS4 hC3 hNI).trans
                ((linkServerStashedReply_runQueueStage hS5).window _))).dispatch
                ((SystemState.RunQueueDispatchStage.descheduleCurrent st5 c caller hC5).trans_stage
                  (SystemState.linkReplyWaiter_runQueueStage _ caller receiver))
    · split
      · exact (RunQueueStage.refl _).entry
      · rename_i st1 hE
        split
        · exact (RunQueueStage.refl _).entry
        · rename_i st2 hS2
          have hC1 : st1.scheduler.currentOnCore c = some caller :=
            currentOnCore_of_scheduler_eq (endpointQueueEnqueue_scheduler_eq _ _ _ _ _ hE) hCur
          exact (((endpointQueueEnqueue_runQueueStage hE).window (.block c)).trans
            (storeTcbIpcStateAndMessage_runQueueBlockStage hS2 hC1 hNI)).dispatch
            ((SystemState.RunQueueDispatchStage.descheduleCurrent st2 c caller
              (currentOnCore_of_scheduler_eq
                (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2) hC1)).trans_stage
              (recordSendCap_runQueueStage _ caller _ _))
  · split <;> exact (RunQueueStage.refl _).entry

-- ============================================================================
-- Capability transfer and donation
-- ============================================================================

/-- A free-index write writes no reference table. -/
theorem setCapFreeIndex_referenceTables (st : SystemState) (addr : CSpaceAddr) (idx : Nat) :
    (setCapFreeIndex st addr idx).referenceTables = st.referenceTables := by
  cases hO : st.objects[addr.cnode]? with
  | some o =>
    cases o with
    | cnode cn => exact storeObject_referenceTables (setCapFreeIndex_eq_storeObject hO)
    | _ => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]
  | none => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]

/-- Setting an untyped source full writes no reference table. -/
theorem untypedSourceSetFull_referenceTables (st : SystemState) (src : CSpaceAddr)
    (cap : Capability) : (untypedSourceSetFull st src cap).referenceTables = st.referenceTables :=
  untypedSourceSetFull_of (P := fun s => s.referenceTables = st.referenceTables) rfl
    fun idx => setCapFreeIndex_referenceTables st src idx

/-- A derivation-tree edge writes no reference table. -/
theorem cdtAddChild_referenceTables (st : SystemState) (p c : SlotRef) (op : DerivationOp) :
    (st.cdtAddChild p c op).referenceTables = st.referenceTables := by
  simp only [SystemState.referenceTables, SystemState.cdtAddChild_irqHandlers]

/-- A slot insert writes no reference table. -/
theorem cspaceInsertSlot_referenceTables {st st' : SystemState} {addr : CSpaceAddr}
    {cap : Capability} (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.referenceTables = st.referenceTables := by
  obtain ⟨_, _, _, _, hStore⟩ := cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_referenceTables hStore

/-- One capability's transfer writes no reference table. -/
theorem ipcTransferSingleCap_referenceTables {cap : Capability} {srcNode : SlotRef}
    {receiverRoot : SeLe4n.ObjId} {slotBase : SeLe4n.Slot} {scanLimit : Nat}
    {st st' : SystemState} {result : CapTransferResult}
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.referenceTables = st.referenceTables := by
  obtain ⟨_, -, ⟨rfl, -⟩ | ⟨_, _, -, -, -, hIns, -, rfl⟩⟩ := ipcTransferSingleCap_ok_cases hStep
  · rfl
  · rw [untypedSourceSetFull_referenceTables, cdtAddChild_referenceTables]
    exact cspaceInsertSlot_referenceTables hIns

theorem ipcUnwrapCapsLoop_referenceTables
    (caps : Array TransferCap) (receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCapsLoop caps receiverRoot idx nextBase accResults fuel st
             = .ok (summary, st')) :
    st'.referenceTables = st.referenceTables := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep; rfl
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none => simp [hCap] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    | some tc =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap tc.cap tc.srcSlot
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        obtain ⟨_, rfl⟩ := hStep; rfl
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hT := ipcTransferSingleCap_referenceTables hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => rw [ih _ _ _ _ hStep, hT]
        | noSlot => rw [ih _ _ _ _ hStep, hT]
        | grantDenied => rw [ih _ _ _ _ hStep, hT]
        | sourceRevoked => rw [ih _ _ _ _ hStep, hT]

/-- The objects at a key agreeing up to derivation metadata hold the same table
back-links: a CNode and a thread hold none. -/
theorem _root_.SeLe4n.Model.SystemState.objectAgreesOffDerivationMetadataAt.tableBackLinks
    {st st' : SystemState} {oid : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationMetadataAt st' st oid) :
    objTableBackLinks st'.objects[oid]? = objTableBackLinks st.objects[oid]? := by
  rcases h with e | ⟨_, _, ha, hb, _⟩ | ⟨_, _, ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]; rfl
  · rename_i hw; rw [ha, hb]
    simp only [objTableBackLinks_some, KernelObject.tableBackLinks,
      TCB.proj_eq_of_withoutLinks_eq (·.taintWords) hw]

/-- **The capability transfer keeps the table references**: it writes no
reference table, and every object it writes is a CNode or a thread's links. -/
theorem ipcUnwrapCaps_tableReferenceFrame {caps : Array TransferCap} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {grant : Bool} {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps root base grant st = .ok (summary, st')) :
    SystemState.TableReferenceFrame st st' := by
  refine ⟨?_, fun k => ?_⟩
  · unfold ipcUnwrapCaps at h
    split at h
    · simp at h; obtain ⟨_, rfl⟩ := h; rfl
    · exact ipcUnwrapCapsLoop_referenceTables _ _ _ _ _ _ _ _ _ h
  · by_cases hk : k = root
    · subst hk
      rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode caps k base grant st st' summary
        hObjInv h with e | ⟨cn', hc⟩
      · rw [e]
      · cases hC : st.getCNode? k with
        | none => rw [ipcUnwrapCaps_state_eq_of_root_not_cnode caps k base grant st st' summary hC h]
        | some cn => rw [hc, (SystemState.getCNode?_eq_some_iff st k cn).mp hC]; rfl
    · exact (ipcUnwrapCaps_preserves_objects_ne caps root base grant st st' summary
        k hk hObjInv h).tableBackLinks

/-- The objects at a key agreeing up to derivation metadata hold the same
release links: a CNode and a thread hold none. -/
theorem _root_.SeLe4n.Model.SystemState.objectAgreesOffDerivationMetadataAt.releaseLinkOn
    {st st' : SystemState} {oid : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationMetadataAt st' st oid) (c : Concurrency.CoreId) :
    SystemState.objReleaseLinkOn st'.objects[oid]? c =
      SystemState.objReleaseLinkOn st.objects[oid]? c := by
  rcases h with e | ⟨_, _, ha, hb, _⟩ | ⟨_, _, ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]; rfl
  · rw [ha, hb]; rfl

/-- **The capability transfer holds the release queues**: it writes no
scheduler slot, and every object it writes is a CNode or a thread's links. -/
theorem ipcUnwrapCaps_releaseStateAgree {caps : Array TransferCap} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {grant : Bool} {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps root base grant st = .ok (summary, st')) :
    SystemState.releaseStateAgree st' st := by
  refine ⟨.of_objReleaseLinkOn fun k c => ?_,
    by rw [ipcUnwrapCaps_preserves_scheduler caps root base grant st st' summary h]⟩
  by_cases hk : k = root
  · subst hk
    rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode caps k base grant st st' summary
      hObjInv h with e | ⟨cn', hc⟩
    · rw [e]
    · cases hC : st.getCNode? k with
      | none => rw [ipcUnwrapCaps_state_eq_of_root_not_cnode caps k base grant st st' summary hC h]
      | some cn => rw [hc, (SystemState.getCNode?_eq_some_iff st k cn).mp hC]; rfl
  · exact (ipcUnwrapCaps_preserves_objects_ne caps root base grant st st' summary
      k hk hObjInv h).releaseLinkOn c

/-- The objects at a key agreeing up to derivation metadata hold the same
refill view: a CNode and a thread hold none. -/
theorem _root_.SeLe4n.Model.SystemState.objectAgreesOffDerivationMetadataAt.refillView
    {st st' : SystemState} {oid : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationMetadataAt st' st oid) :
    objRefillView st'.objects[oid]? = objRefillView st.objects[oid]? := by
  rcases h with e | ⟨_, _, ha, hb, _⟩ | ⟨_, _, ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]; rfl
  · rw [ha, hb]; rfl

/-- The capability transfer keeps every context's refill view: every object it
writes is a CNode or a thread's links. -/
theorem ipcUnwrapCaps_refillViewsKept {caps : Array TransferCap} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {grant : Bool} {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps root base grant st = .ok (summary, st')) :
    RefillViewsKept st' st := by
  refine .of_eq fun k => ?_
  by_cases hk : k = root
  · subst hk
    rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode caps k base grant st st' summary
      hObjInv h with e | ⟨cn', hc⟩
    · rw [e]
    · cases hC : st.getCNode? k with
      | none => rw [ipcUnwrapCaps_state_eq_of_root_not_cnode caps k base grant st st' summary hC h]
      | some cn => rw [hc, (SystemState.getCNode?_eq_some_iff st k cn).mp hC]; rfl
  · exact (ipcUnwrapCaps_preserves_objects_ne caps root base grant st st' summary
      k hk hObjInv h).refillView

/-- The objects at a key agreeing up to derivation metadata hold the same
yield codes: a CNode holds none and a thread's links are not its yield code. -/
theorem _root_.SeLe4n.Model.SystemState.objectAgreesOffDerivationMetadataAt.yieldCodes
    {st st' : SystemState} {oid : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationMetadataAt st' st oid) :
    objYieldCodes st'.objects[oid]? = objYieldCodes st.objects[oid]? := by
  rcases h with e | ⟨_, _, ha, hb, _⟩ | ⟨_, _, ha, hb, e⟩
  · rw [e]
  · rw [ha, hb]; rfl
  · have e2 := congrArg TCB.yieldToCode e
    rw [ha, hb]; exact congrArg (fun n => (n, 0)) e2

/-- The capability transfer keeps every yield code: every object it writes is
a CNode or a thread's links. -/
theorem ipcUnwrapCaps_yieldLinksKept {caps : Array TransferCap} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {grant : Bool} {st st' : SystemState} {summary : CapTransferSummary}
    (hObjInv : st.objects.invExt)
    (h : ipcUnwrapCaps caps root base grant st = .ok (summary, st')) :
    YieldLinksKept st' st := fun k => by
  by_cases hk : k = root
  · subst hk
    rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode caps k base grant st st' summary
      hObjInv h with e | ⟨cn', hc⟩
    · rw [e]
    · cases hC : st.getCNode? k with
      | none => rw [ipcUnwrapCaps_state_eq_of_root_not_cnode caps k base grant st st' summary hC h]
      | some cn => rw [hc, (SystemState.getCNode?_eq_some_iff st k cn).mp hC]; rfl
  · exact (ipcUnwrapCaps_preserves_objects_ne caps root base grant st st' summary
      k hk hObjInv h).yieldCodes

/-- The cap transfer writes CNodes, the derivation tree and slot links: every
thread's TCB reads as it did off its slot links. -/
theorem ipcUnwrapCaps_runQueueStage {caps : Array TransferCap} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {grant : Bool} {st st' : SystemState} {summary : CapTransferSummary}
    (h : ipcUnwrapCaps caps root base grant st = .ok (summary, st')) : RunQueueStage st st' :=
  have hS := ipcUnwrapCaps_preserves_scheduler caps root base grant st st' summary h
  RunQueueStage.of_placement
    (fun hInv => ipcUnwrapCaps_preserves_objects_invExt caps root base grant st st' summary hInv h)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => TCB.map_proj_of_map_withoutLinks_eq TCB.placement
      (ipcUnwrapCaps_getTcb?_eq caps root base grant st st' summary x hInv h))
    (fun hInv => SystemState.StateMono.of_stateFields fun x =>
      TCB.map_proj_of_map_withoutLinks_eq (fun t => (t.ipcState, t.threadState, t.cpuAffinity))
        (ipcUnwrapCaps_getTcb?_eq caps root base grant st st' summary x hInv h))
    (fun hInv => ipcUnwrapCaps_tableReferenceFrame hInv h)
    (fun hInv => ipcUnwrapCaps_releaseStateAgree hInv h)
    (fun hInv => ipcUnwrapCaps_refillViewsKept hInv h)
    (fun hInv => ipcUnwrapCaps_yieldLinksKept hInv h)
    (hRes := by rw [ipcUnwrapCaps_preserves_machine caps root base grant st st' summary h])

/-- WS-ZA ZA4.7: the rendezvous capability lookup: CDT writes, then the
receiver-side unwrap. -/
theorem receiveTransferCaps_runQueueStage
    {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {st st' : SystemState} {summary : CapTransferSummary}
    (h : receiveTransferCaps req root base st = .ok (summary, st')) : RunQueueStage st st' := by
  unfold receiveTransferCaps at h
  cases req with
  | none =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact .refl _
  | some r =>
      obtain ⟨cr, addrs, depth⟩ := r
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact .refl _
      · exact ipcUnwrapCaps_runQueueStage h

/-- The donation rebinds a context and two threads' bindings: no run-queue
field moves. -/
theorem donateSchedContext_runQueueStage {st st' : SystemState}
    {client server : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    (h : donateSchedContext st client server scId = .ok st') : RunQueueStage st st' :=
  have hS := donateSchedContext_scheduler_eq st st' client server scId h
  RunQueueStage.of_placement
    (fun hInv => donateSchedContext_preserves_objects_invExt st st' client server scId hInv h)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => donateSchedContext_getTcb?_placement_eq st st' client server scId hInv h x)
    (fun hInv => SystemState.StateMono.of_stateFields
      (donateSchedContext_getTcb?_stateFields_eq st st' client server scId hInv h))
    (fun hInv => .of_kindPreservingWrite
      (donateSchedContext_kindPreservingWrite st st' client server scId hInv h)
      (donateSchedContext_referenceTables h))
    (fun hInv => donateSchedContext_releaseStateAgree st st' client server scId hInv h)
    (fun hInv => donateSchedContext_refillViewsKept st st' client server scId hInv h)
    (fun hInv => donateSchedContext_yieldLinksKept st st' client server scId hInv h)
    (by rw [hS])
    (by rw [donateSchedContext_machine_eq st st' client server scId h])

theorem applyCallDonation_runQueueStage {st st' : SystemState}
    {callerV receiverV : SeLe4n.ValidThreadId}
    (h : applyCallDonation st callerV receiverV = .ok st') : RunQueueStage st st' := by
  rw [applyCallDonation_characterisation] at h
  split at h
  · exact donateSchedContext_runQueueStage h
  · cases h; exact RunQueueStage.refl _

theorem applyCallDonationOnCore_runQueueStage {st st' : SystemState}
    {callerV receiverV : SeLe4n.ValidThreadId} {donorHome doneeHome : Concurrency.CoreId}
    (h : applyCallDonationOnCore st callerV receiverV donorHome doneeHome = .ok st') :
    RunQueueStage st st' := by
  obtain ⟨st1, hDon, harm⟩ :=
    applyCallDonationOnCore_ok_decompose st st' callerV receiverV donorHome doneeHome h
  rcases harm with ⟨-, rfl⟩ | ⟨scId, -, rfl⟩
  · exact applyCallDonation_runQueueStage hDon
  · exact (applyCallDonation_runQueueStage hDon).trans
      (migrateSchedContextReplenishment_runQueueStage _ _ _ _)

-- ============================================================================
-- Call dispatch
-- ============================================================================

theorem endpointCallWithCapsOnCore_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some caller)
    (hNI : isIdleThreadId caller = false) :
    SystemState.RunQueueEntryStage st
      (endpointCallWithCapsOnCore endpointId caller payload base c st).1 := by
  have s0 := endpointCallOnCore_runQueueEntryStage endpointId caller payload c st hHeads hCur hNI
  unfold endpointCallWithCapsOnCore
  generalize endpointCallOnCore endpointId caller payload c st = r at s0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact s0
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact s0
      | (rename_i hU; exact s0.trans (receiveTransferCaps_runQueueStage hU).entry)

theorem endpointCallCrossCoreDispatch_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some caller)
    (hNI : isIdleThreadId caller = false) :
    SystemState.RunQueueEntryStage st
      (endpointCallCrossCoreDispatch endpointId caller payload base c st).1 := by
  have s0 := endpointCallWithCapsOnCore_runQueueEntryStage endpointId caller payload base c st
    hHeads hCur hNI
  unfold endpointCallCrossCoreDispatch
  generalize endpointCallWithCapsOnCore endpointId caller payload base c st = r at s0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact s0
  | ok res =>
    dsimp only
    repeat' split
    all_goals first
      | exact s0
      | (rename_i hD; exact s0.trans ((applyCallDonationOnCore_runQueueStage hD).trans
          (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)).entry)

-- ============================================================================
-- Delivery staging and fault delivery
-- ============================================================================

theorem writeReturnFrameToTcb_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) :
    RunQueueStage st (Architecture.writeReturnFrameToTcb st tid frame) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

theorem writeDeliveredFrameToTcb_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) :
    RunQueueStage st (Architecture.writeDeliveredFrameToTcb st tid frame) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

theorem recordPhysicalWrites_runQueueStage (st : SystemState)
    (ws : List Architecture.PhysicalWrite) :
    RunQueueStage st (Architecture.recordPhysicalWrites st ws) :=
  RunQueueStage.of_frame rfl rfl rfl

theorem stageDeliveredMessage_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (n : Nat) : RunQueueStage st (Architecture.stageDeliveredMessage st tid n) := by
  unfold Architecture.stageDeliveredMessage
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact (writeDeliveredFrameToTcb_runQueueStage _ _ _).trans
        (recordPhysicalWrites_runQueueStage _ _)

theorem stageWokenDelivery_runQueueStage (st : SystemState) (w? : Option SeLe4n.ThreadId)
    (n : Nat) : RunQueueStage st (Architecture.stageWokenDelivery st w? n) := by
  cases w? with
  | none => exact RunQueueStage.refl _
  | some tid => exact stageDeliveredMessage_runQueueStage st tid n

theorem recordPendingFault_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) : RunQueueStage st (recordPendingFault st tid tf) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

/-- **A deschedule on core `c`, then a write to the descheduled thread that may
mark it inactive** — the fault suspend and the fault abandon.  Between
scheduling points the thread is queued on `c` at most and run by `c` at most,
and is `.ready` (`hQ`, `hC`, `hRdy`); the deschedule takes it off both, so the
write lands on a thread no core runs and no queue holds, and leaves it
coherent. -/
theorem descheduleThenOffWrite_runQueueEntryStage (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : Concurrency.CoreId) {f : TCB → TCB}
    (hQ : st.currentDequeuedUnique → ∀ c', st.queuedOn c' tid = true → c' = c)
    (hC : st.currentDequeuedUnique → ∀ c', st.scheduler.currentOnCore c' = some tid → c' = c)
    (hRdy : st.currentDequeuedUnique → ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hNI : isIdleThreadId tid = false) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hReady : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready)
    (hWf : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hYf : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    SystemState.RunQueueEntryStage st ((removeRunnableOnCore st tid c).updateTcb tid f) := by
  have hS := SystemState.RunQueueStage.runDescheduleOnCore st c tid
  refine ⟨hS.1.trans (SystemState.RunQueueLinkStage.updateTcb _ tid hf hWf hYf),
    fun hInv hR _ d => ?_⟩
  obtain ⟨hInv1, hR1⟩ := hS.1 hInv hR
  refine SystemState.currentDequeuedUniqueExcept_updateTcb_offWrite hInv1
    (hS.2.1 none hInv hR hR1 d) (fun c' h => ?_) (fun c' => ?_) hNI hf (fun x hx => ?_)
  · have h' : (st.runDescheduleOnCore c tid).scheduler.currentOnCore c' = some tid := h
    rw [SystemState.runDescheduleOnCore_currentOnCore] at h'
    split at h'
    · cases h'
    · rename_i hn; have e := hC d c' h'; subst e; exact hn ⟨rfl, h'⟩
  · show (st.runDescheduleOnCore c tid).queuedOn c' tid = false
    rw [SystemState.runDescheduleOnCore_queuedOn]
    split
    · rfl
    · rename_i hn
      cases hq : st.queuedOn c' tid
      · rfl
      · exact absurd ⟨rfl, hQ d c' hq⟩ hn
  · have e := SystemState.runDescheduleOnCore_getTcb?_ipcState st c tid tid
    have hx' : (st.runDescheduleOnCore c tid).getTcb? tid = some x := hx
    rw [hx'] at e
    cases hT : st.getTcb? tid with
    | none => rw [hT] at e; cases e
    | some y =>
      rw [hT] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact .inl (hReady x (e.trans (hRdy d y hT)))

/-- **A deschedule where the thread is placed, then an off-queue write**: the
fault abandon.  Between scheduling points a thread is queued on one core at most
and is not queued where it runs, so the core `placedCoreOf?` finds is the only
one holding it; a thread placed nowhere is left where it is. -/
theorem placedThenOffWrite_runQueueEntryStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c₀ : Concurrency.CoreId) {f : TCB → TCB}
    (hRdy : st.currentDequeuedUnique → ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hNI : isIdleThreadId tid = false) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hReady : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready)
    (hWf : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hYf : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    SystemState.RunQueueEntryStage st
      ((removeRunnableOnCore st tid ((placedCoreOf? st tid).getD c₀)).updateTcb tid f) := by
  refine descheduleThenOffWrite_runQueueEntryStage st tid _ (fun d c' hq => ?_)
    (fun d c' hc => ?_) hRdy hNI hf hReady hWf hYf
  · cases hP : placedCoreOf? st tid with
    | none => rw [((placedCoreOf?_none_iff st tid).mp hP c').1] at hq; cases hq
    | some c =>
      have hS := placedCoreOf?_sound st tid c hP
      simp only [Option.getD_some]
      rcases Bool.or_eq_true_iff.mp hS with h | h
      · exact SystemState.queuedOn_core_unique hq h
      · rw [d.not_queued (beq_iff_eq.mp h) c'] at hq; cases hq
  · cases hP : placedCoreOf? st tid with
    | none => exact absurd hc ((placedCoreOf?_none_iff st tid).mp hP c').2
    | some c =>
      have hS := placedCoreOf?_sound st tid c hP
      simp only [Option.getD_some]
      rcases Bool.or_eq_true_iff.mp hS with h | h
      · rw [d.not_queued hc c] at h; cases h
      · exact (d.current c tid (beq_iff_eq.mp h)).2.1 c' hc

/-- **A deschedule where the thread is placed, then one off-queue write**: a
final delete's suspend, the removal and the `.Inactive` mark.  As
`placedThenOffWrite_runQueueEntryStage`, with the removal skipped for a thread
placed nowhere. -/
theorem descheduleAtPlacedThenOffWrite_runQueueEntryStage (st : SystemState)
    (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hRdy : st.currentDequeuedUnique → ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hNI : isIdleThreadId tid = false) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hReady : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready)
    (hWf : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hYf : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    SystemState.RunQueueEntryStage st
      ((descheduleAt st tid (placedCoreOf? st tid)).updateTcb tid f) := by
  cases hP : placedCoreOf? st tid with
  | none =>
    refine ⟨SystemState.RunQueueLinkStage.updateTcb st tid hf hWf hYf, fun hInv _ _ d => ?_⟩
    exact SystemState.currentDequeuedUniqueExcept_updateTcb_offWrite hInv d
      (fun c => ((placedCoreOf?_none_iff st tid).mp hP c).2)
      (fun c => ((placedCoreOf?_none_iff st tid).mp hP c).1) hNI hf
      (fun x hx => .inl (hReady x (hRdy d x hx)))
  | some c =>
    have e : (placedCoreOf? st tid).getD c = c := by rw [hP]; rfl
    have h := placedThenOffWrite_runQueueEntryStage st tid c hRdy hNI hf hReady hWf hYf
    rw [e] at h
    exact h

/-- **A deschedule where the thread is placed, then two off-queue writes**: the
suspend's removal, pending-state clear and `.Inactive` mark.  As
`placedThenOffWrite_runQueueEntryStage`, with the removal skipped for a thread
placed nowhere. -/
theorem descheduleAtPlacedThenOffWrites_runQueueEntryStage (st : SystemState)
    (tid : SeLe4n.ThreadId) {f g : TCB → TCB}
    (hRdy : st.currentDequeuedUnique → ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hNI : isIdleThreadId tid = false) (hf : ∀ x c, (f x).runLinkOn c = x.runLinkOn c)
    (hg : ∀ x c, (g x).runLinkOn c = x.runLinkOn c)
    (hReady : ∀ x, x.ipcState = .ready → (g (f x)).ipcState = .ready)
    (hWf : ∀ x, (f x).taintWords = x.taintWords := by taint_words_kept)
    (hWg : ∀ x, (g x).taintWords = x.taintWords := by taint_words_kept)
    (hYf : ∀ x, (f x).yieldToCode = x.yieldToCode := by yield_code_kept)
    (hYg : ∀ x, (g x).yieldToCode = x.yieldToCode := by yield_code_kept) :
    SystemState.RunQueueEntryStage st
      (((descheduleAt st tid (placedCoreOf? st tid)).updateTcb tid f).updateTcb tid g) := by
  have hW : ∀ s : SystemState, SystemState.RunQueueLinkStage s ((s.updateTcb tid f).updateTcb tid g) :=
    fun s => (SystemState.RunQueueLinkStage.updateTcb s tid hf hWf hYf).trans
      (SystemState.RunQueueLinkStage.updateTcb _ tid hg hWg hYg)
  cases hP : placedCoreOf? st tid with
  | none =>
    refine ⟨hW st, fun hInv _ _ d => ?_⟩
    exact SystemState.currentDequeuedUniqueExcept_updateTcb₂_offWrite hInv d
      (fun c => ((placedCoreOf?_none_iff st tid).mp hP c).2)
      (fun c => ((placedCoreOf?_none_iff st tid).mp hP c).1) hNI hf hg
      (fun x hx => .inl (hReady x (hRdy d x hx)))
  | some c =>
    have hS := SystemState.RunQueueStage.runDescheduleOnCore st c tid
    have hSound := placedCoreOf?_sound st tid c hP
    refine ⟨hS.1.trans (hW _), fun hInv hR _ d => ?_⟩
    obtain ⟨hInv1, hR1⟩ := hS.1 hInv hR
    refine SystemState.currentDequeuedUniqueExcept_updateTcb₂_offWrite hInv1
      (hS.2.1 none hInv hR hR1 d) (fun c' h => ?_) (fun c' => ?_) hNI hf hg (fun x hx => ?_)
    · have h' : (st.runDescheduleOnCore c tid).scheduler.currentOnCore c' = some tid := h
      rw [SystemState.runDescheduleOnCore_currentOnCore] at h'
      split at h'
      · cases h'
      · rename_i hn
        have e : c' = c := by
          rcases Bool.or_eq_true_iff.mp hSound with hq | hc
          · rw [d.not_queued h' c] at hq; cases hq
          · exact (d.current c tid (beq_iff_eq.mp hc)).2.1 c' h'
        subst e; exact hn ⟨rfl, h'⟩
    · show (st.runDescheduleOnCore c tid).queuedOn c' tid = false
      rw [SystemState.runDescheduleOnCore_queuedOn]
      split
      · rfl
      · rename_i hn
        cases hq : st.queuedOn c' tid
        · rfl
        · refine absurd ⟨rfl, ?_⟩ hn
          rcases Bool.or_eq_true_iff.mp hSound with h | h
          · exact SystemState.queuedOn_core_unique hq h
          · rw [d.not_queued (beq_iff_eq.mp h) c'] at hq; cases hq
    · have e := SystemState.runDescheduleOnCore_getTcb?_ipcState st c tid tid
      have hx' : (st.runDescheduleOnCore c tid).getTcb? tid = some x := hx
      rw [hx'] at e
      cases hT : st.getTcb? tid with
      | none => rw [hT] at e; cases e
      | some y =>
        rw [hT] at e
        simp only [Option.map_some, Option.some.injEq] at e
        exact .inl (hReady x (e.trans (hRdy d y hT)))

/-- The fault suspend of core `c`'s current thread. -/
theorem faultSuspendOnCore_runQueueEntryStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) (hCur : st.scheduler.currentOnCore c = some tid)
    (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueEntryStage st (faultSuspendOnCore st tid c) :=
  descheduleThenOffWrite_runQueueEntryStage st tid c
    (fun d c' hq => by rw [d.not_queued hCur c'] at hq; cases hq)
    (fun d c' h => (d.current c tid hCur).2.1 c' h)
    (fun d x hx => by
      obtain ⟨y, hy, hr⟩ := d.runnable hCur
      rw [hx] at hy; cases hy; exact hr.1)
    hNI (fun _ _ => rfl) (fun _ h => h)

theorem writeFaultRegistersToTcb_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : RunQueueStage st (writeFaultRegistersToTcb st tid w) :=
  RunQueueStage.updateTcb st tid (fun _ _ => rfl)

/-- The fault delivery for core `c`'s current thread: the handler call, or the
fail-closed suspend; then the woken handler's frame and the fault record. -/
theorem faultDeliverOnCore_runQueueEntryStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (fctx : FaultContext) (c : Concurrency.CoreId)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some tid)
    (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueEntryStage st (faultDeliverOnCore st tid f fctx c).1 := by
  have sus := (faultSuspendOnCore_runQueueEntryStage st tid c hCur hNI).trans
    (recordPendingFault_runQueueStage _ tid { fault := f, context := fctx }).entry
  unfold faultDeliverOnCore
  split
  · exact sus
  · rename_i tgt _
    have s0 := endpointCallCrossCoreDispatch_runQueueEntryStage tgt.endpoint tid
      (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st hHeads hCur hNI
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid
      (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st = r at s0 ⊢
    obtain ⟨st1, r⟩ := r
    cases r with
    | error e => exact sus
    | ok res =>
      exact s0.trans ((stageWokenDelivery_runQueueStage _ _ _).trans
        (recordPendingFault_runQueueStage _ _ _)).entry

theorem faultDeliverOnCoreChecked_runQueueEntryStage (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) (c : Concurrency.CoreId)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some tid)
    (hNI : isIdleThreadId tid = false) :
    SystemState.RunQueueEntryStage st (faultDeliverOnCoreChecked ctx st tid f fctx c).1 := by
  have sus := (faultSuspendOnCore_runQueueEntryStage st tid c hCur hNI).trans
    (recordPendingFault_runQueueStage _ tid { fault := f, context := fctx }).entry
  unfold faultDeliverOnCoreChecked
  split
  · exact sus
  · split
    · exact faultDeliverOnCore_runQueueEntryStage st tid f fctx c hHeads hCur hNI
    · exact sus

end SeLe4n.Kernel
