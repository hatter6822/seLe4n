/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.BlockedNotResident

/-!
# The syscall arms' readiness frames, and the syscall entry's carry

WS-ZA ZA6.20.  A syscall arm blocks the caller and no other thread: each arm is
`readyKeptStage` off the caller (`BlockedNotResident.lean`), composed over the
link stages its run-queue proof (`RunQueueEntryStage`) already names.  The
blocking arms block the caller with their one IPC-state store
(`storeTcbIpcStateAndMessage_readyKeptStage`); every other step is a run-queue,
switch or dispatch stage, which keeps `StateMono`, or a TCB write that keeps
the IPC state.  The frames are a family beside the arms' entry-stage proofs,
not a field of `RunQueueEntryStage`: a thread dispatched mid-step and blocked
later in the same step would break a field composed stage by stage.  The
routed dispatch, the checked entry and the ABI dispatch keep every thread but
the executing core's current thread ready
(`syscallDispatchFromAbi_readyKeptStage`), and
`syscallDispatchEntryState_preserves_blockedNotResident` closes the entry with
`settleThenActivateOnCore_blockedNotResident`.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

namespace readyKeptStage

variable {S : SeLe4n.ThreadId → Prop}

theorem of_eq {st st' : SystemState} (h : st' = st) : readyKeptStage S st st' := by
  subst h; exact refl _

end readyKeptStage

/-! ### Writes to one thread -/

/-- **A TCB store at a thread's own key keeps every other thread's readiness.** -/
theorem storeObject_tcb_readyKeptStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {o : KernelObject} (hS : storeObject tid.toObjId o st = .ok ((), st')) :
    readyKeptStage (· = tid) st st' := fun hI _ t hn hr x hx => by
  rw [storeObject_getTcb?_ne st st' _ _ t
    (fun h' => hn (ThreadId.toObjId_injective _ _ h')) hI hS] at hx
  exact hr x hx

theorem readyKeptStage.updateTcb {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready) :
    readyKeptStage S st (st.updateTcb tid f) :=
  fun hI _ => readyKeptExcept_updateTcb st tid f hI hf

/-- A deschedule, then an off-queue write that keeps a ready thread ready. -/
theorem removeRunnableThenWrite_readyKeptStage {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (f : TCB → TCB)
    (hf : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready) :
    readyKeptStage S st ((removeRunnableOnCore st tid c).updateTcb tid f) :=
  have hS := SystemState.RunQueueStage.runDescheduleOnCore st c tid
  (readyKeptStage.of_stage hS).trans hS.1 (.updateTcb _ tid f hf)

theorem descheduleAtThenWrite_readyKeptStage {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (c? : Option CoreId) (f : TCB → TCB)
    (hf : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready) :
    readyKeptStage S st ((descheduleAt st tid c?).updateTcb tid f) :=
  have hS := descheduleAt_runQueueStage st tid c?
  (readyKeptStage.of_stage hS).trans hS.1 (.updateTcb _ tid f hf)

/-! ### The notification wait and the replies -/

theorem notificationWait_block_readyKeptStage {st st1 st2 st3 : SystemState}
    {notificationId : SeLe4n.ObjId} {ntfn n' : Notification} {waiter : SeLe4n.ThreadId}
    {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage} {tail : Option SeLe4n.ThreadId}
    {c : CoreId}
    (hN : st.getNotification? notificationId = some ntfn)
    (hT : lookupTcb st waiter = some tcb)
    (hS1 : storeObject notificationId (.notification n') st = .ok ((), st1))
    (hS2 : storeTcbIpcStateAndMessage_fromTcb st1 waiter tcb s m = .ok st2)
    (hL : linkNtfnWaiter st2 waiter tail = .ok st3)
    (hCur : st.scheduler.currentOnCore c = some waiter) (hNI : isIdleThreadId waiter = false) :
    readyKeptStage (· = waiter) st (removeRunnableOnCore st3 waiter c) := by
  have hC1 : st1.scheduler.currentOnCore c = some waiter :=
    currentOnCore_of_scheduler_eq (storeObject_scheduler_eq _ _ _ _ hS1) hCur
  have hC3 : st3.scheduler.currentOnCore c = some waiter :=
    currentOnCore_of_scheduler_eq (linkNtfnWaiter_scheduler_eq hL)
      (currentOnCore_of_scheduler_eq (storeTcbIpcStateAndMessage_fromTcb_scheduler_eq hS2) hC1)
  have hNs := storeObject_notificationOver_runQueueStage hN hS1
  have w : SystemState.RunQueueWindowStage (.block c) st st2 :=
    SystemState.RunQueueWindowStage.of_invExt fun hInv => by
      have hNo := (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mp hN
      have hTo := lookupTcb_some_objects st waiter tcb hT
      have hNe : waiter.toObjId ≠ notificationId := by
        intro hEq; rw [hEq, hNo] at hTo; cases hTo
      have hT1 : st1.objects[waiter.toObjId]? = some (.tcb tcb) := by
        rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hS1, hTo]
      unfold storeTcbIpcStateAndMessage_fromTcb at hS2
      split at hS2
      · cases hS2
      · rename_i hS; cases hS2
        exact (hNs.window _).trans
          (SystemState.RunQueueWindowStage.storeObject_block hS
            ((SystemState.getTcb?_eq_some_iff st1 waiter tcb).mpr hT1) (fun _ => rfl) rfl hC1 hNI)
  have r2 : readyKeptStage (· = waiter) st st2 := by
    refine (readyKeptStage.of_stage hNs).trans hNs.1 ?_
    unfold storeTcbIpcStateAndMessage_fromTcb at hS2
    split at hS2
    · cases hS2
    · rename_i hS; cases hS2; exact storeObject_tcb_readyKeptStage hS
  have hL3 := linkNtfnWaiter_runQueueStage hL
  exact r2.trans w.1 ((readyKeptStage.of_stage hL3).trans hL3.1
    (.of_dispatch (SystemState.RunQueueDispatchStage.descheduleCurrent st3 c waiter hC3)))

theorem notificationWaitOnCore_readyKeptStage (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (c : CoreId) (st : SystemState)
    (hCur : st.scheduler.currentOnCore c = some waiter) (hNI : isIdleThreadId waiter = false) :
    readyKeptStage (· = waiter) st (notificationWaitOnCore notificationId waiter c st).1 := by
  unfold notificationWaitOnCore
  repeat' (first | split | dsimp only)
  all_goals first
    | exact .refl _
    | exact .of_stage ((storeObject_notificationOver_runQueueStage (by assumption)
         (by assumption)).trans (storeTcbIpcState_runQueueStage (by assumption) rfl))
    | exact notificationWait_block_readyKeptStage (by assumption) (by assumption)
         (by assumption) (by assumption) (by assumption) hCur hNI

/-- The fault reply's outcome blocks no thread: a restart frame, or the abandon's
deschedule and `.Inactive` mark. -/
theorem faultReplyApplyOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (faulted : SeLe4n.ThreadId) (outcome : Architecture.FaultReplyOutcome) :
    readyKeptStage S st (faultReplyApplyOnCore st faulted outcome) := by
  unfold faultReplyApplyOnCore
  split
  · exact .of_stage (SystemState.RunQueueStage.updateTcb
      (f := fun tcb => ((tcb.withRestartFrame _).setPendingFault none)) _ _ (fun _ _ => rfl))
  · unfold faultAbandonOnCore faultAbandonCore
    exact removeRunnableThenWrite_readyKeptStage _ _ _ _ fun _ h => h

/-- The reply leg's answer to its caller links the run queues for any start:
the ordinary staging and the restart are stages, the abandon a deschedule then
an off-queue write. -/
theorem replyRecvAnswerCaller_runQueueLinkStage (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (prevCaller : SeLe4n.ThreadId) (capInfo : Nat) :
    SystemState.RunQueueLinkStage st (replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none => exact (stageDeliveredMessage_runQueueStage _ _ _).1
  | some o =>
    show SystemState.RunQueueLinkStage st (faultReplyApplyOnCore st prevCaller o)
    unfold faultReplyApplyOnCore
    split
    · exact (SystemState.RunQueueStage.updateTcb
        (f := fun tcb => ((tcb.withRestartFrame _).setPendingFault none)) _ _ (fun _ _ => rfl)).1
    · unfold faultAbandonOnCore faultAbandonCore
      exact (SystemState.RunQueueStage.runDescheduleOnCore _ _ _).1.trans
        (SystemState.RunQueueLinkStage.updateTcb _ _ (fun _ _ => rfl))

/-- The reply leg's answer blocks no thread. -/
theorem replyRecvAnswerCaller_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState)
    (prevCaller : SeLe4n.ThreadId) (capInfo : Nat) :
    readyKeptStage S st (replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none => exact .of_stage (stageDeliveredMessage_runQueueStage _ _ _)
  | some o => exact faultReplyApplyOnCore_readyKeptStage st prevCaller o

theorem faultReplyOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hD : st.currentDequeuedUnique) :
    readyKeptStage S st (faultReplyOnCore replier faulted mi regs c st).1 := by
  have hE := endpointReplyCrossCoreDispatch_runQueueStage replier faulted IpcMessage.empty c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  unfold faultReplyOnCore
  split
  · exact .refl _
  split
  · exact .refl _
  dsimp only
  split
  · exact .refl _
  · rename_i stR sgi hR
    rw [hR] at hE
    exact (readyKeptStage.of_stage hE).trans hE.1 (faultReplyApplyOnCore_readyKeptStage _ _ _)

theorem replyTransferOnCoreChecked_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {ctx : LabelingContext} {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool} {c : CoreId}
    {st st' : SystemState} (hD : st.currentDequeuedUnique)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c st = .ok ((), st')) :
    readyKeptStage S st st' := by
  unfold replyTransferOnCoreChecked at h
  split at h
  · have hF := faultReplyOnCore_readyKeptStage (S := S) replier callerTid mi regs c st hD
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hE := endpointReplyCrossCoreDispatchChecked_runQueueStage ctx replier callerTid msg c st
      (blockedCurrentNowhere_of_currentDequeuedUnique hD)
    revert h hE
    generalize endpointReplyCrossCoreDispatchChecked ctx replier callerTid msg c st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h _; cases h
    | ok _ =>
      intro h hE
      simp only [] at h
      cases hX : replyTransferCaps st replier callerTid grant s with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, sX⟩ := p
        rw [hX] at h
        cases h
        exact .of_stage ((hE.trans (receiveTransferCaps_runQueueStage hX)).trans
          (stageDeliveredMessage_runQueueStage _ _ _))

/-- `ReplyRecv` blocks only its caller: the reply, the donation pop and the reply
leg's capability transfer are stages, and the receive half blocks the caller. -/
theorem endpointReplyRecvOnCore_readyKeptStage {answer : Option Architecture.FaultReplyOutcome}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId}
    {st st' : SystemState} {s : CapTransferSummary}
    (hInv : st.objects.invExt) (hRf : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hQ : queueHeadBlockedConsistent st)
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false)
    (h : endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant c st =
      .ok (s, st')) :
    readyKeptStage (· = tid) st st' := by
  have hE := endpointReplyOnCore_runQueueStage tid prevCaller msg c st
    (blockedCurrentNowhere_of_currentDequeuedUnique hD)
  have hC1 : (endpointReplyOnCore tid prevCaller msg c st).1.scheduler.currentOnCore c = some tid :=
    (endpointReplyOnCore_currentOnCore tid prevCaller msg c st c).trans hCur
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg c st hInv
  have hEB := endpointReplyOnCore_endpoint_backward tid prevCaller msg c st hInv
  have hCB := endpointReplyOnCore_currentOnCore tid prevCaller msg c st
  have hQ1 : ∀ sgi?, (endpointReplyOnCore tid prevCaller msg c st).2 = .ok sgi? →
      queueHeadBlockedConsistent (endpointReplyOnCore tid prevCaller msg c st).1 := fun _ hOk =>
    endpointReplyOnCore_preserves_queueHeadBlockedConsistent tid prevCaller msg c st hInv hQ hOk
  unfold endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  generalize endpointReplyOnCore tid prevCaller msg c st = p at hE h hC1 hInv1 hEB hCB hQ1
  obtain ⟨st1, r⟩ := p
  dsimp only at hE hC1 hInv1 hEB hCB hQ1
  cases r with
  | error => cases h
  | ok sgi =>
  dsimp only at h
  have hH1 := (endpointHeadsWakeable_of hD hQ).of_frame hEB hCB (hQ1 _ rfl)
  split at h
  · cases h
  rename_i ret st1q hPop
  -- The reply leg's capability transfer, between the pop and the receive leg.
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [hX] at h
  dsimp only at h
  have hXU := hX
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hXU
  have hPopS := (replyRecvPopDonation_runQueueStage hPop).trans (receiveTransferCaps_runQueueStage hXU)
  obtain ⟨hQE, hQC, hQT⟩ := replyRecvPopDonation_frame hInv1 hPop
  obtain ⟨hXE, hXC, hXT⟩ := receiveTransferCaps_ipcFrame
    (replyRecvPopDonation_preserves_objects_invExt _ _ _ _ _ hInv1 hPop) hXU
  have hPE : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint), st1p.objects[oid]? = some (.endpoint ep) →
      st1.objects[oid]? = some (.endpoint ep) := fun e ep h => hQE e ep (hXE e ep h)
  have hPC : ∀ c, st1p.scheduler.currentOnCore c = st1.scheduler.currentOnCore c :=
    fun c => (hXC c).trans (hQC c)
  have hPT : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB), st1p.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st1.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState :=
    fun y t h => by
      obtain ⟨u, hu, hU⟩ := hXT y t h
      obtain ⟨v, hv, hV⟩ := hQT y u hu
      exact ⟨v, hv, hV.trans hU⟩
  have hH2 := hH1.of_frame hPE hPC (queueHeadBlockedConsistent_of_endpoint_tcb_backward _ _ hPE hPT
      (hQ1 _ rfl))
  -- The replier is current, so active; the reply and the pop suspend no thread.
  have hA1 : st1.activeAt tid :=
    activeKeptStage.of_stage hE hInv hRf tid (hD.runnable hCur).activeAt
  have hAp : st1p.activeAt tid :=
    let ⟨hI1, hR1⟩ := hE.1.links hInv hRf
    activeKeptStage.of_stage hPopS hI1 hR1 tid hA1
  have hR := endpointReceiveDualWithCapsOnCore_runQueueEntryStage epId tid (some rid) c
    st1p hH2 ((hPC c).trans hC1) hNI hAp
  have rR := endpointReceiveDualWithCapsOnCore_readyKeptStage epId tid (some rid) c
    st1p hH2 ((hPC c).trans hC1) hNI hAp
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) c st1p = q at hR rR h
  obtain ⟨st2, r2⟩ := q
  dsimp only at hR rR
  rcases r2 with _ | ⟨nt, sm, _⟩ <;> dsimp only at h
  · cases h
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  have A := hE.trans hPopS
  -- The post-receive donor is blocked on its reply and every thread stays
  -- coherent, so it is not suspended.
  have hAll := A.entry.trans hR
  obtain ⟨hI2, hR2⟩ := hAll.1.links hInv hRf
  have hD2 := hAll.2 hInv hRf hR2 hD
  have hPH := (replyRecvPostReceiveDonation_runQueueStage hI2 hR2 (hD2.coherent nt) hPost).trans
    (applyReceiveLegPipHandoff_runQueueStage st3 tid nt
      ((recordedReplyServer? st prevCaller).getD tid) c)
  exact (readyKeptStage.of_stage A).trans A.1 (rR.trans hR.1 ((readyKeptStage.of_stage hPH).trans
    hPH.1 ((replyRecvAnswerCaller_readyKeptStage answer _ prevCaller _).trans
      (replyRecvAnswerCaller_runQueueLinkStage answer _ prevCaller _)
      (.of_stage (stageWokenSendCompletion_runQueueStage _ _)))))

/-! ### The scheduling arms -/

theorem handleRescheduleSgiOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {c : CoreId} (h : handleRescheduleSgiOnCore st c = .ok st') : readyKeptStage S st st' :=
  fun hI hR => .of_stateMono (handleRescheduleSgiOnCore_stateMono h hI hR)

theorem suspendRescheduleOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {runningCore executingCore : CoreId} {wasCurrent localDeboosted : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : suspendRescheduleOnCore st runningCore executingCore wasCurrent localDeboosted =
      .ok (st', sgi?)) : readyKeptStage S st st' := by
  unfold suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hH; rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1];
        exact handleRescheduleSgiOnCore_readyKeptStage hH)
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .refl _)

theorem priorityRescheduleOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {running? : Option CoreId} {ec : CoreId} {sp : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec sp =
      .ok (st', sgi?)) : readyKeptStage S st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h
    with hEq | hH
  · exact .of_eq hEq
  · exact handleRescheduleSgiOnCore_readyKeptStage hH

theorem applyPriorityChangeOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB} {p : SeLe4n.Priority} {ec : CoreId}
    {b : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p ec b =
      .ok (st', sgi?)) : readyKeptStage S st st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  have A := (((SchedContext.PriorityManagement.updatePrioritySource_runQueueStage st tid tcb p).trans
    (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_runQueueStage _ tid p
      (determineTargetCore st tid))).trans
    ((markKeyChangeFor_runQueueStage _ tid (effectiveSchedParams st tcb)).trans
      (PriorityInheritance.repropagateFromWaiter_runQueueStage _ tid ec
        st.objects.size)))
  exact (readyKeptStage.of_stage A).trans A.1 (priorityRescheduleOnCore_readyKeptStage h)

theorem setPriorityOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : readyKeptStage S st st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore_readyKeptStage h
      · cases h
  · cases h

theorem setMCPriorityOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p ec =
      .ok (st', sgi?)) : readyKeptStage S st st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i targetTcb hTarget _
        dsimp only at h
        have hS := SystemState.RunQueueStage.rewriteObject_tcb
          (t' := { targetTcb with maxControlledPriority := p })
          hTarget (fun _ => by rfl) (SystemState.rewriteAdmissible_tcb hTarget _)
        split at h
        · exact (readyKeptStage.of_stage hS).trans hS.1 (applyPriorityChangeOnCore_readyKeptStage h)
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .of_stage hS
      · cases h
  · cases h

/-- The affinity change keeps every thread's IPC state: it rewrites the moved
thread's affinity and run links, and no other thread's TCB but its links. -/
theorem setThreadCpuAffinityWithMigration_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {affinity : Option CoreId}
    {ec : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (st', sgi?)) :
    readyKeptStage S st st' := fun hInv _ u _ hr x' hx' => by
  obtain ⟨tcb, hT, -, -, -, hNe, hTv, -, -, -⟩ := setThreadCpuAffinityWithMigration_placement hInv h
  have hTv' : (st'.getTcb? tid).map TCB.withoutRunLinks =
      (some { tcb with cpuAffinity := affinity }).map TCB.withoutRunLinks := hTv
  have hPair : (st'.getTcb? u).map TCB.ipcState = (st.getTcb? u).map TCB.ipcState := by
    by_cases hu : u = tid
    · rw [hu, TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.ipcState hTv', hT]; rfl
    · exact TCB.map_proj_eq_of_map_withoutRunLinks_eq _ (hNe u hu)
  rw [hx'] at hPair
  cases hx : st.getTcb? u with
  | none => rw [hx] at hPair; cases hPair
  | some x =>
    rw [hx] at hPair
    simp only [Option.map_some, Option.some.injEq] at hPair
    rw [hPair]; exact hr x hx

theorem schedControlConfigure_readyKeptStage {S : SeLe4n.ThreadId → Prop} {core : CoreId}
    {vScId : SeLe4n.ValidObjId} {budget period priority deadline domain : Nat}
    {st st' : SystemState}
    (h : SchedContextOps.schedControlConfigure core vScId budget period priority deadline domain st =
      .ok ((), st')) : readyKeptStage S st st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨_, _, _, _, -, -, -, hM, h⟩
  · exact .of_stage (schedContextConfigure_runQueueStage h)
  · exact (setThreadCpuAffinityWithMigration_readyKeptStage hM).trans
      (setThreadCpuAffinityWithMigration_runQueueEntryStage hM).1
      (.of_stage (schedContextConfigure_runQueueStage h))

theorem schedContextUnbindOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {vScId : SeLe4n.ValidObjId} {ec : CoreId} {st st' : SystemState}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hD : st.currentDequeuedUnique)
    (h : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi?)) :
    readyKeptStage S st st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  split at h
  · cases h
  · rename_i stU hU
    have A := SchedContextOps.schedContextUnbind_runQueueStage_of_dequeued vScId st stU hD hU
    exact (readyKeptStage.of_stage A).trans A.1 (priorityRescheduleOnCore_readyKeptStage h)

theorem schedContextConsumedOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {s : SeLe4n.SchedContextId} {c : CoreId} {st st' : SystemState}
    (h : schedContextConsumedOnCore s c st = .ok st') : readyKeptStage S st st' := by
  obtain ⟨caller, -, rfl⟩ := schedContextConsumedOnCore_ok h
  exact .of_stage (SystemState.setConsumed_runQueueStage st s caller)

/-- WS-ZA ZA6.29: two readiness frames compose over a step that keeps the link
invariants. -/
theorem readyKeptStage.trans_links {S : SeLe4n.ThreadId → Prop} {a b c : SystemState}
    (L : a.objects.invExt → a.runQueueRefined → b.objects.invExt ∧ b.runQueueRefined)
    (h1 : readyKeptStage S a b) (h2 : readyKeptStage S b c) : readyKeptStage S a c :=
  fun hI hR => let ⟨hI', hR'⟩ := L hI hR; (h1 hI hR).trans (h2 hI' hR')

/-- WS-ZA ZA6.29: **the yieldTo blocks no thread**: the completion, the resume's
re-placement, the consumed time, the requeue and the link's writes keep every
thread's state fields, and the link's scheduling point keeps them too. -/
theorem schedContextYieldToOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {s : SeLe4n.SchedContextId} {c : CoreId} {st st' : SystemState}
    (h : SchedContextOps.schedContextYieldToOnCore s c st = .ok st') : readyKeptStage S st st' := by
  obtain ⟨caller, -, t, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
    SchedContextOps.schedContextYieldToOnCore_ok h
  have h1 := SystemState.completeYieldFrom_runQueueStage st s
  have h2 := releasePlace_runQueueFrameStage (completeYieldFrom st s)
    (determineTargetCore (completeYieldFrom st s) t) s
  have hK : readyKeptStage S st ((completeYieldFrom st s).releasePlace
      (determineTargetCore (completeYieldFrom st s) t) s) :=
    (readyKeptStage.of_stage h1).trans h1.1 (fun hI hR => .of_stateMono (h2.2.2 hI hR))
  have hL : st.objects.invExt → st.runQueueRefined →
      ((completeYieldFrom st s).releasePlace
        (determineTargetCore (completeYieldFrom st s) t) s).objects.invExt ∧
      ((completeYieldFrom st s).releasePlace
        (determineTargetCore (completeYieldFrom st s) t) s).runQueueRefined := fun hI hR =>
    let ⟨a, b⟩ := h1.1.links hI hR; h2.1.links a b
  refine readyKeptStage.trans_links hL hK ?_
  unfold SchedContextOps.yieldToBound
  dsimp only
  generalize (completeYieldFrom st s).releasePlace (determineTargetCore (completeYieldFrom st s) t) s
    = st2
  have hSet : ∀ X : SystemState, readyKeptStage S X (setConsumed X s caller) := fun X =>
    .of_stage (SystemState.setConsumed_runQueueStage X s caller)
  have hLink : ∀ pC pT,
      readyKeptStage S st2 (SchedContextOps.yieldToLink st2 c s caller t pC pT) := fun pC pT =>
    readyKeptStage.trans_links (fun hI hR => (yieldToLinkPrefix_links st2 c s caller t pC pT hI hR).1)
      (fun hI hR => .of_stateMono (yieldToLinkPrefix_links st2 c s caller t pC pT hI hR).2)
      (handleRescheduleSgiOnCore_readyKeptStage (SchedContextOps.yieldToLink_sgi st2 c s caller t pC pT))
  have hReq : ∀ home pT,
      readyKeptStage S st2 (setConsumed (SchedContextOps.yieldToRequeue st2 home t pT) s caller) :=
    fun home pT => readyKeptStage.trans_links (yieldToRequeue_links st2 home t pT)
      (fun _ _ => .of_stateMono (yieldToRequeue_stateMono st2 home t pT)) (hSet _)
  split
  · exact hSet _
  · split
    · exact hSet _
    · split
      · exact hSet _
      · split
        · split
          · exact hReq _ _
          · exact hLink _ _
        · exact hSet _

/-- The yield blocks no thread: its charge is a preemption window, closed by the
reschedule. -/
theorem yieldOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {c : CoreId} (h : yieldOnCore st c = .ok st') (hH : st.currentContextPlaceableOnCore c) :
    readyKeptStage S st st' := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · rename_i tid hCur
    split at h
    · cases h
    · rename_i hC
      exact fun hI hR => .of_stateMono (windowDispatch_stateMono
        (yieldChargeOnCore_runQueueWindowStage hC hCur hH)
        (scheduleEffectiveOnCore_runQueueDispatchStage h) hI hR)

theorem resumeThreadOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : resumeThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    readyKeptStage S st st' := by
  unfold resumeThreadOnCore at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have hFB := (((resumeReadyMidState_runQueueFrameStage st vtid.val).trans
        ((markKeyChangeFrom_runQueueStage st (resumeReadyMidState st vtid.val)
          vtid.val).toFrame _)).mono (P' := fun _ => True)
          fun _ _ => trivial).trans
        (resumeContext_runQueueFrameStage _ vtid.val (determineTargetCore st vtid.val))
      have r : readyKeptStage S st (enqueueRunnableOnCore
          (resumeContext (markKeyChangeFrom st (resumeReadyMidState st vtid.val) vtid.val)
            vtid.val (determineTargetCore st vtid.val))
          (determineTargetCore st vtid.val) vtid.val) :=
        (readyKeptStage.of_frame hFB).transFrame hFB
          fun hI _ => .of_stateMono (enqueueRunnableOnCore_stateMono _ _ _ hI)
      split at h
      · split at h
        · split at h
          · rename_i hH
            rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]
            exact readyKeptStage.trans_links (fun hI hR => (hFB.1.links hI hR).elim
              (enqueueRunnableOnCore_runQueueLinkStage _ _ _).links) r
              (handleRescheduleSgiOnCore_readyKeptStage hH)
          · cases h
        · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact r
      · rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .of_frame hFB
  · cases h

/-- **The suspend blocks no thread**: seL4-MCS's `cancelIPC` makes its victim
ready, the chain revert is a stage, the removal's two off-queue writes keep the
IPC state, and `tcbReleaseRemove` writes release links alone. -/
theorem suspendThreadOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    readyKeptStage S st st' := by
  simp only [suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    have hS1 := cancelIpcKeepingContexts_runQueueStage st vtid.val tcb
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse hA =>
      have hS12 : SystemState.RunQueueStage (cancelIpcKeepingContexts st vtid.val tcb)
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
           | none => cancelIpcKeepingContexts st vtid.val tcb) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact SystemState.RunQueueStage.refl _
        | some serverId => exact PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _
      have hS3 := hS1.trans hS12
      have hD3 := descheduleAt_runQueueStage
        (match PriorityInheritance.blockingServer st vtid.val with
         | some serverId => (PriorityInheritance.propagatePipChainCrossCore
             (cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
         | none => cancelIpcKeepingContexts st vtid.val tcb) vtid.val (placedCoreOf? st vtid.val)
      have L := (hS3.1.trans hD3.1).trans
        ((SystemState.RunQueueLinkStage.updateTcb _ vtid.val
          (f := fun tcb => { tcb with
            pendingMessage := none
            timeoutBudget := none
            queuePrevCode := 0
            queueNextCode := 0
            queuePPrevCode := 0 })
          (fun _ _ => rfl)).trans
          (SystemState.RunQueueLinkStage.updateTcb _ vtid.val
            (f := fun t => { t with threadState := .Inactive }) (fun _ _ => rfl)))
      have r := (readyKeptStage.of_stage (S := S) hS3).trans hS3.1
        ((readyKeptStage.of_stage hD3).trans hD3.1 fun hI _ =>
          (readyKeptExcept_updateTcb _ vtid.val (fun tcb => { tcb with
                pendingMessage := none
                timeoutBudget := none
                queuePrevCode := 0
                queueNextCode := 0
                queuePPrevCode := 0 }) hI fun _ h => h).trans
            (readyKeptExcept_updateTcb _ vtid.val (fun t => { t with threadState := .Inactive })
              (SystemState.updateTcb_preserves_objects_invExt _ _ _ hI) fun _ h => h))
      have hRR := releaseRemoveThread_runQueueFrameStage
        (((descheduleAt (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
           | none => cancelIpcKeepingContexts st vtid.val tcb) vtid.val
            (placedCoreOf? st vtid.val)).updateTcb vtid.val fun tcb => { tcb with
              pendingMessage := none
              timeoutBudget := none
              queuePrevCode := 0
              queueNextCode := 0
              queuePPrevCode := 0 }).updateTcb vtid.val
          fun t => { t with threadState := .Inactive }) vtid.val
      have hY := SystemState.cancelYieldTo_runQueueStage (releaseRemoveThread
        (((descheduleAt (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcKeepingContexts st vtid.val tcb) serverId executingCore).1
           | none => cancelIpcKeepingContexts st vtid.val tcb) vtid.val
            (placedCoreOf? st vtid.val)).updateTcb vtid.val fun tcb => { tcb with
              pendingMessage := none
              timeoutBudget := none
              queuePrevCode := 0
              queueNextCode := 0
              queuePPrevCode := 0 }).updateTcb vtid.val
          fun t => { t with threadState := .Inactive }) vtid.val) vtid.val
      unfold clearPendingStateValid clearPendingState at hStep
      exact r.trans L ((readyKeptStage.of_frame hRR).transFrame hRR
        ((readyKeptStage.of_stage hY).trans hY.1 (suspendRescheduleOnCore_readyKeptStage hStep)))

/-! ### The finalising deletes -/

/-- A kernel entry from `st` that keeps readiness off `S`, extended by a stage. -/
theorem readyEntry_stage {S : SeLe4n.ThreadId → Prop} {st s s' : SystemState}
    (h : SystemState.RunQueueEntryStage st s ∧ readyKeptStage S st s)
    (X : SystemState.RunQueueStage s s') :
    SystemState.RunQueueEntryStage st s' ∧ readyKeptStage S st s' :=
  ⟨h.1.trans X.entry, h.2.trans h.1.1 (.of_stage X)⟩

/-- **A finalisation blocks no thread**: every cancel makes its thread ready or
keeps it, and every other step is a stage or the suspend's deschedule and
off-queue `.Inactive` mark, which keeps the IPC state. -/
theorem finaliseFinalObject_readyEntry {S : SeLe4n.ThreadId → Prop} (target : Nat)
    {st s : SystemState} (h : SystemState.RunQueueEntryStage st s ∧ readyKeptStage S st s) :
    SystemState.RunQueueEntryStage st (finaliseFinalObject target s) ∧
      readyKeptStage S st (finaliseFinalObject target s) :=
  finaliseFinalObject_closed (fun s => SystemState.RunQueueEntryStage st s ∧ readyKeptStage S st s)
    (fun e q s ep t tcb h hE hH hT hC =>
      readyEntry_stage h (storeEndpointWaiterCancelled_runQueueStage s e q ep t tcb hE hH hT hC))
    (fun n s _ t tcb h _ _ hT hC =>
      readyEntry_stage h (notificationWaiterCancel_runQueueStage s n t tcb hT hC))
    (fun n s _ t h _ _ hCode hIn => by
      have hSpec := unbindNotification_of_inPlace s t hIn
      rw [hCode, Nat.add_sub_cancel] at hSpec
      exact readyEntry_stage h (unbindNotification_runQueueStage hSpec))
    (fun s t _ h _ _ _ _ => readyEntry_stage h (descheduleAt_runQueueStage s t _))
    (fun _ _ _ _ _ _ h _ _ _ _ hOk => readyEntry_stage h (cancelBoundDonationOnCore_runQueueStage hOk))
    (fun s _ t tcb _ h _ hB _ _ => readyEntry_stage h (cancelIpcBlocking_runQueueStage s t tcb
      (by unfold Lifecycle.Suspend.cancelledCallerDonation?; rw [hB])))
    (fun s e q t ep tcb h hT hE hC =>
      readyEntry_stage h (storeEndpointBlockedCancelled_runQueueStage s e q t ep tcb hT hE hC))
    (fun s t tcb h hT hS hO _ hId =>
      ⟨h.1.trans (finaliseSuspend_runQueueEntryStage s t tcb hT hS hO hId),
        h.2.trans h.1.1 (descheduleAtThenWrite_readyKeptStage s t _ finalisedSuspendMark
          fun _ h => h)⟩)
    (fun s t h => readyEntry_stage h (SystemState.RunQueueStage.of_frameLive
      (st' := finaliseThreadReleaseCores s t)
      (finaliseThreadReleaseCores_objects s t)
      (by rw [finaliseThreadReleaseCores_scheduler]) (by rw [finaliseThreadReleaseCores_scheduler])
      (fun c u hU => by
        rw [finaliseThreadReleaseCores_machine] at hU
        unfold MachineState.releaseThread at hU
        rw [MachineState.releaseThreadOnCores_residentOnCore] at hU
        split at hU
        · cases hU
        · exact Or.inl hU)
      (by rw [finaliseThreadReleaseCores_scheduler])
      (by rw [finaliseThreadReleaseCores_scheduler])))
    (fun _ s1 x _ _ _ h _ _ hR _ hS _ _ _ _ =>
      readyEntry_stage h ((storeObject_replyOver_runQueueStage hR hS).trans
        (updateSchedContext_runQueueStage s1 ⟨x.val⟩ _)))
    (fun s _ _ c t h _ _ _ _ => readyEntry_stage h ((cancelIpcBlockingReclaimed_runQueueStage s c t).trans
      (finaliseReplyRevert_runQueueStage _ _)))
    (fun s _ _ tid _ h _ _ e => e ▸ readyEntry_stage h
      (SystemState.RunQueueStage.updateTcb s tid (f := TCB.stashCleared) (fun _ _ => rfl)))
    ⟨fun s t h => readyEntry_stage h (SystemState.cancelYieldTo_runQueueStage s t),
     fun s c h => readyEntry_stage h (SystemState.completeYieldFrom_runQueueStage s c)⟩
    (fun _ _ _ _ h hT _ hS => readyEntry_stage h (orphanReplyWaiter_runQueueStage hT hS))
    (fun s _ r c _ h _ _ _ _ => readyEntry_stage h (finaliseReplyUnheldPop_runQueueStage s r c))
    (fun s _ _ _ t h _ _ _ _ => readyEntry_stage h (cutCancelledCallerHead_runQueueStage s t))
    target s h

theorem cspaceDeleteSlotFinalising_readyEntry {S : SeLe4n.ThreadId → Prop} {ec : CoreId}
    {addr : CSpaceAddr} {st s s' : SystemState}
    (hQ : SystemState.RunQueueEntryStage st s ∧ readyKeptStage S st s)
    (h : cspaceDeleteSlotFinalising ec addr s = .ok ((), s')) :
    SystemState.RunQueueEntryStage st s' ∧ readyKeptStage S st s' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr s s' h
  rcases retireFinalisedObject_cases ec (slotRetireTarget s addr.cnode addr.slot)
    (slotRetireRecorder s addr.cnode addr.slot) st2 with ⟨-, hE⟩ | ⟨-, hE⟩
  · rw [hE]
    exact readyEntry_stage (readyEntry_stage hQ ((cspaceDeleteSlot_runQueueStage hD).trans
      (finaliseDestroyedCapabilities_runQueueStage hF))) (retireIrqNode_runQueueStage st2 _)
  · rw [hE]
    exact readyEntry_stage (finaliseFinalObject_readyEntry _ (readyEntry_stage hQ
      (((cspaceDeleteSlot_runQueueStage hD).trans (finaliseDestroyedCapabilities_runQueueStage hF)).trans
        (releaseFinalRegistration_runQueueStage _ st2))))
      (retireFinalObject_runQueueStage ec _ _ _)

/-- The start of a kernel entry: nothing yet. -/
theorem readyEntry_refl {S : SeLe4n.ThreadId → Prop} (st : SystemState) :
    SystemState.RunQueueEntryStage st st ∧ readyKeptStage S st st :=
  ⟨⟨SystemState.RunQueueLinkStage.refl st, fun _ _ _ d => d⟩, .refl _⟩

theorem cspaceRevokeCdtFinalising_readyKeptStage {S : SeLe4n.ThreadId → Prop} {ec : CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) : readyKeptStage S st st' :=
  (cspaceRevokeCdtFinalising_closed (fun s => SystemState.RunQueueEntryStage st s ∧
      readyKeptStage S st s)
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_readyEntry hQ hD)
    (fun _ _ hQ => finaliseFinalObject_readyEntry _ hQ) (readyEntry_refl st) h).2

theorem copyThreadSpacesZombie_readyKeptStage {S : SeLe4n.ThreadId → Prop} {ec : CoreId}
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (h : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') : readyKeptStage S st st' :=
  (copyThreadSpacesZombie_closed (fun s => SystemState.RunQueueEntryStage st s ∧
      readyKeptStage S st s)
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_readyEntry hQ hD)
    (fun _ _ hQ => finaliseFinalObject_readyEntry _ hQ)
    (fun _ _ hQ hS => readyEntry_stage hQ (copyThreadSpaces_runQueueStage hS))
    (readyEntry_refl st) h).2

/-- The zombie delete as a stage pair, for a step that continues after it. -/
theorem cspaceDeleteSlotZombie_readyEntry {S : SeLe4n.ThreadId → Prop} {ec : CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' ∧ readyKeptStage S st st' :=
  cspaceDeleteSlotZombie_closed (fun s => SystemState.RunQueueEntryStage st s ∧
      readyKeptStage S st s)
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_readyEntry hQ hD)
    (fun _ _ hQ => finaliseFinalObject_readyEntry _ hQ) (readyEntry_refl st) h

theorem cspaceDeleteSlotZombie_readyKeptStage {S : SeLe4n.ThreadId → Prop} {ec : CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) : readyKeptStage S st st' :=
  (cspaceDeleteSlotZombie_closed (fun s => SystemState.RunQueueEntryStage st s ∧
      readyKeptStage S st s)
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_readyEntry hQ hD)
    (fun _ _ hQ => finaliseFinalObject_readyEntry _ hQ) (readyEntry_refl st) h).2

/-! ### The dispatch -/

/-- **The capability-only dispatch blocks no thread** on any arm: a finalising
delete's cancels make their threads ready, the suspend's mark keeps the IPC
state, and every other arm is a stage or a reschedule. -/
theorem dispatchCapabilityOnly_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hD : st.currentDequeuedUnique) (hStep : k st = .ok ((), st')) :
    readyKeptStage S st st' := by
  unfold dispatchCapabilityOnly at hArm
  cases hSy : decoded.syscallId <;> simp only [hSy] at hArm <;> try cases hArm
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact readyKeptStage.of_stage (irqHandlerAck_runQueueStage hStep)
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl =>
      obtain ⟨_, _, _, -, -, -, hG⟩ := irqControlGetFromCap_ok _ _ _ _ _ hStep
      exact readyKeptStage.of_stage (irqControlGet_runQueueStage hG)
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, -, hN⟩ := irqHandlerSetNotificationFromCap_ok _ _ _ _ _ _ hStep
      obtain ⟨-, st1, -, -, -, hZ, hC | rfl⟩ := irqHandlerSetNotification_ok_cases hN
      · exact (readyEntry_stage (cspaceDeleteSlotZombie_readyEntry hZ)
          (cspaceCopy_runQueueStage hC)).2
      · exact (readyEntry_stage (cspaceDeleteSlotZombie_readyEntry hZ)
          (cspaceCopyPerform_runQueueStage _ _ _ _)).2
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      exact cspaceDeleteSlotZombie_readyKeptStage (irqHandlerClear_ok hStep).2
    all_goals try cases hStep
  case cspaceDelete =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact cspaceDeleteSlotZombie_readyKeptStage hStep
    all_goals try cases hStep
  case cspaceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact cspaceRevokeCdtFinalising_readyKeptStage hStep
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeMintReplyCapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          refine readyKeptStage.of_stage ?_
          exact mintReplyCapWithCdt_runQueueStage hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      refine readyKeptStage.of_stage ?_
      exact untypedRetypeFromCap_runQueueStage hStep
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      refine readyKeptStage.of_stage ?_
      obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ _ _ hStep
      exact untypedResetSlot_runQueueStage hS
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceMapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine readyKeptStage.of_stage ?_
            exact vspaceMapOrRemapFromFrameCap_runQueueStage hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnmapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine readyKeptStage.of_stage ?_
            exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_runQueueStage hStep
    all_goals try cases hStep
  case vspaceUnifyInstruction =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine readyKeptStage.of_stage ?_
            exact vspaceUnifyInstructionPage_runQueueStage hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      refine readyKeptStage.of_stage ?_
      exact revokeService_runQueueStage hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object epId =>
      try dsimp only [] at hStep
      cases hLkS : lookupServiceByRecordedRegistration epId st with
      | error e => simp only [hLkS] at hStep; cases hStep
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hStep
          have hStEq : st1 = st := lookupServiceByRecordedRegistration_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          refine readyKeptStage.of_stage ?_
          exact writeReturnFrameToTcb_runQueueStage _ _ _
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextConfigureArgsChecked decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : resolveSchedControlConfigureTarget tid core args.scCPtr st with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              split at hStep
              · exact schedControlConfigure_readyKeptStage hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st with
      | error e => simp only [hRes] at hStep; cases hStep
      | ok vThreadId =>
          simp only [hRes] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              refine readyKeptStage.of_stage ?_
              exact schedContextBind_runQueueStage hStep
    all_goals try cases hStep
  case schedContextUnbind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextUnbindArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              cases hUn : SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact schedContextUnbindOnCore_readyKeptStage hD hUn
    all_goals try cases hStep
  case schedContextConsumed =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
              executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact schedContextConsumedOnCore_readyKeptStage hC
    all_goals try cases hStep
  case schedContextYieldTo =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : SchedContextOps.schedContextYieldToOnCore
              (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact schedContextYieldToOnCore_readyKeptStage hC
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : decodeTcbBindNotificationArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              cases hRoot : st.getCNode? callerTcb.cspaceRoot with
              | none => simp only [hRoot] at hStep; cases hStep
              | some rootCn =>
                  simp only [hRoot] at hStep
                  try dsimp only [] at hStep
                  cases hCap2 : syscallLookupCap { callerId := tid, cspaceRoot := callerTcb.cspaceRoot, capAddr := args.notificationCPtr, capDepth := rootCn.depth, requiredRight := .write } st with
                  | error e => simp only [hCap2] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨ntfnCap, stL⟩ := pair
                      simp only [hCap2] at hStep
                      cases hNT : ntfnCap.target with
                      | object notifId =>
                          simp only [hNT] at hStep
                          refine readyKeptStage.of_stage ?_
                          exact bindNotification_runQueueStage hStep
                      | _ => simp only [hNT] at hStep; cases hStep
    all_goals try cases hStep
  case tcbUnbindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hUn : unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
      | error e => simp only [hUn] at hStep; cases hStep
      | ok pair =>
          obtain ⟨u, stU⟩ := pair; cases u
          simp only [hUn] at hStep
          cases hStep
          refine readyKeptStage.of_stage ?_
          exact unbindNotification_runQueueStage hUn
    all_goals try cases hStep
  case tcbSuspend =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSuspendArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSus : Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
              | error e => simp only [hSus] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hSus] at hStep
                  cases hStep
                  exact suspendThreadOnCore_readyKeptStage hSus
    all_goals try cases hStep
  case tcbResume =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeResumeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vtid =>
          simp only [hVal] at hStep
          cases hRes : Lifecycle.Suspend.resumeThreadOnCore
              (retirePendingFaultForResume st vtid.val) vtid
              executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              exact (readyKeptStage.of_stage (retirePendingFaultForResume_runQueueStage st vtid.val)).trans
                  (retirePendingFaultForResume_runQueueStage st vtid.val).1
                  (resumeThreadOnCore_readyKeptStage hRes)
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newPriority)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setPriorityOnCore_readyKeptStage hSet
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setMCPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newMCP)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setMCPriorityOnCore_readyKeptStage hSet
    all_goals try cases hStep
  case tcbSetIPCBuffer =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetIPCBufferArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp st vtid
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  refine readyKeptStage.of_stage ?_
                  exact setIPCBufferOp_runQueueStage hSet
    all_goals try cases hStep
  case tcbSetAffinity =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetAffinityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hAff : decodeAffinity args.affinityRaw with
              | error e => simp only [hAff] at hStep; cases hStep
              | ok affinity =>
                  simp only [hAff] at hStep
                  cases hSet : setThreadCpuAffinityOnCore st vtid affinity
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setThreadCpuAffinityWithMigration_readyKeptStage hSet
    all_goals try cases hStep
  case tcbSetFaultHandler =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetFaultHandlerArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : setThreadFaultHandlerOp st vtid args.handlerCPtr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  refine readyKeptStage.of_stage ?_
                  exact setThreadFaultHandlerOp_runQueueStage hSet
    all_goals try cases hStep
  case tcbSetSpace =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hR : resolveSetSpace tid args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact copyThreadSpacesZombie_readyKeptStage hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hR : resolveCallerCapObject tid args.vspaceRoot .write st with
          | error e => simp only [hR] at hStep; cases hStep
          | ok p =>
              obtain ⟨_, rootId⟩ := p
              simp only [hR] at hStep
              refine readyKeptStage.of_stage ?_
              exact pageTableMap_runQueueStage hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      refine readyKeptStage.of_stage ?_
      exact pageTableUnmap_runQueueStage hStep
    all_goals try cases hStep


theorem clearStashStage_readyKeptStage {S : SeLe4n.ThreadId → Prop} {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : SystemState.RunQueueEntryStage st s) (r : readyKeptStage S st s)
    (hStage : ∀ x, SystemState.RunQueueStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    readyKeptStage S st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact r.trans hS.1 (.of_stage ((clearWokenReceiverStash_runQueueStage woken? hClr).trans
      (hStage _)))

theorem endpointSendCrossCoreDispatchChecked_readyKeptStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (c : CoreId)
    (st : SystemState) (P : SyscallArmPremises st c sender) :
    readyKeptStage (· = sender) st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload c st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact .refl _
    | exact endpointSendDualWithCapsOnCore_readyKeptStage _ _ _ _ _ P.endpointHeads
        P.current P.notIdle

theorem endpointCallCrossCoreDispatchChecked_readyKeptStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (c : CoreId)
    (st : SystemState) (P : SyscallArmPremises st c caller) :
    readyKeptStage (· = caller) st
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload c st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_readyKeptStage _ _ _ _ _ P.endpointHeads
      P.current P.notIdle
  · exact .refl _

theorem notificationWaitCrossCoreDispatchChecked_readyKeptStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (c : CoreId)
    (st : SystemState) (P : SyscallArmPremises st c waiter) :
    readyKeptStage (· = waiter) st
      (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter c st).1 := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · exact notificationWaitOnCore_readyKeptStage _ _ _ _ P.current P.notIdle
  · exact .refl _


/-- **Every arm `dispatchWithCapChecked` routes blocks only the caller**: the
send, receive, call, notification-wait and reply-receive arms block it, and no
other arm blocks a thread. -/
theorem dispatchWithCapChecked_readyKeptStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    readyKeptStage (· = tid) st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_readyKeptStage decoded cap tid executingCore k st st' hC
      P.dequeued (dispatchCapabilityOnlyChecked_ok hC h)
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    rw [auditReadFromCore_frame _ _ _ _ _ _ _ hA]
    refine readyKeptStage.of_stage ?_
    exact writeReturnFrameToTcb_runQueueStage _ _ _
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      refine readyKeptStage.of_stage ?_
      refine SystemState.RunQueueStage.trans ?_ (writeReturnFrameToTcb_runQueueStage _ _ _)
      exact SystemState.RunQueueStage.of_frame rfl rfl rfl
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_readyKeptStage
      ((runQueueStage_of_pair_eq
        (endpointSendCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ _ P) hSend))
      ((runQueueStage_of_pair_eq
        (endpointSendCrossCoreDispatchChecked_readyKeptStage _ _ _ _ _ _ P) hSend))
      (fun x => stageWokenDelivery_runQueueStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    have E := runQueueStage_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ P.endpointHeads
        P.current P.notIdle P.currentActive) hRecv
    obtain ⟨_, hR2⟩ := E.1.links P.objInv P.refined
    exact (runQueueStage_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_readyKeptStage _ _ _ _ _ P.endpointHeads
        P.current P.notIdle P.currentActive) hRecv).trans E.1
      (.of_stage (((applyReceiveRendezvousHandoff_runQueueStage
          ((E.2 P.objInv P.refined hR2 P.dequeued).coherent _) hHand).trans
        (stageWokenSendCompletion_runQueueStage _ _)).trans
        (stageDeliveredMessage_runQueueStage _ _ _)))
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact (runQueueStage_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_readyKeptStage _ _ _ _ _ _ P) hCall).trans
        (runQueueStage_of_pair_eq
          (endpointCallCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ _ P) hCall).1
        (.of_stage (stageWokenDelivery_runQueueStage _ _ _))
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_readyKeptStage P.dequeued h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · refine readyKeptStage.of_stage ?_
        exact cspaceMintWithCdt_runQueueStage h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · refine readyKeptStage.of_stage ?_
      exact cspaceCopy_runQueueStage h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · refine readyKeptStage.of_stage ?_
      exact cspaceMove_runQueueStage h
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · refine readyKeptStage.of_stage ?_
      exact registerService_runQueueStage h
    · cases h
  case none.notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_readyKeptStage (runQueueStage_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig).entry (.of_stage (runQueueStage_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig))
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_readyKeptStage _ _ _ _ _ P) hW).trans
        (runQueueStage_of_pair_eq
          (notificationWaitCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ P) hW).1
        (.of_stage (writeReturnFrameToTcb_runQueueStage _ _ _))
    · rename_i hW
      cases h
      exact runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_readyKeptStage _ _ _ _ _ P) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_readyKeptStage P.objInv P.refined P.dequeued P.queueHeads
      P.current P.notIdle hRR).trans (endpointReplyRecvOnCore_runQueueEntryStage P.objInv
        P.refined P.dequeued P.queueHeads P.current P.notIdle hRR).1
      (.of_stage (stageDeliveredMessage_runQueueStage _ _ _))
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    refine readyKeptStage.of_stage ?_
    exact SystemState.RunQueueStage.of_frame rfl rfl rfl
  case none.declassifySignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_readyKeptStage (runQueueStage_of_pair_eq
        (notificationSignalDeclassifiedOnCore_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig).entry (.of_stage (runQueueStage_of_pair_eq
        (notificationSignalDeclassifiedOnCore_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig))
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h


/-- **The checked syscall dispatch keeps every ready thread other than the
caller ready**: the yield moves no thread's IPC state, the capability
resolution is a read, the routed arm keeps every thread but the caller ready,
and the taint pass writes the taint table and the taint words alone. -/
theorem dispatchSyscallChecked_readyKeptStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    readyKeptStage (· = tid) st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_readyKeptStage hYieldOk (P.placeable executingCore)
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  suffices hP : SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st executingCore)
      st stPost ∧ readyKeptStage (· = tid) st stPost from
    readyKeptStage.trans_links hP.1.1.links hP.2 (readyKeptStage.of_stage
      (SystemState.RunQueueStage.of_objectsAgreeOffTaint
        (applySyscallTaint_objectsAgreeOffTaint _ _ _) applySyscallTaint_invExt
        (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])
        (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])))
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  exact ⟨dispatchWithCapChecked_runQueueEntryStageOn ctx decoded tid executingCore _ cap _
    stPost P hD,
    dispatchWithCapChecked_readyKeptStage ctx decoded tid executingCore _ cap _ stPost P hD⟩


/-! ### The syscall entry -/

/-- **The checked syscall entry keeps every ready thread other than the core's
current thread ready**: the register and decode reads, the IPC-buffer fill
writing one core's TLB, and the dispatch, which blocks at most its caller. -/
theorem syscallEntryChecked_readyKeptStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState}
    (E : EntryPremises st)
    (hNI : ∀ tid, st.scheduler.currentOnCore e = some tid → isIdleThreadId tid = false)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    readyKeptStage (fun t => st.scheduler.currentOnCore e = some t) st st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  rename_i regs s hLk
  split at h
  · cases h
  rename_i decoded hDec
  dsimp only at h
  obtain ⟨t, ht⟩ := Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st e tid
    decoded.overflowCount
  rw [ht] at h
  have hF := SystemState.RunQueueStage.of_frame (st := st)
    (st' := { st with perCoreTlb := t }) rfl rfl rfl
  refine readyKeptStage.mono (S := (· = tid)) (fun x hx => hx ▸ hCur) ?_
  exact readyKeptStage.trans hF.entry.1 (.of_stage hF)
    (dispatchSyscallChecked_readyKeptStage ctx decoded tid e _ st'
      ((E.of_ipcFrame hF (IpcFrame.of_frame rfl fun _ => rfl)).arm hCur (hNI tid hCur)) h)

/-- **The ABI dispatch keeps every ready thread other than the core's current
thread ready**: the argument spill writes the caller's registers, then the
checked entry, the capability-fault delivery suspending the caller, or a
refusal record. -/
theorem syscallDispatchFromAbi_readyKeptStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (E : EntryPremises st)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    readyKeptStage (fun t => st.scheduler.currentOnCore e = some t) st st' := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact readyKeptStage.refl _
  rename_i tid hCur
  split at h
  · cases h; exact readyKeptStage.refl _
  rename_i hIdle
  have hNI : isIdleThreadId tid = false := by simpa using hIdle
  have hW : SystemState.RunQueueStage st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact SystemState.RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
  have E1 : EntryPremises (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) :=
    E.of_ipcFrame hW (by
      unfold Platform.FFI.writeFfiRegistersToTcb
      exact IpcFrame.updateTcb _ _ fun _ => rfl)
  have hCur1 : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).scheduler.currentOnCore e
      = some tid := by rw [Platform.FFI.writeFfiRegistersToTcb_scheduler]; exact hCur
  refine readyKeptStage.mono (S := (· = tid)) (fun x hx => hx ▸ hCur) ?_
  dsimp only at h
  split at h
  · split at h
    · cases h
      unfold Platform.FFI.deliverSyscallCapFault
      have hW2 := writeFaultRegistersToTcb_runQueueStage
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid
        (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)
      have E2 := E1.of_ipcFrame hW2 (by
        unfold writeFaultRegistersToTcb
        exact IpcFrame.updateTcb _ _ fun _ => rfl)
      exact readyKeptStage.trans (hW.trans hW2).entry.1 (.of_stage (hW.trans hW2))
        (faultDeliverOnCoreChecked_readyKeptStage _ _ tid _ _ e E2.endpointHeads
          (by rw [writeFaultRegistersToTcb_scheduler]; exact hCur1) hNI
          (E2.dequeued.runnable (by rw [writeFaultRegistersToTcb_scheduler]; exact hCur1)).activeAt)
    · cases h
      exact .of_stage (hW.trans (SystemState.RunQueueStage.of_frame
        ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
          (Architecture.recordErrorOverflow_objects _ _ _))
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
        (by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
        (hS := by rw [Platform.FFI.recordSyscallRefusal_scheduler_eq, Architecture.recordErrorOverflow_scheduler])
        (hRes := by
          unfold Platform.FFI.recordSyscallRefusal Architecture.recordErrorOverflow
          split <;> (try split) <;> (try split) <;> rfl)))
  · rename_i hE
    cases h
    refine readyKeptStage.trans hW.entry.1 (.of_stage hW)
      (readyKeptStage.mono (fun x hx => ?_) (syscallEntryChecked_readyKeptStage E1
        (fun t ht => by rw [hCur1] at ht; cases ht; exact hNI) hE))
    rw [hCur1] at hx; cases hx; rfl


/-- WS-ZA ZA6.20: **the syscall entry keeps a thread blocked in IPC resident on
no core.**  The trap-frame save and the IPC-buffer words block no thread; every
dispatch arm blocks at most the caller, the executing core's current thread
(`syscallDispatchFromAbi_readyKeptStage`); the caller's return staging and the
local scheduling point block none; and the caller is resident on no other core
(`currentNotResidentElsewhere`).  The dispatch's coverage reads its premises at
the state the dispatch runs from, as the sister carry's does
(`syscallDispatchEntryState_preserves_currentNotResidentElsewhere`). -/
theorem syscallDispatchEntryState_preserves_blockedNotResident (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (E : EntryPremises st)
    (hInv0 : st.objects.invExt) (hR0 : st.runQueueRefined) (hD0 : st.currentDequeuedUnique)
    (hB : finalisingDeleteBundle (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hPlaced : placedThreadsHaveTcbs (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hAwayCur : ∀ t, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e = some t →
      ∀ c, (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n).queuedOn c t = false)
    (hC : st.currentNotResidentElsewhere) (hBNR : st.blockedNotResident) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2
      ).blockedNotResident := by
  refine BlockedNotResident.of_frame (X := (syscallDispatchCrossCoreStep ctx e trapped.syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n)).2) ?_
    (fun d tid hR => by
      have hM := syncUserWords_residentCode (syscallDispatchCrossCoreStep ctx e trapped.syscallId
        trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
        trapped.pstate trapped.sp trapped.x30 (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2 ByteArray.empty 0
      simp only [MachineState.residentOnCore] at hR ⊢; rw [← hM]; exact hR)
    (fun tid t' hT => ⟨t', by
      have hO := Architecture.IpcBufferRead.syncUserWords_objects (syscallDispatchCrossCoreStep
        ctx e trapped.syscallId
        trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
        trapped.pstate trapped.sp trapped.x30 (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2 ByteArray.empty 0
      unfold SystemState.getTcb? at hT ⊢
      rw [← hO]; exact hT, rfl⟩)
  have hS := (saveCapturedSyscallFrame_runQueueStage st e frame).trans
    (SystemState.RunQueueStage.of_frame (Architecture.IpcBufferRead.syncUserWords_objects _ _ _)
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hS := by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
      (hRes := by unfold Architecture.IpcBufferRead.syncUserWords; split <;> rfl)
      (st' := Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
  have hF := (saveCapturedSyscallFrame_ipcFrame st e frame).trans
    (IpcFrame.of_frame (Architecture.IpcBufferRead.syncUserWords_objects
        (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
      fun _ => by rw [Architecture.IpcBufferRead.syncUserWords_scheduler])
  have ES := E.of_ipcFrame hS hF
  obtain ⟨hInvS, hRS⟩ := hS.1.links hInv0 hR0
  have hS0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler = st.scheduler := by
    rw [Architecture.IpcBufferRead.syncUserWords_scheduler, saveCapturedSyscallFrame_scheduler]
  have hM0 : (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).machine.residentCode =
        st.machine.residentCode := by
    rw [syncUserWords_residentCode, saveCapturedSyscallFrame_residentCode]
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e trapped.syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5 trapped.x6 trapped.pc
    trapped.pstate trapped.sp trapped.x30
    (Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame) bytes n)
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  have A := syscallDispatchFromAbi_runQueueEntryStage ES hD
  have B := (stageCallerReturnFor_runQueueStage ((Architecture.IpcBufferRead.syncUserWords
    (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e)
    st' e outcome)
  have ABC := A.trans ((B.entry.trans (scheduleLocalSuccessorFrom_runQueueEntryStage
    ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n).scheduler.currentOnCore e) _ e)).toOn _)
  have Full := (hS.entry.toOn _).trans (ABC.trans
    ((settleThenActivateOnCore_runQueueEntryStage _ e).toOn _))
  obtain ⟨hInvM, hRM⟩ := ABC.1.links hInvS hRS
  obtain ⟨hDc, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInvS hB hPlaced hAwayCur hD
  obtain ⟨hStage, hStageInv⟩ := stageCallerReturnFor_stepCovers e
    ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
      bytes n).scheduler.currentOnCore e) st' outcome hDInv
  have hCov := stepCovers_trans (stepCovers_trans hDc hStage)
    (scheduleLocalSuccessorFrom_stepCovers e
      ((Architecture.IpcBufferRead.syncUserWords (Architecture.saveCapturedSyscallFrame st e frame)
        bytes n).scheduler.currentOnCore e) _ hStageInv)
  have r : readyKeptStage (fun t => (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e = some t)
      _ _ :=
    (syscallDispatchFromAbi_readyKeptStage ES hD).trans_links A.1.links
      ((readyKeptStage.of_stage B).trans B.entry.1 fun hI hR =>
        .of_stateMono (scheduleLocalSuccessorFrom_stateMono
          ((Architecture.IpcBufferRead.syncUserWords
            (Architecture.saveCapturedSyscallFrame st e frame) bytes n).scheduler.currentOnCore e)
          _ e hI hR))
  refine BlockedNotResident.clearLedgers' ?_
  exact settleThenActivateOnCore_blockedNotResident hBNR hC hInvM hRM
    (residentKeptOffCore_trans (residentKeptOffCore_of_eq hM0) hCov.residentKept)
    ((readyKeptExcept.of_stateMono (hS.2.2 hInv0 hR0)).trans
      (fun t hn => r hInvS hRS t fun hc => hn (by rwa [hS0] at hc)))
    (Full.2 hInv0 hR0 (Full.1.links hInv0 hR0).2 hD0)

end SeLe4n.Kernel
