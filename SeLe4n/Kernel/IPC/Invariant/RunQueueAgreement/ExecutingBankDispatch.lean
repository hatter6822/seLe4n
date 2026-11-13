/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.ExecutingBankFrame

/-!
# The executing core's bank across the syscall dispatch, per arm

Each arm of the dispatch keeps `bankAgree` on the executing core `ec` for its
caller `tid` (`ExecutingBankFrame`), organised as the census
(`SavedRegistersCapabilityDispatch`, `SavedRegistersDispatch`) is:

* an arm with no scheduling point is covered at a core other than `ec`
  (`otherCore ec`), and its census holds there, so it keeps `ec`'s bank and
  slot and writes no thread current on `ec`; its stagings into the caller write
  the caller's return window alone (`bankFrame.*_caller`);
* a scheduling arm's prefix does the same (`SchedPointPrefix.bankAgree`), and its
  scheduling point keeps the agreement;
* the yield ends in the budget-aware scheduler, which establishes the match.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The Consumed invocation keeps the agreement**: covered at another core, it
writes a scheduling context and the consumed time into its caller's return
window (`setConsumed`). -/
theorem schedContextConsumedOnCore_bankAgree {e e' : CoreId} {c0 : SeLe4n.ThreadId}
    {s : SeLe4n.SchedContextId} {st st' : SystemState} (hne : e ≠ e')
    (hInv : st.objects.invExt) (hCur : st.scheduler.currentOnCore e = some c0)
    (hA : bankAgree e c0 st) (h : schedContextConsumedOnCore s e st = .ok st') :
    bankAgree e c0 st' := by
  have C := (schedContextConsumedOnCore_stepCovers e' hInv h).1
  obtain ⟨caller, hC, rfl⟩ := schedContextConsumedOnCore_ok h
  rw [hCur] at hC; cases hC
  refine (bankFrame.of_maskKept hne C ?_).bankAgree hA
  unfold setConsumed
  split
  · exact (regsMaskKept.of_kept (savedRegsKeptExcept.updateSchedContext (W := fun _ => False)
      st _ _ hInv)).trans (regsMaskKept.updateTcb_caller _
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) fun _ => rfl)
  · exact .refl _

/-- WS-ZA ZA6.29: a step keeping core `e`'s bank and slot and the saved context
of each thread current on `e` after it. -/
theorem bankFrame.of_savedRegs {e : CoreId} {c0 : SeLe4n.ThreadId} {pre post : SystemState}
    (hM : post.machine.regsOnCore e = pre.machine.regsOnCore e) (hK : currentKeptOnCore e pre post)
    (hR : ∀ t, post.scheduler.currentOnCore e = some t → post.savedRegs t = pre.savedRegs t) :
    bankFrame e c0 pre post :=
  ⟨hM, hK, fun t ht => by rw [hR t ht]⟩

theorem yieldToLinkPrefix_machine (S : SystemState) (c : CoreId) (s : SeLe4n.SchedContextId)
    (caller t : SeLe4n.ThreadId) (pC pT : SeLe4n.Priority) :
    (SchedContextOps.yieldToLinkPrefix S c s caller t pC pT).machine = S.machine := by
  unfold SchedContextOps.yieldToLinkPrefix
  simp only [SystemState.runEnqueueHeadOnCore_machine]
  unfold SystemState.runDescheduleOnCore
  simp only [SystemState.runRemoveOnCore_machine, SystemState.setYieldLink_machine]

theorem yieldToRequeue_machine (S : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : (SchedContextOps.yieldToRequeue S home t p).machine = S.machine := by
  unfold SchedContextOps.yieldToRequeue
  split
  · rfl
  · simp

theorem yieldToRequeue_currentOnCore (S : SystemState) (home : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (c : CoreId) :
    (SchedContextOps.yieldToRequeue S home t p).scheduler.currentOnCore c =
      S.scheduler.currentOnCore c := by
  unfold SchedContextOps.yieldToRequeue
  split
  · rfl
  · simp only [SystemState.markReschedulePendingOnCore_scheduler,
      SchedulerState.markReschedulePendingOnCore_currentOnCore,
      SystemState.runEnqueueHeadOnCore_currentOnCore]
    simp [SchedulerState.setRunQueueOnCore, SchedulerState.setRunQueueEndsOnCore,
      SchedulerState.currentOnCore]

/-- WS-ZA ZA6.29: **the yieldTo invocation keeps the agreement**: the completion
writes the context's earlier yielder, which is linked and so not the caller;
the resume and the requeue write no saved context; `setConsumed` writes the
caller's return window; the linked branch's prefix writes no saved context and
keeps or clears the core's slot, and its scheduling point keeps the
agreement. -/
theorem schedContextYieldToOnCore_bankAgree {e e' : CoreId} {c0 : SeLe4n.ThreadId}
    {s : SeLe4n.SchedContextId} {st st' : SystemState} (hne : e ≠ e')
    (hInv : st.objects.invExt) (hYA : st.yieldLinksAgree) (hYN : st.yieldLinkedNotResident)
    (hCur : st.scheduler.currentOnCore e = some c0)
    (hA : bankAgree e c0 st) (h : SchedContextOps.schedContextYieldToOnCore s e st = .ok st') :
    bankAgree e c0 st' := by
  obtain ⟨caller, -, t, -, -, hC, -, -, -, -, -, -, -, rfl⟩ :=
    SchedContextOps.schedContextYieldToOnCore_ok h
  rw [hCur] at hC; cases hC
  have F1 : bankFrame e c0 st (completeYieldFrom st s) :=
    .of_savedRegs (by rw [SystemState.completeYieldFrom_eq_objects])
      (.of_eq (by rw [SystemState.completeYieldFrom_scheduler])) fun u hu => by
        rw [SystemState.completeYieldFrom_scheduler, hCur] at hu
        cases hu
        refine completeYieldFrom_savedRegsKeptExcept hInv _ ?_
        rintro ⟨sc, k, hS, hCd, hk⟩
        rw [hk] at hCur
        exact ((offCoreFree_of_yieldCode (e := e') hYN (yieldCode_of_yieldFrom hYA hS hCd)) e hne).1 hCur
  have hInv1 := SystemState.completeYieldFrom_preserves_objects_invExt st s hInv
  unfold SchedContextOps.yieldToBound
  dsimp only
  have hW := SystemState.releasePlace_releaseOnlyWrite (completeYieldFrom st s)
    (determineTargetCore (completeYieldFrom st s) t) s
  have F2 : bankFrame e c0 (completeYieldFrom st s) ((completeYieldFrom st s).releasePlace
      (determineTargetCore (completeYieldFrom st s) t) s) :=
    .of_savedRegs (by rw [hW.machine]) (.of_eq (hW.currentOnCore e)) fun u _ =>
      (savedRegsKeptExcept.of_releaseLinks (W := fun _ => False)
        (SystemState.releasePlace_agree _ _ _)) u id
  have hInv2 := SystemState.releasePlace_objects_invExt _
    (determineTargetCore (completeYieldFrom st s) t) s hInv1
  have hA2 := (F1.trans F2).bankAgree hA
  generalize (completeYieldFrom st s).releasePlace (determineTargetCore (completeYieldFrom st s) t)
    s = st2 at hA2 hInv2 ⊢
  have hSet : ∀ X : SystemState, X.objects.invExt → bankAgree e c0 X →
      bankAgree e c0 (setConsumed X s c0) := fun X hX hAX =>
    (bankFrame.mk (by rw [SystemState.setConsumed_eq_objects])
      (.of_eq (by rw [SystemState.setConsumed_scheduler])) fun u _ => (by
        unfold setConsumed
        split
        · exact (regsMaskKept.of_kept (savedRegsKeptExcept.updateSchedContext (W := fun _ => False)
            X _ _ hX)).trans (regsMaskKept.updateTcb_caller _
              (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hX) fun _ => rfl)
        · exact .refl _ : regsMaskKept c0 X (setConsumed X s c0)) u).bankAgree hAX
  have hLink : ∀ pC pT, bankAgree e c0 (SchedContextOps.yieldToLink st2 e s c0 t pC pT) :=
    fun pC pT => bankAgree_schedPoint
      (SchedContextOps.yieldToLinkPrefix_objects_invExt st2 e s c0 t pC pT hInv2)
      ((bankFrame.of_savedRegs (by rw [yieldToLinkPrefix_machine])
        (yieldToLinkPrefix_currentKeptOnCore st2 e s c0 t pC pT) fun u _ =>
          (yieldToLinkPrefix_savedRegsKeptExcept (W := fun _ => False) st2 e s c0 t pC pT
            hInv2) u id).bankAgree hA2)
      (.inr (SchedContextOps.yieldToLink_sgi st2 e s c0 t pC pT))
  split
  · exact hSet _ hInv2 hA2
  · split
    · exact hSet _ hInv2 hA2
    · split
      · exact hSet _ hInv2 hA2
      · split
        · split
          · exact hSet _ (SchedContextOps.yieldToRequeue_objects_invExt _ _ _ _ hInv2)
              ((bankFrame.of_savedRegs (by rw [yieldToRequeue_machine])
                (.of_eq (yieldToRequeue_currentOnCore _ _ _ _ e)) fun u _ =>
                  (yieldToRequeue_savedRegsKeptExcept (W := fun _ => False) st2 _ t _) u id).bankAgree
                hA2)
          · exact hLink _ _
        · exact hSet _ hInv2 hA2

/-- **The resume keeps the agreement**: its fault retire writes the restart frame
of a suspended thread, which no core runs, and writes no bank and no slot; then
the resume's prefix and scheduling point. -/
theorem tcbResume_bankAgree {e e' : CoreId} {c0 : SeLe4n.ThreadId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {sgi? : Option (CoreId × Concurrency.SgiKind)} (hne : e ≠ e')
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hA : bankAgree e c0 st)
    (h : Lifecycle.Suspend.resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid e =
      .ok (st', sgi?)) : bankAgree e c0 st' := by
  have hSch := retirePendingFaultForResume_scheduler_eq st vtid.val
  have hInv1 := retirePendingFaultForResume_preserves_objects_invExt st vtid.val hInv
  have hStage := retirePendingFaultForResume_runQueueStage st vtid.val
  have hD1 := hStage.2.1 none hInv hR (hStage.1 hInv hR).2 hD
  obtain ⟨tcb, hT, hIn⟩ := resumeThreadOnCore_inactive h
  have hCur : ∀ d, d ≠ e' → st.scheduler.currentOnCore d ≠ some vtid.val := fun d _ hd => by
    obtain ⟨x, hx, hAc⟩ := hD1.currentActive d vtid.val (by rw [hSch]; exact hd)
    rw [hT] at hx; cases hx; exact hAc hIn
  have F : bankFrame e c0 st (retirePendingFaultForResume st vtid.val) :=
    bankFrame.of_offCore hne ((retirePendingFaultForResume_keyFrame _ _ hInv).stepCovers (e := e')
      (hRes := by rw [retirePendingFaultForResume_machine])
      (hBank := banksKeptOffCore_of_eq (by rw [retirePendingFaultForResume_machine])))
      (retirePendingFaultForResume_savedRegsKeptOffCore hInv hCur)
  obtain ⟨_, Q⟩ := resumeThreadOnCore_schedPointPrefix
    (base := retirePendingFaultForResume st vtid.val) hInv1 h
  exact Q.bankAgree (.refl _) (F.bankAgree hA)

/-- WS-ZA ZA6.28: **every arm `dispatchCapabilityOnly` routes keeps the executing
core's agreement**: the finalising deletes, the retype and every arm with no
scheduling point are covered at another core, whose census they keep; the
Consumed invocation and the service query write the caller's return window
alone; the unbind, the suspend, the resume and the priority arms keep it through
their prefix and scheduling point. -/
theorem dispatchCapabilityOnly_bankAgree {decoded : SyscallDecodeResult}
    {cap : Capability} {tid : SeLe4n.ThreadId} {ec : CoreId} {k : Kernel Unit}
    {st st' : SystemState} (P : SyscallArmPremises st ec tid) (hRT : st.residentsHaveTcbs)
    (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs st)
    (hK : dispatchCapabilityOnly decoded cap tid ec = some k) (h : k st = .ok ((), st'))
    (hA : bankAgree ec tid st) : bankAgree ec tid st' := by
  have hInv := P.objInv
  have hBi := hB.bidirectional
  have B : FinaliseCensusBase st :=
    ⟨P.objInv, P.refined, P.toEntryPremises.blocked, hBNR, hYA, hYN⟩
  have hne := ne_otherCore ec
  generalize otherCore ec = e' at hne
  have hO : ∀ {s : SystemState}, stepCovers e' st s → savedRegsKeptOffCore e' st s →
      bankAgree ec tid s := fun hC hS => (bankFrame.of_offCore hne hC hS).bankAgree hA
  have hF : ∀ {s : SystemState}, savedRegsKept st s → stepCovers e' st s ∧ s.objects.invExt →
      bankAgree ec tid s := fun hS hC =>
    hO hC.1 (savedRegsKeptOffCore_of_savedRegsKept hS P.dequeued hRT hC.1.currentKept
      hC.1.residentKept)
  have hX : ∀ {s : SystemState}, savedRegsKeptExcept (fun _ => False) st s →
      stepCovers e' st s ∧ s.objects.invExt → bankAgree ec tid s := fun k hC =>
    (bankFrame.of_kept hne hC.1 k).bankAgree hA
  have hP : ∀ {s' : SystemState}, (∃ s, SchedPointPrefix ec st st s s') → bankAgree ec tid s' :=
    fun ⟨_, Q⟩ => Q.bankAgree (.refl _) hA
  have hSN : ∀ {line : Nat} {src : CSpaceAddr},
      irqHandlerSetNotification ec line src st = .ok ((), st') → bankAgree ec tid st' :=
    fun hN =>
      have hC := (irqHandlerSetNotification_stepCovers (e := e') hB hN).1
      hO hC (irqHandlerSetNotification_savedRegsKeptOffCore B hB P.dequeued hRT
        hC.currentKept hC.residentKept hN)
  unfold dispatchCapabilityOnly at hK
  cases hId : decoded.syscallId <;> rw [hId] at hK <;> simp only [Option.some.injEq,
    reduceCtorEq] at hK
  all_goals subst hK
  all_goals cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  all_goals (repeat' split at h)
  all_goals first | (cases h; done) | skip
  all_goals first
    | exact hO (cspaceDeleteSlotZombie_stepCovers _ _ _ _ _ hB h).1
        (cspaceDeleteSlotZombie_savedRegsKeptOffCore B hB h)
    | exact hO (cspaceRevokeCdtFinalising_stepCovers _ _ _ _ _ hB h).1
        (cspaceRevokeCdtFinalising_savedRegsKeptOffCore B hB h)
    | exact hF (mintReplyCapWithCdt_savedRegsKept hInv h)
        ((mintReplyCapWithCdt_keyFrame _ _ _ _ hInv h).stepCoversInv (e := e')
          (hRes := by rw [mintReplyCapWithCdt_machine_eq h])
          (hBank := banksKeptOffCore_of_eq (by rw [mintReplyCapWithCdt_machine_eq h])))
    | exact hF (untypedResetFromCap_savedRegsKept hInv h)
        ((untypedResetFromCap_keyFrame _ _ _ _ hInv h).stepCoversInv (e := e')
          (hRes := by rw [untypedResetFromCap_machine_eq h])
          (hBank := banksKeptOffCore_of_eq (by rw [untypedResetFromCap_machine_eq h])))
    | exact hF (vspaceMapOrRemapFromFrameCap_savedRegsKept hInv h)
        ((vspaceMapOrRemapFromFrameCap_keyFrame _ _ _ _ _ hInv h).stepCoversInv (e := e'))
    | exact hF (vspaceUnmapPageWithShootdownAndIcacheBroadcast_savedRegsKept hInv h)
        ((vspaceRootOnlyWrite_keyFrame
          (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame _ _ _ _ _ hInv h)).stepCoversInv
          (e := e'))
    | exact hF (vspaceUnifyInstructionPage_savedRegsKept h)
        ((capabilityKeyFrame_of_objects_scheduler_eq hInv
          (Architecture.vspaceUnifyInstructionPage_frame h).1
          (Architecture.vspaceUnifyInstructionPage_frame h).2.2.1).stepCoversInv (e := e')
          (hRes := by rw [(Architecture.vspaceUnifyInstructionPage_frame h).2.2.2.1])
          (hBank := banksKeptOffCore_of_eq
            (by rw [(Architecture.vspaceUnifyInstructionPage_frame h).2.2.2.1])))
    | exact hF (revokeServiceByRecordedRegistration_savedRegsKept hInv h)
        ((revokeServiceByRecordedRegistration_keyFrame hInv h).stepCoversInv (e := e'))
    | exact hF (pageTableMap_savedRegsKept hInv h)
        ((pageTableMap_keyFrame _ _ _ _ _ hInv h).stepCoversInv (e := e'))
    | exact hF (pageTableUnmap_savedRegsKept hInv h)
        ((pageTableUnmap_keyFrame _ _ _ hInv h).stepCoversInv (e := e'))
    | exact hF (irqHandlerAck_savedRegsKept h) (irqHandlerAck_stepCovers (e := e') hInv h)
    | exact hO (cspaceDeleteSlotZombie_stepCovers _ _ _ _ _ hB (irqHandlerClear_ok h).2).1
        (cspaceDeleteSlotZombie_savedRegsKeptOffCore B hB (irqHandlerClear_ok h).2)
    | exact hF (irqControlGet_savedRegsKept hInv
          (irqControlGetFromCap_ok _ _ _ _ _ h).choose_spec.choose_spec.choose_spec.2.2.2)
        (irqControlGet_stepCovers (e := e') hInv
          (irqControlGetFromCap_ok _ _ _ _ _ h).choose_spec.choose_spec.choose_spec.2.2.2)
    | exact hSN (irqHandlerSetNotificationFromCap_ok _ _ _ _ _ _ h).choose_spec.choose_spec.2
    | exact hX (schedControlConfigure_savedRegsKeptExcept hInv h)
        (schedControlConfigure_stepCovers _ _ _ _ _ _ _ _ _ _ hInv hBi h)
    | exact hX (schedContextBind_savedRegsKeptExcept hInv h)
        (schedContextBind_stepCovers _ _ _ _ _ hInv hBi h)
    | exact hX (bindNotification_savedRegsKeptExcept hInv h)
        ((bindNotification_keyFrame _ _ _ _ hInv h).stepCoversInv (e := e'))
    | (obtain ⟨_, _, _, _, _, _, _, _, _, hU⟩ := untypedRetypeFromCap_ok _ _ _ _ _ _ h
       exact hF (untypedRetypeFromCap_savedRegsKept hInv h)
         (untypedRetypeObject_stepCovers e' hInv hBi hPlaced hU))
    | (cases h; rename_i hS
       first
        | (rw [lookupServiceByRecordedRegistration_preserves_state _ _ _ _ hS]
           exact (bankFrame.writeReturnFrameToTcb_caller _ hInv).bankAgree hA)
        | exact hP (schedContextUnbindOnCore_schedPointPrefix hInv hS)
        | exact schedContextConsumedOnCore_bankAgree hne hInv P.current hA hS
        | exact schedContextYieldToOnCore_bankAgree hne hInv hYA hYN P.current hA hS
        | exact hX (unbindNotification_savedRegsKeptExcept hInv hS)
            ((unbindNotification_keyFrame _ _ _ hInv hS).stepCoversInv (e := e')
              (hRes := by rw [unbindNotification_machine_eq hS])
              (hBank := banksKeptOffCore_of_eq (by rw [unbindNotification_machine_eq hS])))
        | exact hP (suspendThreadOnCore_schedPointPrefix hInv P.toEntryPremises.blocked hBNR hS)
        | exact tcbResume_bankAgree hne hInv P.refined P.dequeued hA hS
        | exact hP (setPriorityOnCore_schedPointPrefix hInv hS)
        | exact hP (setMCPriorityOnCore_schedPointPrefix hInv hS)
        | exact hX (setThreadCpuAffinityWithMigration_savedRegsKeptExcept hInv hS)
            (setThreadCpuAffinityWithMigration_stepCovers _ _ _ _ e' _ _ hInv hS)
        | exact hX (setIPCBufferOp_savedRegsKeptExcept hInv hS)
            ((setIPCBufferOp_keyFrame _ _ _ _ hInv hS).stepCoversInv (e := e')
              (hRes := by rw [Architecture.IpcBufferValidation.setIPCBufferOp_machine_eq _ _ _ _ hS])
              (hBank := banksKeptOffCore_of_eq
                (by rw [Architecture.IpcBufferValidation.setIPCBufferOp_machine_eq _ _ _ _ hS])))
        | exact hX (setThreadFaultHandlerOp_savedRegsKeptExcept hInv hS)
            ((setThreadFaultHandlerOp_keyFrame _ _ _ _ hInv hS).stepCoversInv (e := e')
              (hRes := by rw [setThreadFaultHandlerOp_machine_eq hS])
              (hBank := banksKeptOffCore_of_eq (by rw [setThreadFaultHandlerOp_machine_eq hS])))
        | exact hO (copyThreadSpacesZombie_stepCovers _ _ _ _ _ _ _ _ hB hS).1
            (copyThreadSpacesZombie_savedRegsKeptOffCore B hB hS))

/-- WS-ZA ZA6.28: **every arm `dispatchWithCapChecked` routes keeps the executing
core's agreement**: the capability-only arms by
`dispatchCapabilityOnly_bankAgree`; every IPC, notification, CSpace, registry,
declassification and audit arm is covered at another core, whose census it
keeps up to its staging into the caller, and that staging writes the caller's
return window alone. -/
theorem dispatchWithCapChecked_bankAgree {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {ec : CoreId} {gate : SyscallGate}
    {cap : Capability} {st st' : SystemState} (P : SyscallArmPremises st ec tid)
    (hRT : st.residentsHaveTcbs) (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident)
    (hYA : st.yieldLinksAgree) (hYN : st.yieldLinkedNotResident)
    (hPlaced : placedThreadsHaveTcbs st)
    (h : dispatchWithCapChecked ctx decoded tid ec gate cap st = .ok ((), st'))
    (hA : bankAgree ec tid st) : bankAgree ec tid st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid ec with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_bankAgree P hRT hB hBNR hYA hYN hPlaced hC
      (dispatchCapabilityOnlyChecked_ok hC h) hA
  | none =>
  rw [hC] at h
  dsimp only at h
  have hInv := P.objInv
  have hne := ne_otherCore ec
  generalize otherCore ec = e' at hne
  have hW : ∀ {s : SystemState}, stepCovers e' st s → savedRegsWrittenFree e' st st s →
      bankFrame ec tid st s := fun hC hW => bankFrame.of_writtenFree hne hC hW
  have hF : ∀ {s : SystemState}, savedRegsKept st s → stepCovers e' st s ∧ s.objects.invExt →
      bankAgree ec tid s := fun hS hC =>
    (bankFrame.of_offCore hne hC.1 (savedRegsKeptOffCore_of_savedRegsKept hS P.dequeued hRT
      hC.1.currentKept hC.1.residentKept)).bankAgree hA
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA'
    cases h
    rw [auditReadFromCore_frame _ _ _ _ _ _ _ hA']
    exact (bankFrame.writeReturnFrameToTcb_caller _ hInv).bankAgree hA
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA'
    cases h
    unfold auditDrainVisiblePrefix at hA'
    split at hA'
    · cases hA'
      refine (bankFrame.trans ?_ (bankFrame.writeReturnFrameToTcb_caller _ ?_)).bankAgree hA
      · exact bankFrame.of_frame rfl rfl rfl
      · exact hInv
    · cases hA'
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
      (endpointSendCrossCoreDispatchChecked_stepCovers e' hInv) hSend
    have hCv := (stepCovers_clearStash_stage hS hSInv
      (fun x hx => stageWokenDelivery_keyFrame x _ _ hx) h).1
    split at h
    · cases h
    rename_i hClr
    cases h
    exact (hW hCv (sendArm_savedRegsWrittenFree _ P hRT hBNR hSend hClr)).bankAgree hA
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    obtain ⟨hV, hVInv⟩ := stepCovers_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_stepCovers e' hInv) hRecv
    obtain ⟨hD, hDInv⟩ := applyReceiveRendezvousHandoff_stepCovers e' hVInv hHand
    have hS1 := stageWokenSendCompletion_keyFrame stDon
      ((st.getEndpoint? epId).bind (·.sendQ.head)) hDInv
    obtain ⟨w1, i1⟩ := receiveArmCompletion_savedRegsWrittenFree (e := e') P hRT hBNR hRecv hHand
    exact ((hW (stepCovers_trans (stepCovers_trans hV hD) hS1.stepCovers) w1).trans
      (bankFrame.stageDeliveredMessage_caller _ i1)).bankAgree hA
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_stepCovers e' hInv) hCall
      exact (hW (stepCoversInv_trans hS (stageWokenDelivery_keyFrame _ _ _ hSInv).stepCoversInv).1
        (callArm_savedRegsWrittenFree _ P hRT hBNR hCall)).bankAgree hA
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact (hW (replyTransferOnCoreChecked_stepCovers e' hInv h).1
      (replyTransferOnCoreChecked_savedRegsWrittenFree P.dequeued hRT hBNR hInv h)).bankAgree hA
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact hF (cspaceMintWithCdt_savedRegsKept hInv h)
          ((cspaceMintWithCdt_keyFrame _ _ _ _ _ _ hInv h).stepCoversInv (e := e')
            (hRes := by rw [cspaceMintWithCdt_machine_eq h])
            (hBank := banksKeptOffCore_of_eq (by rw [cspaceMintWithCdt_machine_eq h])))
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact hF (cspaceCopy_savedRegsKept hInv h)
        ((cspaceCopy_keyFrame _ _ _ _ _ hInv h).stepCoversInv (e := e')
          (hRes := by rw [cspaceCopy_machine_eq h])
          (hBank := banksKeptOffCore_of_eq (by rw [cspaceCopy_machine_eq h])))
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact hF (cspaceMove_savedRegsKept hInv h)
        ((cspaceMove_keyFrame _ _ _ _ hInv h).stepCoversInv (e := e')
          (hRes := by rw [cspaceMove_machine_eq h])
          (hBank := banksKeptOffCore_of_eq (by rw [cspaceMove_machine_eq h])))
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · exact hF (savedRegsKept.of_serviceRecordRewrite hInv (registerService_serviceRecordRewrite h))
        ((registerService_keyFrame hInv h).stepCoversInv (e := e')
          (hRes := by rw [registerService_preserves_machine _ _ _ h])
          (hBank := banksKeptOffCore_of_eq (by rw [registerService_preserves_machine _ _ _ h])))
    · cases h
  case none.notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_stepCovers e' hInv) hSig
      have hCv := (stepCovers_clearStash_stage hS hSInv (fun x hx => keyFrame_trans_stage hx) h).1
      split at h
      · cases h
      rename_i hClr
      cases h
      exact (hW hCv (notificationSignalArm_savedRegsWrittenFree P hRT hBNR hSig hClr)).bankAgree hA
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hWt
      cases h
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_stepCovers e' hInv) hWt
      have h1 := notificationWaitCrossCoreDispatchChecked_savedRegsUnwritten ctx notifId tid ec
        P.objInv
      rw [hWt] at h1
      exact ((bankFrame.of_unwritten hne hS h1).trans
        (bankFrame.writeReturnFrameToTcb_caller _ h1.2)).bankAgree hA
    · rename_i hWt
      cases h
      have h1 := notificationWaitCrossCoreDispatchChecked_savedRegsUnwritten ctx notifId tid ec
        P.objInv
      rw [hWt] at h1
      exact (bankFrame.of_unwritten hne (stepCovers_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_stepCovers e' hInv) hWt).1 h1).bankAgree hA
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    obtain ⟨hS, hSInv⟩ := endpointReplyRecvOnCore_stepCovers e' hInv hRR
    obtain ⟨w, i⟩ := endpointReplyRecvOnCore_savedRegsWrittenFree P.dequeued P.queueHeads hRT
      hBNR hInv hRR
    exact ((hW hS w).trans (bankFrame.stageDeliveredMessage_caller _ i)).bankAgree hA
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    exact (bankFrame.of_frame rfl rfl rfl).bankAgree hA
  case none.declassifySignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationSignalDeclassifiedOnCore_stepCovers e' hInv) hSig
      have hCv := (stepCovers_clearStash_stage hS hSInv (fun x hx => keyFrame_trans_stage hx) h).1
      split at h
      · cases h
      rename_i hClr
      cases h
      exact (hW hCv (declassifySignalArm_savedRegsWrittenFree P hRT hBNR hSig hClr)).bankAgree hA
    · cases h

/-! ### The yield, the taint pass and the checked dispatch -/

/-- **The yield establishes the executing core's match**: its charge keeps the
store well formed and ends in the budget-aware scheduler, which restores its
choice into the bank. -/
theorem yieldOnCore_contextMatchesCurrentOnCore {st st' : SystemState} {e : CoreId}
    (hInv : st.objects.invExt) (h : yieldOnCore st e = .ok st') :
    contextMatchesCurrentOnCore st' e := by
  unfold yieldOnCore at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i st1 hCharge
  exact scheduleEffectiveOnCore_establishes_contextMatchesCurrentOnCore st1 e st'
    (yieldChargeOnCore_savedRegsUnwritten hInv hCharge).2 h

/-- The taint pass writes taint words alone: no saved register, slot or bank. -/
theorem bankFrame.of_taint {e : CoreId} {c0 : SeLe4n.ThreadId} (plan : TaintPlan)
    (pre post : SystemState) : bankFrame e c0 post (applySyscallTaint plan pre post) :=
  ⟨by rw [applySyscallTaint_machine], .of_eq (by rw [applySyscallTaint_scheduler]),
    fun t _ => by
      rw [savedRegsKeptExcept.of_objectsAgreeOffTaint (W := fun _ => False)
        (applySyscallTaint_objectsAgreeOffTaint _ _ _) t id]⟩

/-- WS-ZA ZA6.28: **the checked syscall dispatch keeps the executing core's
agreement**: the yield establishes the match, the capability resolution is a
read, every routed arm keeps the agreement (`dispatchWithCapChecked_bankAgree`),
and the taint pass writes taint words alone. -/
theorem dispatchSyscallChecked_bankAgree {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {e : CoreId} {st st' : SystemState}
    (P : SyscallArmPremises st e tid) (hRT : st.residentsHaveTcbs)
    (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs st)
    (h : dispatchSyscallChecked ctx decoded tid e st = .ok ((), st'))
    (hA : bankAgree e tid st) : bankAgree e tid st' := by
  have hInv := P.objInv
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact bankAgree_of_match (yieldOnCore_contextMatchesCurrentOnCore hInv hYieldOk)
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  suffices hP : bankAgree e tid stPost from (bankFrame.of_taint _ _ _).bankAgree hP
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  exact dispatchWithCapChecked_bankAgree P hRT hB hBNR hYA hYN hPlaced hD hA

/-- WS-ZA ZA6.28: **the checked syscall entry keeps the executing core's
agreement**: the register and decode reads write nothing, the IPC-buffer fill
writes one core's TLB, and the dispatch keeps it
(`dispatchSyscallChecked_bankAgree`). -/
theorem syscallEntryChecked_bankAgree {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} {c0 : SeLe4n.ThreadId} (E : EntryPremises st)
    (hNI : ∀ tid, st.scheduler.currentOnCore e = some tid → isIdleThreadId tid = false)
    (hRT : st.residentsHaveTcbs) (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident)
    (hYA : st.yieldLinksAgree) (hYN : st.yieldLinkedNotResident)
    (hPlaced : placedThreadsHaveTcbs st) (hC0 : st.scheduler.currentOnCore e = some c0)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st'))
    (hA : bankAgree e c0 st) : bankAgree e c0 st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  rw [hC0] at hCur; cases hCur
  split at h
  · cases h
  rename_i regs s hLk
  split at h
  · cases h
  rename_i decoded hDec
  dsimp only at h
  obtain ⟨t, ht⟩ := Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st e c0
    decoded.overflowCount
  rw [ht] at h
  have hF := SystemState.RunQueueStage.of_frame (st := st)
    (st' := { st with perCoreTlb := t }) rfl rfl rfl
  exact dispatchSyscallChecked_bankAgree (st := { st with perCoreTlb := t })
    ((E.of_ipcFrame hF (IpcFrame.of_frame rfl fun _ => rfl)).arm hC0 (hNI c0 hC0))
    hRT (finalisingDeleteBundle.of_objects_scheduler_eq (s := st) rfl rfl hB) hBNR hYA hYN
    hPlaced h hA

end SeLe4n.Kernel
