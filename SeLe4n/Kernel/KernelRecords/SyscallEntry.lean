-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Entry
import SeLe4n.Kernel.ReschedulePendingArms.Entry
import SeLe4n.Kernel.ReplyRecvRefusalErrors

/-! # The syscall entry keeps the records, and every committing entry preserves them

WS-ZA ZA6.37.  The syscall entry's committed state is a records stage: the
trap-frame save, the IPC-buffer words handed to the state, the argument spill,
the checked entry (or the capability-fault delivery, or the refusal record),
the caller's return staging, the local scheduling point, the residency
settlement and the ledger drains.  The dispatch reads its premises
(`RecordsArmPremises`, the running caller `.ready` in IPC) off the state the
step runs from; the spill writes registers alone, so it keeps them.

Each committing entry then preserves `kernelRecordsSound` outright: the
`*_preserves_kernelRecordsSound` theorems close each stage on the state the
entry starts from.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### The dispatch premises across register writes -/

/-- A step that writes no object and keeps the scheduler keeps the dispatch
premises. -/
theorem RecordsArmPremises.of_objects_scheduler_eq {s s' : SystemState}
    (hO : s'.objects = s.objects) (hS : s'.scheduler = s.scheduler) (P : RecordsArmPremises s) :
    RecordsArmPremises s' := by
  have hG : ∀ t, s'.getTcb? t = s.getTcb? t := fun t => by unfold SystemState.getTcb?; rw [hO]
  have F := finalisingDeleteBundle.of_objects_scheduler_eq hO hS P.deletes.2
  refine ⟨⟨ipcReachable_of_bundle F ((ReachLinkFrame.of_objects_eq hO hS).preserves
    P.deletes.1.reachQueueInvariant), F⟩, fun t tcb ht hI => ?_⟩
  rw [hG] at ht
  have Q := P.inactiveQuiescent t tcb ht hI
  exact ⟨fun x hx => Q.ready x (by rw [← hG]; exact hx),
    fun x hx => Q.noNext x (by rw [← hG]; exact hx),
    fun x hx => Q.noPrev x (by rw [← hG]; exact hx),
    fun x hx => Q.noPPrev x (by rw [← hG]; exact hx),
    fun x hx => Q.noStash x (by rw [← hG]; exact hx),
    fun x hx => Q.noPendingMsg x (by rw [← hG]; exact hx),
    fun x hx => Q.noBudget x (by rw [← hG]; exact hx)⟩

/-- A TCB write that keeps the thread state and every quiescent field keeps
every `.Inactive` thread quiescent. -/
theorem inactiveQuiescent_updateTcb {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).threadState = x.threadState ∧ (f x).ipcState = x.ipcState ∧
      (f x).queueNext = x.queueNext ∧ (f x).queuePrev = x.queuePrev ∧
      (f x).queuePPrev = x.queuePPrev ∧ (f x).pendingReceiveReply = x.pendingReceiveReply ∧
      (f x).pendingMessage = x.pendingMessage ∧ (f x).timeoutBudget = x.timeoutBudget)
    (hQ : ∀ t tcb, st.getTcb? t = some tcb → tcb.threadState = .Inactive →
      threadIpcFieldsQuiescent st t) :
    ∀ t tcb, (st.updateTcb tid f).getTcb? t = some tcb → tcb.threadState = .Inactive →
      threadIpcFieldsQuiescent (st.updateTcb tid f) t := by
  intro t tcb ht hI
  have hG := updateTcb_getTcb?_eq (f := f) (tid := tid) hInv t
  rw [ht] at hG
  split at hG
  · cases hx : st.getTcb? t with
    | none => rw [hx] at hG; cases hG
    | some x =>
      rw [hx, Option.map_some] at hG
      cases hG
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hf x
      have Q := hQ t x hx (by rw [← h0]; exact hI)
      have E : ∀ y, (st.updateTcb tid f).getTcb? t = some y → y = f x := fun y hy =>
        Option.some.inj (hy.symm.trans ht)
      exact ⟨fun y hy => by rw [E y hy]; exact h1.trans (Q.ready x hx),
        fun y hy => by rw [E y hy]; exact h2.trans (Q.noNext x hx),
        fun y hy => by rw [E y hy]; exact h3.trans (Q.noPrev x hx),
        fun y hy => by rw [E y hy]; exact h4.trans (Q.noPPrev x hx),
        fun y hy => by rw [E y hy]; exact h5.trans (Q.noStash x hx),
        fun y hy => by rw [E y hy]; exact h6.trans (Q.noPendingMsg x hx),
        fun y hy => by rw [E y hy]; exact h7.trans (Q.noBudget x hx)⟩
  · have Q := hQ t tcb hG.symm hI
    have E : ∀ y, (st.updateTcb tid f).getTcb? t = some y → st.getTcb? t = some y :=
      fun y hy => by rw [← hy, ht]; exact hG.symm
    exact ⟨fun y hy => Q.ready y (E y hy), fun y hy => Q.noNext y (E y hy),
      fun y hy => Q.noPrev y (E y hy), fun y hy => Q.noPPrev y (E y hy),
      fun y hy => Q.noStash y (E y hy), fun y hy => Q.noPendingMsg y (E y hy),
      fun y hy => Q.noBudget y (E y hy)⟩

/-- The ABI argument spill writes one thread's registers alone, so it keeps
the dispatch premises. -/
theorem RecordsArmPremises.writeFfiRegistersToTcb {st : SystemState} (tid : SeLe4n.ThreadId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 : UInt64) (P : RecordsArmPremises st) :
    RecordsArmPremises
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
  have hInv := P.deletes.2.1.2.1
  have F := finalisingDeleteBundle_writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 x6
    P.deletes.2
  unfold Platform.FFI.writeFfiRegistersToTcb at F ⊢
  refine ⟨⟨ipcReachable_of_bundle F ?_, F⟩,
    inactiveQuiescent_updateTcb hInv (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      P.inactiveQuiescent⟩
  refine ReachLinkFrame.preserves (st := st) ?_ P.deletes.1.reachQueueInvariant
  exact ReachLinkFrame.updateTcb st tid _ hInv fun _ => rfl

/-- The spill keeps every running thread `.ready` in IPC. -/
theorem CurrentReady.writeFfiRegistersToTcb {st : SystemState} (tid : SeLe4n.ThreadId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 : UInt64) (hInv : st.objects.invExt)
    (hR : CurrentReady st) :
    CurrentReady (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
  intro c t hc
  unfold Platform.FFI.writeFfiRegistersToTcb at hc ⊢
  rw [SystemState.updateTcb_scheduler] at hc
  exact (hR c t hc).updateTcb hInv fun _ => rfl

/-! ### The syscall entry -/

/-- **The checked syscall entry keeps the records**: the register read and the
decode read, the IPC-buffer fill writes one core's TLB, and the dispatch is a
stage from the premises the fill keeps, for the caller the core runs. -/
theorem syscallEntryChecked_recordsStage {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (P : RecordsArmPremises st) (hR : CurrentReady st)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  split at h
  · cases h
  rename_i decoded hDec
  exact (RecordsStage.of_frameK fun hI =>
    RecordsFrame.of_objects_eq (st' := st) hI rfl rfl).trans
    (dispatchSyscallChecked_recordsStage ctx decoded tid e _ st'
      (RecordsArmPremises.of_objects_scheduler_eq (s := st) rfl rfl P) (hR e tid hCur) h)

/-- The nothing-received outcome keeps the records: a placement deschedule where
the pop handed a context back, then the priority-inheritance walk. -/
theorem RecordsFrame.replyRecvNothingReceived (rs : SeLe4n.ThreadId) (c : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (s : SystemState)
    (hInv : s.objects.invExt) :
    RecordsFrame s (_root_.SeLe4n.Kernel.replyRecvNothingReceived rs c ret? s) := by
  unfold _root_.SeLe4n.Kernel.replyRecvNothingReceived
  cases ret? with
  | none => exact RecordsFrame.propagatePipChainCrossCore _ _ _ _ hInv
  | some p =>
    obtain ⟨_, holder⟩ := p
    have P := RecordsFrame.descheduleAtPlacement s holder hInv
    exact P.trans (RecordsFrame.propagatePipChainCrossCore _ _ _ _ P.invExt)

open SeLe4n.Model.SystemState in
/-- **A refused reply-receive keeps the records** (WS-SX SX34): the legs it ran
before it stopped are the success path's prefix -- the reply leg, the pop, the
transfer, the caller's answer, the context return and the receive leg, a records
step on either outcome that keeps the reply-waiter queues -- and the
nothing-received outcome, after the holder's deschedule where the post-receive
donation refused, is a records frame. -/
theorem RecordsStage.replyRecvTransferStoppedState {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage}
    {grant : Bool} {c : CoreId} {st : SystemState}
    (hR : ipcReachable st) (hC : CallerReady st tid) :
    RecordsStage st (_root_.SeLe4n.Kernel.replyRecvTransferStoppedState epId tid rid prevCaller
      label msg grant c st) := by
  have hInv := hR.objects_invExt
  have hQ := hR.ipcInvariantFull.queueHeadBlockedConsistent
  rcases replyRecvTransferStoppedState_cases epId tid rid prevCaller label msg grant c st with
    hE | ⟨hA, e, hB⟩
  · rw [hE]; exact .refl _
  generalize _root_.SeLe4n.Kernel.replyRecvTransferStoppedState epId tid rid prevCaller label
    msg grant c st = s at hB ⊢
  have hAns : replyRecvCallerFaultAnswer? st prevCaller label msg = none →
      NoFaultAt st prevCaller := fun hA x hx => by
    cases hF : x.pendingFault with
    | none => rfl
    | some _ => simp only [replyRecvCallerFaultAnswer?, hx, hF] at hA; cases hA
  revert hB hAns
  generalize replyRecvCallerFaultAnswer? st prevCaller label msg = answer
  generalize replyRecvLegMessage answer msg = m
  intro hB hAns
  rcases endpointReplyRecvAnsweringBodyR_stopped hInv hA hB with
    ⟨-, hS⟩ | ⟨sgi, ret?, popped, hR1, hPop1, hInvP, hTail⟩
  · rw [hS]; exact .refl _
  have A := ReplyLegStep.endpointReplyOnCore (replier := tid) (target := prevCaller) (msg := m)
    (c := c) hInv
  have hB1 := endpointReplyOnCore_preserves_replyWaitersConsistent tid prevCaller m c st hInv
  have hI1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller m c st hInv
  generalize hRl : endpointReplyOnCore tid prevCaller m c st = p at A hB1 hI1 hR1 hPop1 hTail
  obtain ⟨st1, r⟩ := p
  dsimp only at A hB1 hI1 hR1 hPop1 hTail
  subst hR1
  have hX : replyRecvReplyTransfer answer st tid prevCaller grant popped =
      .ok (receiveTransferCapsDone (if answer.isSome = true then none
        else replyCapRequest st tid grant) none (receiverCapTarget? st prevCaller) popped) := by
    rw [replyRecvReplyTransfer_eq_receiveTransferCaps]; exact receiveTransferCaps_eq_done _ _ _ _
  generalize receiveTransferCapsDone (if answer.isSome = true then none
    else replyCapRequest st tid grant) none (receiverCapTarget? st prevCaller) popped = Dn at hX hTail
  obtain ⟨xs, st1p⟩ := Dn
  dsimp only at hTail
  have hPop := hPop1
  obtain ⟨hQp, hRp, hEp⟩ := replyRecvReceiveLegFacts hInv hQ hRl hPop hX hC.ready
  have F0 := RecordsFrame.replyRecvPopDonation A.1.invExt hPop
  have F1 := F0.trans (RecordsFrame.receiveTransferCaps F0.invExt
    (by rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX; exact hX))
  have Ans : RecordsStep st (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) := by
    have := RecordsStep.replyRecvReplyStep (grant := grant) hInv hAns hRl hPop
    rwa [replyRecvReplyStepState_eq_of_ok hPop hX] at this
  have hIp : st1p.objects.invExt := replyRecvReplyTransfer_objects_invExt hInvP hX
  have hBp : st.replyWaitersConsistent → st1p.replyWaitersConsistent := fun h => by
    refine SystemState.replyWaitersConsistent.of_views ?_ (hB1 h)
    have hX' := hX
    rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX'
    rw [receiveTransferCaps_replyViews_eq hInvP hX', replyRecvPopDonation_replyViews_eq hI1 hPop]
  obtain ⟨hQa, hRa, hEa⟩ := replyRecvAnswerCaller_receiveLegFacts answer (st := st) prevCaller tid
    xs.capInfo hIp hQp hRp hEp
  have hIa := replyRecvAnswerCaller_preserves_objects_invExt answer st1p prevCaller xs.capInfo hIp
  have hBa : st.replyWaitersConsistent →
      (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo).replyWaitersConsistent := fun h =>
    SystemState.replyWaitersConsistent.of_views (replyRecvAnswerCaller_replyViews_eq _ _ _ _ hIp)
      (hBp h)
  generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a
    at Ans hQa hRa hEa hIa hBa hTail
  have FR : RecordsFrame st1a (receiveReturnSchedContext true st1a tid) :=
    receiveReturnSchedContext_induct (fun a b => RecordsFrame a b) true st1a tid
      (RecordsFrame.refl Ans.invExt)
      (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS tid Ans.invExt)
  obtain ⟨hQr, hRr, hEpR⟩ := receiveReturnSchedContext_receiveLegFacts true st1a tid hIa hQa hRa
  have hIr := receiveReturnSchedContext_objects_invExt true st1a tid hIa
  have hBr : st.replyWaitersConsistent →
      (receiveReturnSchedContext true st1a tid).replyWaitersConsistent := fun h =>
    SystemState.replyWaitersConsistent.of_views
      (receiveReturnSchedContext_replyViews_eq true st1a tid hIa) (hBa h)
  have S2 := RecordsStep.endpointReceiveDualWithCapsOnCore (endpointId := epId)
    (replyId := some rid) (c := c) FR.invExt hQr (fun x hx => by rw [hRr x hx]; exact ipcParked_ready)
  have St2 : RecordsStage st (_root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore epId tid (some rid) c
      (receiveReturnSchedContext true st1a tid)).1 :=
    RecordsStage.of_step ((Ans.trans (.of_frame FR)).trans S2) fun h =>
      endpointReceiveDualWithCapsOnCore_preserves_replyWaitersConsistent epId tid (some rid) c _
        hIr (hBr h)
        (by
          intro v hv
          obtain ⟨t, hT, rfl⟩ := tcb_of_replyViews hv
          have hS := hRr t ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hT)
          simp only [TCB.replyView, TCB.blockingServer?, hS])
        (by
          intro ep s hE hH
          refine ⟨fun hs => ?_, sendHead_serverFree hQr hE hH⟩
          subst hs
          obtain ⟨tcb, hT, hRd⟩ := hC
          rcases (hQ epId ep s tcb (hEa epId ep (hEpR epId ep hE)) hT).2 hH with hS | hS <;>
            rw [hRd] at hS <;> cases hS)
  have hI2 := _root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore_preserves_objects_invExt epId tid (some rid) c _ hIr
  rcases hTail with hS | ⟨st2, next, summary, sgi', hV, hS⟩
  · rw [hS]; exact St2.trans (.of_frame (RecordsFrame.replyRecvNothingReceived _ _ _ _ hI2))
  rw [hV] at St2 hI2
  rcases hS with hS | ⟨sc, holder, -, hS⟩
  · rw [hS]; exact St2.trans (.of_frame (RecordsFrame.replyRecvNothingReceived _ _ _ _ hI2))
  rw [hS]
  have H := RecordsFrame.replyRecvHolderDeschedule tid holder st2 hI2
  exact St2.trans (.of_frame (H.trans (RecordsFrame.replyRecvNothingReceived _ _ _ _ H.invExt)))

/-- **The ABI dispatch keeps the records**: the argument spill (a register
write, which keeps the premises), then the checked entry, a capability-fault
delivery for the running caller, or a refusal record. -/
theorem syscallDispatchFromAbi_recordsStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (P : RecordsArmPremises st) (hR : CurrentReady st)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    RecordsStage st st' := by
  have hInv := P.deletes.2.1.2.1
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact RecordsStage.refl _
  rename_i tid hCur
  split at h
  · cases h; exact RecordsStage.refl _
  have hW : RecordsStage st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
    unfold Platform.FFI.writeFfiRegistersToTcb
    exact RecordsStage.of_frameK fun hI => RecordsFrame.updateTcb st tid hI fun _ => rfl
  have P1 := P.writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 x6
  have hR1 := hR.writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 x6 hInv
  have hCur1 : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6
      ).scheduler.currentOnCore e = some tid := by
    rw [Platform.FFI.writeFfiRegistersToTcb_scheduler]; exact hCur
  dsimp only at h
  split at h
  · -- WS-SX SX4: a refused receive hands back its busy reply's cancel, which
    -- keeps the records, the endpoint heads and the caller `.ready`.
    rename_i ke hE
    have hInv1 := P1.deletes.2.1.2.1
    have hIpc1 := P1.deletes.2.1.1
    -- WS-SX SX34: a reply-receive's stopped state keeps the records; it raises a
    -- capability fault only where it stopped where it started
    -- (`cancelReceiveBusyReply_cases_of_fault`), so the fault's delivery reads
    -- the endpoint heads and the caller `.ready` on the two cases it always took
    have hS : RecordsStage (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
          (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) := by
      rcases cancelReceiveBusyReply_cases_holder ctx e
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) with
        hEq | ⟨t', hd, hC', hne, hEq⟩ | hA
      · rw [hEq]; exact .refl _
      · rw [hEq]; exact RecordsStage.cancelReplyHolder _ hd e
      · obtain ⟨t, _, _, _, _, _, _, hCt, -, -, hEq⟩ := hA.stopped
        rw [hCur1] at hCt
        cases hCt
        rw [hEq]
        exact RecordsStage.replyRecvTransferStoppedState P1.deletes.1 (hR1 e tid hCur1)
    have hFF : ∀ f, Platform.FFI.syscallCapFaultAt SeLe4n.arm64DefaultLayout
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
          (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) tid ke =
          some f →
        queueHeadBlockedConsistent (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) ∧
        CallerReady (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) tid := by
      intro f hF
      rcases cancelReceiveBusyReply_cases_of_fault hInv1 hCur1 hE hF with
        hEq | ⟨t', hd, hC', hne, hEq⟩ <;> rw [hEq]
      · exact ⟨hIpc1.queueHeadBlockedConsistent, hR1 e tid hCur1⟩
      · rw [hCur1] at hC'; cases hC'
        exact ⟨cancelReplyHolder_queueHeadBlockedConsistent _ hd e hInv1 (.of_ipcInvariantFull hIpc1),
          (hR1 e tid hCur1).cancelReplyHolder hInv1 (Ne.symm hne)⟩
    generalize cancelReceiveBusyReply ctx e
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) = stR at h hS hFF
    split at h
    · split at h
      · -- a dropped fault: the refusal's state and its ledger record
        cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e _ tid x0 _ stR
        rw [hL]
        exact (hW.trans hS).trans (RecordsStage.of_frameK fun hI =>
          RecordsFrame.of_objects_eq hI rfl rfl rfl)
      · rename_i fault hF _
        obtain ⟨hQR, hCR⟩ := hFF fault hF
        cases h
        unfold Platform.FFI.deliverSyscallCapFault
        exact (hW.trans hS).trans (RecordsStage.faultDeliverAfterSpill ctx _ _ _ _ e tid hQR hCR)
    · split at h
      · cases h
        exact (hW.trans hS).trans (RecordsStage.of_frameK fun hI => RecordsFrame.of_objects_eq hI
          ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_objects _ _ _))
          (by
            unfold Platform.FFI.recordSyscallRefusal Architecture.recordErrorOverflow
            split <;> (try split) <;> (try split) <;> rfl)
          (by rw [Platform.FFI.recordSyscallRefusal_machine_eq, Architecture.recordErrorOverflow_machine]))
      · cases h
        exact (hW.trans hS).trans (RecordsStage.of_frameK fun hI => RecordsFrame.of_objects_eq hI
          (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)
          (by
            unfold Platform.FFI.recordSyscallRefusal
            split <;> (try split) <;> rfl)
          (by rw [Platform.FFI.recordSyscallRefusal_machine_eq]))
  · rename_i hE
    cases h
    exact hW.trans (syscallEntryChecked_recordsStage P1 hR1 hE)

/-- **The syscall step keeps the records**: the ABI dispatch, the caller's
return staging, the local scheduling point, the residency settlement, the
activation and the ledger drains. -/
theorem syscallDispatchCrossCoreStep_recordsStage {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st : SystemState} (P : RecordsArmPremises st) (hR : CurrentReady st) :
    RecordsStage st (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st).2 := by
  obtain ⟨outcome, st', hD⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx e syscallId
    x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 st
  rw [syscallDispatchCrossCoreStep_of_ok hD]
  exact (syscallDispatchFromAbi_recordsStage P hR hD).trans
    (RecordsStage.of_frameK fun hI =>
      let F1 := RecordsFrame.stageCallerReturnFor _ _ e outcome hI
      let F2 := F1.trans (RecordsFrame.scheduleLocalSuccessorFrom _ _ e F1.invExt)
      let F3 := F2.trans (RecordsFrame.settleResidencyOnCore _ e F2.invExt)
      let F4 := F3.trans (RecordsFrame.activateThreadOnCore _ e F3.invExt)
      F4.trans (RecordsFrame.clearLedgers _ F4.invExt))

/-- **The syscall entry's committed state keeps the records**: the trap-frame
save, the entry's IPC-buffer words handed to the state, the step, and the
committed state dropping the words.  The dispatch premises and the running
callers are read off the state the step runs from. -/
theorem syscallDispatchEntryState_recordsStage (ctx : LabelingContext) (e : CoreId)
    (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState)
    (P : RecordsArmPremises (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hR : CurrentReady (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n)) :
    RecordsStage st (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2) :=
  ((RecordsStage.of_frameK fun hI =>
    let F := RecordsFrame.saveCapturedSyscallFrame st e frame hI
    F.trans (RecordsFrame.syncUserWords _ bytes n F.invExt)).trans
    (syscallDispatchCrossCoreStep_recordsStage P hR)).trans
    (RecordsStage.of_frameK fun hI => RecordsFrame.clearUserWords _ hI)

/-! ### Every committing entry preserves the records -/

/-- **The timer entry preserves the records.** -/
theorem perCoreTimerTickEntryState_preserves_kernelRecordsSound (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hK : st.kernelRecordsSound) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).kernelRecordsSound :=
  perCoreTimerTickEntryState_recordsStage coreId frame st hK

/-- **The reschedule entry preserves the records.** -/
theorem perCoreRescheduleEntryState_preserves_kernelRecordsSound (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hK : st.kernelRecordsSound) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))).kernelRecordsSound :=
  perCoreRescheduleEntryState_recordsStage coreId frame st hK

/-- **The FP/SIMD entry preserves the records.** -/
theorem fpAccessEntryState_preserves_kernelRecordsSound (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (live : Option FpContext)
    (st : SystemState) (hK : st.kernelRecordsSound) :
    (activateThreadAt (PriorityInheritance.settleResidencyAt (fpAccessEntryStep
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId live).2 coreId) coreId).kernelRecordsSound :=
  fpAccessEntryState_recordsStage coreId frame live st hK

/-- **The interrupt entry preserves the records**, from the reachable state the
step runs from. -/
theorem interruptEntryState_preserves_kernelRecordsSound (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState)
    (hK : st.kernelRecordsSound)
    (hR : ipcReachable (Concurrency.saveCapturedTrapFrameAt st coreId frame)) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))).kernelRecordsSound :=
  interruptEntryState_recordsStage coreId intId frame st hR hK

/-- **The fault entry preserves the records**, from the queue heads and the
running threads of the state the step runs from. -/
theorem faultEntryState_preserves_kernelRecordsSound (lctx : LabelingContext) (coreId : UInt64)
    (frame : Architecture.InFlightContext) (ectx : Architecture.ExceptionContext)
    (w : FaultRegisterWindow) (st : SystemState) (hK : st.kernelRecordsSound)
    (hQ : queueHeadBlockedConsistent (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)))
    (hCR : CurrentReady (Concurrency.saveCapturedTrapFrameAt st coreId (some frame))) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (faultEntryStep lctx (Concurrency.saveCapturedTrapFrameAt st coreId (some frame)) ectx w
          coreId).2 coreId) coreId))).kernelRecordsSound :=
  faultEntryState_recordsStage lctx coreId frame ectx w st hQ hCR hK

/-- **The unknown-syscall entry preserves the records.** -/
theorem unknownSyscallEntryState_preserves_kernelRecordsSound (lctx : LabelingContext)
    (coreId : UInt64) (frame : Architecture.InFlightContext)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (st : SystemState)
    (hK : st.kernelRecordsSound)
    (hQ : queueHeadBlockedConsistent (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)))
    (hCR : CurrentReady (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame))) :
    (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (unknownSyscallEntryStep lctx
        (Concurrency.saveCapturedSyscallFrameAt st coreId (some frame)) ectx w coreId).2
        coreId) coreId))).kernelRecordsSound :=
  unknownSyscallEntryState_recordsStage lctx coreId frame ectx w st hQ hCR hK

/-- **The syscall entry preserves the records**, from the dispatch premises and
the running callers of the state the step runs from. -/
theorem syscallDispatchEntryState_preserves_kernelRecordsSound (ctx : LabelingContext)
    (e : CoreId) (trapped : Architecture.InFlightContext)
    (frame : Option Architecture.InFlightContext) (bytes : ByteArray) (n : Nat)
    (st : SystemState) (hK : st.kernelRecordsSound)
    (P : RecordsArmPremises (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n))
    (hR : CurrentReady (Architecture.IpcBufferRead.syncUserWords
      (Architecture.saveCapturedSyscallFrame st e frame) bytes n)) :
    (Architecture.IpcBufferRead.clearUserWords
      (syscallDispatchCrossCoreBracketedStepWords ctx e trapped
        (Architecture.IpcBufferRead.syncUserWords
          (Architecture.saveCapturedSyscallFrame st e frame) bytes n)).2).kernelRecordsSound :=
  syscallDispatchEntryState_recordsStage ctx e trapped frame bytes n st P hR hK

end SeLe4n.Kernel
