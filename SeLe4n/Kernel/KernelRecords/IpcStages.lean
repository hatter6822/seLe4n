-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcSend
import SeLe4n.Kernel.KernelRecords.IpcReceive
import SeLe4n.Kernel.KernelRecords.IpcCall
import SeLe4n.Kernel.KernelRecords.IpcReply
import SeLe4n.Kernel.KernelRecords.IpcNotification
import SeLe4n.Kernel.KernelRecords.Donation
import SeLe4n.Kernel.IPC.Invariant.Reachability

/-!
# The IPC arms keep the records

WS-ZA ZA6.37.  Each IPC arm the capability dispatch routes is a records step
(`Kernel/KernelRecords/Ipc*.lean`) that leaves the reply-waiter queues to the
queues' own theorems, and those read the reachable state and the running
thread: the thread the dispatch runs is `.ready` in IPC (`CallerReady`), so it
waits on no server and is parked on nothing, and the queue heads it meets wait on
none (`ipcReachable`).  The bound signal's delivery is the one arm whose queue
theorem is stated here: the receiver it wakes is blocked on a receive, so it
waits on no server.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The thread the dispatch runs: a TCB `.ready` in IPC. -/
def CallerReady (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = .ready

namespace CallerReady

theorem notParked {st : SystemState} {t : SeLe4n.ThreadId} (h : CallerReady st t) :
    NotParkedAt st t := fun x hx => by
  obtain ⟨tcb, hT, hR⟩ := h
  have hE := hT.symm.trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hE
  subst hE; rw [hR]; exact ipcParked_ready

theorem serverFree {st : SystemState} {t : SeLe4n.ThreadId} (h : CallerReady st t) :
    ReplyViews.serverFree st.replyViews t := by
  obtain ⟨tcb, hT, hR⟩ := h
  exact serverFree_of_tcb hT (by simp only [TCB.blockingServer?, hR])

end CallerReady

/-- **The bound signal keeps the reply-waiter queues consistent**: the bound
receiver it delivers to is blocked on a receive, so it waits on no server before
the delivery or after; with no bound receiver it is the plain signal. -/
theorem notificationSignalBoundOnCore_preserves_replyWaitersConsistent (nid : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hHead : ∀ n w, st.getNotification? nid = some n → n.waitHead = some w →
      ReplyViews.serverFree st.replyViews w) :
    (notificationSignalBoundOnCore nid badge c st).1.replyWaitersConsistent := by
  unfold notificationSignalBoundOnCore
  split
  · rename_i t epId hB
    obtain ⟨tcb, hT, hR⟩ := boundDeliveryTarget?_some st nid t epId hB
    have hSF : ∀ v, st.replyViews t.toObjId = some v → v.server = none :=
      serverFree_of_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
        (by simp only [TCB.blockingServer?, hR])
    dsimp only
    split
    · exact hC
    · rename_i st1 hRm
      have F := RecordsFrame.endpointQueueRemoveDual hInv hRm
      split
      · exact hC
      · rename_i st2 hS
        have hI2 := storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ F.invExt hS
        have hV2 : st2.replyViews = st.replyViews := by
          rw [replyViews_storeTcbReceiveComplete F.invExt hS, F.replyViews]
          exact ReplyViews.setServer_of_server hSF
        refine SystemState.replyWaitersConsistent.of_views ?_ hC
        rw [SystemState.wakeThread_replyViews_eq _ _ _ hI2 (by rw [hV2]; exact hSF), hV2]
  · exact notificationSignalOnCore_preserves_replyWaitersConsistent nid badge c st hInv hC hHead

namespace RecordsStage

/-- **The checked send keeps the records**, its sender the running thread. -/
theorem endpointSendCrossCoreDispatchChecked {ctx : LabelingContext} {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload} {c : CoreId}
    {st : SystemState} (hR : ipcReachable st) (hC : CallerReady st sender) :
    RecordsStage st (_root_.SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked ctx endpointId
      sender payload c st).1 :=
  RecordsStage.of_step (RecordsStep.endpointSendCrossCoreDispatchChecked hR.objects_invExt
    hR.ipcInvariantFull.queueHeadBlockedConsistent hC.notParked) fun _ => by
    unfold _root_.SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked
    split
    · obtain ⟨tcb, hT, hRd⟩ := hC
      exact endpointSendDualWithCapsOnCore_preserves_replyWaitersConsistent_of_reachable _ _ _ _
        st hR tcb hT hRd
    · exact hR.replyWaitersConsistent

/-- **The receive keeps the records**, its receiver the running thread.  It
reads the endpoint heads blocked and nothing else of the IPC bundle: the head
it wakes is a sender, which neither is the receiver nor waits on a reply. -/
theorem endpointReceiveDualWithCapsOnCore {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hC : CallerReady st receiver) :
    RecordsStage st (_root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore endpointId receiver
      replyId c st).1 :=
  RecordsStage.of_step (RecordsStep.endpointReceiveDualWithCapsOnCore hInv hQ hC.notParked)
    fun hRW =>
    let ⟨tcb, hT, hRd⟩ := hC
    endpointReceiveDualWithCapsOnCore_preserves_replyWaitersConsistent _ _ _ _ st hInv hRW
      (serverFree_of_tcb hT (by simp only [TCB.blockingServer?, hRd]))
      (fun ep s hE hH => ⟨fun h => (by
          subst h
          rcases (hQ _ ep _ tcb hE hT).2 hH with h | h <;> rw [hRd] at h <;> cases h),
        sendHead_serverFree hQ hE hH⟩)

/-- **The checked call keeps the records**, its caller the running thread. -/
theorem endpointCallCrossCoreDispatchChecked {ctx : LabelingContext} {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload} {c : CoreId}
    {st : SystemState} (hR : ipcReachable st) (hC : CallerReady st caller) :
    RecordsStage st (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatchChecked ctx endpointId
      caller payload c st).1 :=
  RecordsStage.of_step (RecordsStep.endpointCallCrossCoreDispatchChecked hR.objects_invExt
    hR.ipcInvariantFull.queueHeadBlockedConsistent) fun _ => by
    unfold _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatchChecked
    split
    · obtain ⟨tcb, hT, hRd⟩ := hC
      exact endpointCallCrossCoreDispatch_preserves_replyWaitersConsistent_of_reachable _ _ _ _
        st hR tcb hT hRd
    · exact hR.replyWaitersConsistent

/-- **The checked reply keeps the records**: the fault reply, or the reply and
the delivered frame. -/
theorem replyTransferOnCoreChecked {ctx : LabelingContext} {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState}
    (h : _root_.SeLe4n.Kernel.replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c
      st = .ok ((), st')) : RecordsStage st st' := fun hK =>
  have hI := KernelRecords.objects_invExt hK
  RecordsStage.of_step (RecordsStep.replyTransferOnCoreChecked hI h) (fun hC => by
    unfold _root_.SeLe4n.Kernel.replyTransferOnCoreChecked at h
    split at h
    · have hW := faultReplyOnCore_preserves_replyWaitersConsistent replier callerTid mi regs c st
        hI hC
      revert h hW
      generalize faultReplyOnCore replier callerTid mi regs c st = r
      obtain ⟨s, res⟩ := r
      cases res with
      | error _ => intro h; cases h
      | ok _ => intro h hW; cases h; exact hW
    · have hW : (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier callerTid
          msg c st).1.replyWaitersConsistent ∧ (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked
          ctx replier callerTid msg c st).1.objects.invExt :=
        ⟨by unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked
            split
            · exact endpointReplyCrossCoreDispatch_preserves_replyWaitersConsistent _ _ _ _ st hI hC
            · exact hC,
         (ReplyLegStep.endpointReplyCrossCoreDispatchChecked (ctx := ctx) (replier := replier)
            (target := callerTid) (msg := msg) (c := c) hI).1.invExt⟩
      revert h hW
      generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier callerTid
        msg c st = r
      obtain ⟨s, res⟩ := r
      cases res with
      | error _ => intro h; cases h
      | ok _ =>
        intro h hW
        simp only [] at h
        cases hU : _root_.SeLe4n.Kernel.replyTransferCaps st replier callerTid grant s with
        | error _ => rw [hU] at h; cases h
        | ok p =>
          obtain ⟨summary, sX⟩ := p
          rw [hU] at h
          cases h
          have hX := receiveTransferCaps_objects_invExt hW.2 hU
          exact (hW.1.of_views (receiveTransferCaps_replyViews_eq hW.2 hU)).of_views
            (stageDeliveredMessage_replyViews_eq _ _ _ hX)) hK

/-- **The bound signal keeps the records**: the interrupt's delivery. -/
theorem notificationSignalBoundOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hR : ipcReachable st) :
    RecordsStage st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st).1 :=
  RecordsStage.of_step (RecordsStep.notificationSignalBoundOnCore hR.objects_invExt
    hR.notificationWaiterConsistent) fun _ =>
    notificationSignalBoundOnCore_preserves_replyWaitersConsistent nid badge c st
      hR.objects_invExt hR.replyWaitersConsistent
      (fun _ _ hG hH => notificationHead_serverFree hR.notificationWaiterConsistent hG hH)

/-- **The checked bound signal keeps the records.** -/
theorem notificationSignalBoundCrossCoreDispatchChecked {ctx : LabelingContext}
    {nid : SeLe4n.ObjId} {signaler : SeLe4n.ThreadId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hR : ipcReachable st) :
    RecordsStage st (_root_.SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked ctx nid
      signaler badge c st).1 :=
  RecordsStage.of_step (RecordsStep.notificationSignalBoundCrossCoreDispatchChecked
    hR.objects_invExt hR.notificationWaiterConsistent) fun _ => by
    have hB := notificationSignalBoundOnCore_preserves_replyWaitersConsistent nid badge c st
      hR.objects_invExt hR.replyWaitersConsistent
      (fun _ _ hG hH => notificationHead_serverFree hR.notificationWaiterConsistent hG hH)
    unfold _root_.SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked
    repeat' split
    all_goals first | exact hB | exact hR.replyWaitersConsistent

/-- **The checked wait keeps the records**, its waiter the running thread. -/
theorem notificationWaitCrossCoreDispatchChecked {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {waiter : SeLe4n.ThreadId} {c : CoreId} {st : SystemState} (hR : ipcReachable st)
    (hC : CallerReady st waiter) :
    RecordsStage st (_root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked ctx nid waiter
      c st).1 :=
  RecordsStage.of_step (RecordsStep.notificationWaitCrossCoreDispatchChecked hR.objects_invExt
    hC.notParked) fun _ => by
    unfold _root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked
    split
    · split
      · exact hR.replyWaitersConsistent
      · exact notificationWaitOnCore_preserves_replyWaitersConsistent nid waiter c st
          hR.objects_invExt hR.replyWaitersConsistent hC.serverFree
    · exact hR.replyWaitersConsistent

/-- **The declassified signal keeps the records**: the bound signal, then the
audit ledger's hops. -/
theorem notificationSignalDeclassifiedOnCore {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hR : ipcReachable st) :
    RecordsStage st (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore ctx declPolicy nid
      badge c st).1 :=
  RecordsStage.of_step (RecordsStep.notificationSignalDeclassifiedOnCore hR.objects_invExt
    hR.notificationWaiterConsistent) fun _ => by
    have hB := notificationSignalBoundOnCore_preserves_replyWaitersConsistent nid badge c st
      hR.objects_invExt hR.replyWaitersConsistent
      (fun _ _ hG hH => notificationHead_serverFree hR.notificationWaiterConsistent hG hH)
    have S := RecordsStep.notificationSignalBoundOnCore (badge := badge) (c := c)
      hR.objects_invExt hR.notificationWaiterConsistent (nid := nid)
    unfold _root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore
    generalize _root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st = r at S hB
    obtain ⟨st1, res⟩ := r
    cases res <;> dsimp only at S hB ⊢ <;> repeat' split
    all_goals first
      | exact hR.replyWaitersConsistent
      | (rename_i hRec
         have hEq := recordDeclassifiedHops_frame _ _ _ _ _ hRec
         exact hB.of_views (RecordsFrame.of_objects_eq S.invExt (by rw [hEq]) (by rw [hEq])
           (by rw [hEq])).replyViews)

end RecordsStage

end SeLe4n.Kernel
