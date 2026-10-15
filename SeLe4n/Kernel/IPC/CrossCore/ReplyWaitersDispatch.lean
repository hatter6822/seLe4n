-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersCancellation
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInvariant
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.IPC.CrossCore.EndpointSendInvariant
import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant

/-!
# The IPC arms keep the reply-waiter queues consistent (WS-ZA ZA4.6)

The composite arms the syscall dispatcher runs — call with capability transfer,
donation and priority propagation; reply with the donation return; reply-receive;
fault delivery and the fault reply — are built from the primitive legs whose
reply-view effect `ReplyWaitersPreservation` and `ReplyWaitersCancellation`
state.  Every other step of these arms (the capability unwrap, the donation push
and return, the replenishment migration, the priority walks, the return-frame
stagers, the fault record) writes no reply-view field, so it keeps the views
and the invariant rides through it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  Steps that keep the views
-- ============================================================================

/-- Views agree when every thread's view does. -/
theorem replyViews_eq_of_getTcb_map {st st' : SystemState}
    (h : ∀ tid, (st'.getTcb? tid).map TCB.replyView = (st.getTcb? tid).map TCB.replyView) :
    st'.replyViews = st.replyViews := by
  funext k
  have hk := h (SeLe4n.ThreadId.ofObjId k)
  unfold SystemState.getTcb? at hk
  rw [SeLe4n.ThreadId.toObjId_ofObjId] at hk
  unfold replyViews getObject?
  revert hk
  cases st'.objects[k]? with
  | none => cases st.objects[k]? with
    | none => intro _; rfl
    | some o => cases o <;> simp [objReplyView]
  | some o' => cases o' <;> cases st.objects[k]? <;>
      (try rename_i o; try cases o) <;> simp [objReplyView]

/-- A TCB update that keeps every reply-view field keeps the views. -/
theorem replyViews_updateTcb_eq (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).replyView = x.replyView) :
    (st.updateTcb t f).replyViews = st.replyViews := by
  cases hT : st.getTcb? t with
  | none =>
    unfold SystemState.updateTcb; rw [SystemState.getTcbWitnessed?_eq_none hT]
  | some tcb =>
    unfold SystemState.updateTcb; rw [SystemState.getTcbWitnessed?_eq_some hT]
    have hO := (getTcb?_eq_some_iff st t tcb).1 hT
    funext x
    rw [replyViews_rewriteObject _ _ _ _ hInv]
    split
    · rename_i hx; subst hx
      rw [replyViews_of_tcb hO, objReplyView_tcb, hf]
    · rfl

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId)

theorem recordPhysicalWrites_replyViews_eq (st : SystemState) (ws : List Architecture.PhysicalWrite) :
    (Architecture.recordPhysicalWrites st ws).replyViews = st.replyViews := rfl

theorem writeReturnFrameToTcb_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId)
    (fr : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    (Architecture.writeReturnFrameToTcb st t fr).replyViews = st.replyViews :=
  replyViews_updateTcb_eq st t hInv (fun _ => rfl)

theorem writeDeliveredFrameToTcb_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId)
    (fr : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    (Architecture.writeDeliveredFrameToTcb st t fr).replyViews = st.replyViews :=
  replyViews_updateTcb_eq st t hInv (fun _ => rfl)

theorem stageDeliveredMessage_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId) (n : Nat)
    (hInv : st.objects.invExt) :
    (Architecture.stageDeliveredMessage st t n).replyViews = st.replyViews := by
  unfold Architecture.stageDeliveredMessage
  split
  · split
    · split
      · rw [recordPhysicalWrites_replyViews_eq, writeDeliveredFrameToTcb_replyViews_eq _ _ _ hInv]
      · rfl
    · rfl
  · rfl

theorem stageWokenDelivery_replyViews_eq (st : SystemState) (w? : Option SeLe4n.ThreadId)
    (n : Nat) (hInv : st.objects.invExt) :
    (Architecture.stageWokenDelivery st w? n).replyViews = st.replyViews := by
  unfold Architecture.stageWokenDelivery
  split
  · exact stageDeliveredMessage_replyViews_eq _ _ _ hInv
  · rfl

theorem stageWokenSendCompletion_replyViews_eq (st : SystemState) (w? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (Architecture.stageWokenSendCompletion st w?).replyViews = st.replyViews := by
  unfold Architecture.stageWokenSendCompletion
  split
  · rfl
  · split
    · split
      · exact writeReturnFrameToTcb_replyViews_eq _ _ _ hInv
      · rfl
    · rfl

theorem recordPendingFault_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId)
    (tf : ThreadFault) (hInv : st.objects.invExt) :
    (recordPendingFault st t tf).replyViews = st.replyViews :=
  replyViews_updateTcb_eq st t hInv (fun _ => rfl)

theorem applyFaultRestart_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId)
    (fr : Architecture.FaultRestartFrame) (hInv : st.objects.invExt) :
    (applyFaultRestart st t fr).replyViews = st.replyViews :=
  replyViews_updateTcb_eq st t hInv (fun _ => rfl)

theorem faultSuspendOnCore_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : (faultSuspendOnCore st t c).replyViews = st.replyViews := by
  have h := replyViews_updateTcb_eq (removeRunnableOnCore st t c) t
    (f := fun tcb => { tcb with threadState := .Inactive })
    (removeRunnableOnCore_objects_invExt _ _ _ hInv) (fun _ => rfl)
  unfold faultSuspendOnCore
  rw [h, removeRunnableOnCore_replyViews_eq]

theorem faultAbandonOnCore_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : (faultAbandonOnCore st t c).replyViews = st.replyViews := by
  have h := replyViews_updateTcb_eq (removeRunnableOnCore st t c) t
    (f := fun tcb => { tcb with threadState := .Inactive, pendingFault := none })
    (removeRunnableOnCore_objects_invExt _ _ _ hInv) (fun _ => rfl)
  unfold faultAbandonOnCore
  rw [h, removeRunnableOnCore_replyViews_eq]

/-- The capability unwrap writes CNodes alone. -/
theorem ipcUnwrapCaps_replyViews_eq (msg : IpcMessage) (root : SeLe4n.ObjId)
    (base : SeLe4n.Slot) (grant : Bool) {st st' : SystemState} {sum : CapTransferSummary}
    (hInv : st.objects.invExt) (h : ipcUnwrapCaps msg root base grant st = .ok (sum, st')) :
    st'.replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun k t0 hk => ⟨t0, ipcUnwrapCaps_preserves_tcb_objects msg root base grant st st' sum
      k t0 hk hInv h, rfl⟩)
    (fun k t' hk => ⟨t', ipcUnwrapCaps_tcb_backward msg root base grant st st' sum k t'
      hInv h hk⟩)

/-- The rendezvous capability lookup reads the sender's CSpace and writes the
receiver's CNodes alone. -/
theorem receiveTransferCaps_replyViews_eq
    {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)} {root : SeLe4n.ObjId}
    {base : SeLe4n.Slot} {st st' : SystemState} {sum : CapTransferSummary}
    (hInv : st.objects.invExt) (h : receiveTransferCaps req root base st = .ok (sum, st')) :
    st'.replyViews = st.replyViews := by
  obtain ⟨stR, _, hO, _, _, hOr⟩ := receiveTransferCaps_frame h
  have hR : stR.replyViews = st.replyViews := by
    funext k; unfold SystemState.replyViews SystemState.getObject?; rw [hO]
  rcases hOr with rfl | hU
  · exact hR
  · exact (ipcUnwrapCaps_replyViews_eq _ _ _ _ (hO ▸ hInv) hU).trans hR

-- ============================================================================
-- §2  The donation steps keep the views
-- ============================================================================

/-- The donation push rewrites scheduling-context bindings, scheduling contexts
and reply frames: no reply-view field. -/
theorem donateSchedContext_replyViews_eq {st st' : SystemState}
    {client server : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    (hInv : st.objects.invExt) (h : donateSchedContext st client server scId = .ok st') :
    st'.replyViews = st.replyViews :=
  replyViews_eq_of_getTcb_map
    (donateSchedContext_getTcb?_map_eq TCB.replyView (fun _ _ => rfl) st st' client server
      scId hInv h)

theorem applyCallDonation_replyViews_eq {st st' : SystemState}
    {c r : SeLe4n.ValidThreadId} (hInv : st.objects.invExt)
    (h : applyCallDonation st c r = .ok st') : st'.replyViews = st.replyViews := by
  rw [applyCallDonation_characterisation] at h
  split at h
  · exact donateSchedContext_replyViews_eq hInv h
  · cases h; rfl

theorem applyCallDonationOnCore_replyViews_eq {st st' : SystemState}
    {c r : SeLe4n.ValidThreadId} {a b : CoreId} (hInv : st.objects.invExt)
    (h : applyCallDonationOnCore st c r a b = .ok st') : st'.replyViews = st.replyViews := by
  obtain ⟨s1, h1, hOr⟩ := applyCallDonationOnCore_ok_decompose st st' c r a b h
  have hV := applyCallDonation_replyViews_eq hInv h1
  rcases hOr with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
  · exact hV
  · rw [migrateSchedContextReplenishment_replyViews_eq, hV]

theorem applyRendezvousCallDonation_replyViews_eq {st st' : SystemState}
    {r d : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : applyRendezvousCallDonation st r d = .ok st') : st'.replyViews = st.replyViews := by
  unfold applyRendezvousCallDonation at h
  split at h
  · exact applyCallDonationOnCore_replyViews_eq hInv h
  · cases h

theorem applyReceiveRendezvousDonation_replyViews_eq {st st' : SystemState}
    {r d : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : applyReceiveRendezvousDonation st r d = .ok st') : st'.replyViews = st.replyViews := by
  unfold applyReceiveRendezvousDonation at h
  split at h
  · exact applyRendezvousCallDonation_replyViews_eq hInv h
  · cases h; rfl

theorem applyReceiverPipHandoff_replyViews_eq (st : SystemState) (r : SeLe4n.ThreadId)
    (c : CoreId) (hInv : st.objects.invExt) :
    (applyReceiverPipHandoff st r c).replyViews = st.replyViews :=
  propagatePipChainCrossCore_replyViews_eq _ _ _ _ hInv

theorem applyReceiveRendezvousHandoff_replyViews_eq {st st' : SystemState}
    {r d : SeLe4n.ThreadId} {c : CoreId} (hInv : st.objects.invExt)
    (h : applyReceiveRendezvousHandoff st r d c = .ok st') : st'.replyViews = st.replyViews := by
  unfold applyReceiveRendezvousHandoff at h
  split at h
  · cases h
  · rename_i s1 h1
    cases h
    have hV := applyReceiveRendezvousDonation_replyViews_eq hInv h1
    have hI1 : s1.objects.invExt := by
      unfold applyReceiveRendezvousDonation at h1
      split at h1
      · exact applyRendezvousCallDonation_preserves_objects_invExt _ _ _ _ hInv h1
      · cases h1; exact hInv
    split
    · rw [applyReceiverPipHandoff_replyViews_eq _ _ _ hI1, hV]
    · exact hV

theorem applyReceiveLegPipHandoff_replyViews_eq (st : SystemState) (r d w : SeLe4n.ThreadId)
    (c : CoreId) (hInv : st.objects.invExt) :
    (applyReceiveLegPipHandoff st r d w c).replyViews = st.replyViews := by
  unfold applyReceiveLegPipHandoff
  split
  · rfl
  · split
    · exact applyReceiverPipHandoff_replyViews_eq _ _ _ hInv
    · rfl

/-- The reply path's donation return: the context goes back, its replenishments
migrate, the holder is descheduled — no reply-view field. -/
theorem applyReplyDonationOnCore_replyViews_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {t : SeLe4n.ValidThreadId} {a b : CoreId} (hInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid t a b = .ok st') : st'.replyViews = st.replyViews := by
  unfold applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · cases h
      · rename_i s1 h1
        cases h
        rw [descheduleAtPlacement_replyViews_eq, migrateSchedContextReplenishment_replyViews_eq,
          returnDonatedSchedContextResolved_replyViews_eq hInv h1]
    · cases h

-- ============================================================================
-- §3  The arms
-- ============================================================================

/-- **The live receive keeps the reply-waiter queues consistent**: the bare
receive links a dequeued caller to the receiver, and the capability unwrap
after it writes CNodes alone. -/
theorem endpointReceiveDualWithCapsOnCore_preserves_replyWaitersConsistent
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (root : SeLe4n.ObjId) (base : SeLe4n.Slot) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hRecv : ReplyViews.serverFree st.replyViews receiver)
    (hHead : ∀ ep s, st.objects[endpointId]? = some (.endpoint ep) → ep.sendQ.head = some s →
      s ≠ receiver ∧ ReplyViews.serverFree st.replyViews s) :
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId root base c
      st).1.replyWaitersConsistent := by
  have hB := endpointReceiveDualOnCore_preserves_replyWaitersConsistent endpointId receiver
    replyId c st hInv hC hRecv hHead
  have hI := endpointReceiveDualOnCore_preserves_objects_invExt endpointId receiver replyId c st hInv
  unfold endpointReceiveDualWithCapsOnCore
  cases hR : endpointReceiveDualOnCore endpointId receiver replyId c st with
  | mk s1 res =>
    rw [hR] at hB hI
    cases res with
    | error e => exact hB
    | ok v =>
      obtain ⟨sid, sgi⟩ := v
      dsimp only
      repeat' split
      all_goals first
        | exact hB
        | (rename_i hU; exact replyWaitersConsistent.of_views
            (receiveTransferCaps_replyViews_eq hI hU) hB)

theorem endpointCallWithCapsOnCore_preserves_replyWaitersConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hCaller : ReplyViews.serverFree st.replyViews caller)
    (hHead : ∀ ep r, st.objects[endpointId]? = some (.endpoint ep) → ep.receiveQ.head = some r →
      r ≠ caller ∧ ReplyViews.serverFree st.replyViews r) :
    (endpointCallWithCapsOnCore endpointId caller msg rights base c
      st).1.replyWaitersConsistent := by
  have hB := endpointCallOnCore_preserves_replyWaitersConsistent endpointId caller
    { msg with capsGranted := rights.mem .grant } c st hInv hC hCaller hHead
  have hI := endpointCallOnCore_preserves_objects_invExt endpointId caller
    { msg with capsGranted := rights.mem .grant } c st hInv
  unfold endpointCallWithCapsOnCore
  cases hR : endpointCallOnCore endpointId caller { msg with capsGranted := rights.mem .grant } c st with
  | mk s1 res =>
    rw [hR] at hB hI
    cases res with
    | error e => exact hB
    | ok sgi =>
      dsimp only
      repeat' split
      all_goals first
        | exact hB
        | (rename_i hU; exact replyWaitersConsistent.of_views
            (ipcUnwrapCaps_replyViews_eq _ _ _ _ hI hU) hB)

/-- **The live call keeps the reply-waiter queues consistent**: the call links
the caller to the receiver it rendezvoused with; the donation and the priority
walk after it keep the views. -/
theorem endpointCallCrossCoreDispatch_preserves_replyWaitersConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hCaller : ReplyViews.serverFree st.replyViews caller)
    (hHead : ∀ ep r, st.objects[endpointId]? = some (.endpoint ep) → ep.receiveQ.head = some r →
      r ≠ caller ∧ ReplyViews.serverFree st.replyViews r) :
    (endpointCallCrossCoreDispatch endpointId caller msg rights base c
      st).1.replyWaitersConsistent := by
  have hB := endpointCallWithCapsOnCore_preserves_replyWaitersConsistent endpointId caller msg
    rights base c st hInv hC hCaller hHead
  have hI := endpointCallWithCapsOnCore_preserves_objects_invExt endpointId caller msg rights
    base c st hInv
  unfold endpointCallCrossCoreDispatch
  cases hR : endpointCallWithCapsOnCore endpointId caller msg rights base c st with
  | mk s1 res =>
    rw [hR] at hB hI
    cases res with
    | error e => exact hB
    | ok v =>
      dsimp only
      repeat' split
      all_goals first
        | exact hB
        | (rename_i hD
           exact replyWaitersConsistent.of_views
            ((propagatePipChainCrossCore_replyViews_eq _ _ _ _
              (applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hI hD)).trans
              (applyCallDonationOnCore_replyViews_eq hI hD)) hB)

/-- **The live reply keeps the reply-waiter queues consistent**: the reply
unlinks the answered caller; the donation return and the priority reversion
after it keep the views. -/
theorem endpointReplyCrossCoreDispatch_preserves_replyWaitersConsistent
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent) :
    (endpointReplyCrossCoreDispatch replier target msg c st).1.replyWaitersConsistent := by
  have hB := endpointReplyOnCore_preserves_replyWaitersConsistent replier target msg c st hInv hC
  have hI := endpointReplyOnCore_preserves_objects_invExt replier target msg c st hInv
  unfold endpointReplyCrossCoreDispatch
  cases hR : endpointReplyOnCore replier target msg c st with
  | mk s1 res =>
    rw [hR] at hB hI
    cases res with
    | error e => exact hC
    | ok v =>
      dsimp only
      repeat' split
      all_goals first
        | exact hC
        | exact replyWaitersConsistent.of_views
            (propagatePipChainCrossCore_replyViews_eq _ _ _ _ hI) hB
        | (rename_i hD
           exact replyWaitersConsistent.of_views
            ((propagatePipChainCrossCore_replyViews_eq _ _ _ _
              (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hI hD)).trans
              (applyReplyDonationOnCore_replyViews_eq hI hD)) hB)

/-- **Fault delivery keeps the reply-waiter queues consistent**: it is the live
call on the handler's endpoint, or the fail-closed suspend; the fault record and
the woken handler's return frame keep the views. -/
theorem faultDeliverOnCore_preserves_replyWaitersConsistent (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hFaulted : ReplyViews.serverFree st.replyViews tid)
    (hHead : ∀ (eid : SeLe4n.ObjId) (ep : Endpoint) (r : SeLe4n.ThreadId),
      st.objects[eid]? = some (.endpoint ep) → ep.receiveQ.head = some r →
      r ≠ tid ∧ ReplyViews.serverFree st.replyViews r) :
    (faultDeliverOnCore st tid f ctx c).1.replyWaitersConsistent := by
  have hSus : (recordPendingFault (faultSuspendOnCore st tid c) tid
      { fault := f, context := ctx }).replyWaitersConsistent :=
    replyWaitersConsistent.of_views
      ((recordPendingFault_replyViews_eq _ _ _ (faultSuspendOnCore_preserves_objects_invExt
        _ _ _ hInv)).trans (faultSuspendOnCore_replyViews_eq _ _ _ hInv)) hC
  unfold faultDeliverOnCore
  dsimp only
  split
  · exact hSus
  · rename_i tgt _
    have hB := endpointCallCrossCoreDispatch_preserves_replyWaitersConsistent tgt.endpoint tid
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0) c st hInv hC
      hFaulted (hHead tgt.endpoint)
    have hI := endpointCallCrossCoreDispatch_preserves_objects_invExt tgt.endpoint tid
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0) c st hInv
    cases hR : endpointCallCrossCoreDispatch tgt.endpoint tid (faultMessage f ctx tgt.cap.badge)
        tgt.cap.rights (SeLe4n.Slot.ofNat 0) c st with
    | mk s1 res =>
      rw [hR] at hB hI
      cases res with
      | error e => exact hSus
      | ok v =>
        dsimp only
        refine replyWaitersConsistent.of_views ?_ hB
        rw [recordPendingFault_replyViews_eq _ _ _
          (stageWokenDelivery_preserves_objects_invExt _ _ _ hI),
          stageWokenDelivery_replyViews_eq _ _ _ hI]

theorem faultReplyApplyOnCore_replyViews_eq (st : SystemState) (t : SeLe4n.ThreadId)
    (o : Architecture.FaultReplyOutcome) (hInv : st.objects.invExt) :
    (faultReplyApplyOnCore st t o).replyViews = st.replyViews := by
  unfold faultReplyApplyOnCore
  split
  · exact applyFaultRestart_replyViews_eq _ _ _ hInv
  · exact faultAbandonOnCore_replyViews_eq _ _ _ hInv

/-- **The fault reply keeps the reply-waiter queues consistent**: it is the live
reply, then the restart or abandon of the faulted thread. -/
theorem faultReplyOnCore_preserves_replyWaitersConsistent (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent) :
    (faultReplyOnCore replier faulted mi regs c st).1.replyWaitersConsistent := by
  unfold faultReplyOnCore
  split
  · exact hC
  · split
    · exact hC
    · dsimp only
      have hB := endpointReplyCrossCoreDispatch_preserves_replyWaitersConsistent replier faulted
        IpcMessage.empty c st hInv hC
      have hI := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier faulted
        IpcMessage.empty c st hInv
      cases hR : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st with
      | mk s1 res =>
        rw [hR] at hB hI
        cases res with
        | error e => exact hC
        | ok v =>
          dsimp only
          exact replyWaitersConsistent.of_views (faultReplyApplyOnCore_replyViews_eq _ _ _ hI) hB

theorem replyRecvPopDonation_replyViews_eq {rid : SeLe4n.ReplyId} {t : SeLe4n.ThreadId}
    {st st' : SystemState} {ret : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt) (h : replyRecvPopDonation rid t st = .ok (ret, st')) :
    st'.replyViews = st.replyViews := by
  unfold replyRecvPopDonation at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i s1 h1
        cases h
        rw [migrateSchedContextReplenishment_replyViews_eq,
          returnDonatedSchedContextResolved_replyViews_eq hInv h1]
    · cases h
  · cases h; rfl

theorem replyRecvHolderDeschedule_replyViews_eq (t h : SeLe4n.ThreadId) (st : SystemState) :
    (replyRecvHolderDeschedule t h st).replyViews = st.replyViews := by
  unfold replyRecvHolderDeschedule
  split
  · rfl
  · exact descheduleAtPlacement_replyViews_eq _ _

theorem replyRecvHolderDeschedule_objects_invExt (t h : SeLe4n.ThreadId) (st : SystemState)
    (hInv : st.objects.invExt) : (replyRecvHolderDeschedule t h st).objects.invExt := by
  unfold replyRecvHolderDeschedule
  split
  · exact hInv
  · exact descheduleAtPlacement_preserves_objects_invExt _ _ hInv

theorem replyRecvPostReceiveDonation_replyViews_eq {t srv nxt : SeLe4n.ThreadId} {c : CoreId}
    {ret : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation t srv nxt c ret st = .ok ((), st')) :
    st'.replyViews = st.replyViews := by
  unfold replyRecvPostReceiveDonation at h
  split at h
  · cases h; exact propagatePipChainCrossCore_replyViews_eq _ _ _ _ hInv
  · split at h
    · split at h
      · cases h
      · rename_i holder _ _ _ hD
        cases h
        have hI := replyRecvHolderDeschedule_objects_invExt t holder st hInv
        rw [propagatePipChainCrossCore_replyViews_eq _ _ _ _
          (applyRendezvousCallDonation_preserves_objects_invExt _ _ _ _ hI hD),
          applyRendezvousCallDonation_replyViews_eq hI hD,
          replyRecvHolderDeschedule_replyViews_eq]
    · cases h
      rw [propagatePipChainCrossCore_replyViews_eq _ _ _ _
        (descheduleAtPlacement_preserves_objects_invExt _ _ hInv),
        descheduleAtPlacement_replyViews_eq]

/-- **The live reply-receive keeps the reply-waiter queues consistent**: the
reply leg unlinks the answered caller, the receive leg links the next caller to
the server, and every step between and after them (the donation pop, the
capability unwrap, the post-receive donation, the priority hand-off, the
return-frame stagers) keeps the views.

The receive leg's two facts are stated at the state it runs on, the reply leg's
commit with the donation pop applied (`replyRecvPostPopState`), as the arm's
other composite theorems state theirs. -/
theorem endpointReplyRecvOnCore_preserves_replyWaitersConsistent
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (root : SeLe4n.ObjId)
    (base : SeLe4n.Slot) (ec : CoreId) (st stOut : SystemState) (summary : CapTransferSummary)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hRecv1 : ReplyViews.serverFree (replyRecvPostPopState rid prevCaller
      (endpointReplyOnCore tid prevCaller msg ec st).1).replyViews tid)
    (hHead1 : ∀ ep s, (replyRecvPostPopState rid prevCaller
        (endpointReplyOnCore tid prevCaller msg ec st).1).objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head = some s → s ≠ tid ∧ ReplyViews.serverFree (replyRecvPostPopState rid
        prevCaller (endpointReplyOnCore tid prevCaller msg ec st).1).replyViews s)
    (h : endpointReplyRecvOnCore epId tid rid prevCaller msg root base ec st
      = .ok (summary, stOut)) :
    stOut.replyWaitersConsistent := by
  have hB1 := endpointReplyOnCore_preserves_replyWaitersConsistent tid prevCaller msg ec st hInv hC
  have hI1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg ec st hInv
  unfold endpointReplyRecvOnCore at h
  dsimp only at h
  cases hR : endpointReplyOnCore tid prevCaller msg ec st with
  | mk st1 res1 =>
    rw [hR] at h hB1 hI1 hRecv1 hHead1
    cases res1 with
    | error e => cases h
    | ok u =>
      dsimp only at h
      split at h
      · cases h
      · rename_i ret st1p hP
        have hEq : replyRecvPostPopState rid prevCaller st1 = st1p := by
          unfold replyRecvPostPopState; rw [hP]
        rw [hEq] at hRecv1 hHead1
        have hIp := replyRecvPopDonation_preserves_objects_invExt rid prevCaller st1 st1p ret hI1 hP
        have hBp : st1p.replyWaitersConsistent :=
          replyWaitersConsistent.of_views (replyRecvPopDonation_replyViews_eq hI1 hP) hB1
        have hB2 := endpointReceiveDualWithCapsOnCore_preserves_replyWaitersConsistent epId tid
          (some rid) root base ec st1p hIp hBp hRecv1 hHead1
        have hI2 := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt epId tid
          (some rid) root base ec st1p hIp
        split at h
        · cases h
        · rename_i st2 nxt sum2 sgi2 hW
          rw [hW] at hB2 hI2
          split at h
          · cases h
          · rename_i st3 hD
            cases h
            have hI3 := replyRecvPostReceiveDonation_preserves_objects_invExt _ _ _ _ _ _ _ _ hI2 hD
            have hI4 := applyReceiveLegPipHandoff_preserves_objects_invExt st3 tid nxt
              ((recordedReplyServer? st prevCaller).getD tid) ec hI3
            refine replyWaitersConsistent.of_views ?_ hB2
            rw [stageWokenSendCompletion_replyViews_eq _ _
                (stageDeliveredMessage_preserves_objects_invExt _ _ _ hI4),
              stageDeliveredMessage_replyViews_eq _ _ _ hI4,
              applyReceiveLegPipHandoff_replyViews_eq _ _ _ _ _ hI3,
              replyRecvPostReceiveDonation_replyViews_eq hI2 hD]

-- ============================================================================
-- §4  Send: a woken receiver and a blocked sender wait on no server
-- ============================================================================

theorem replyViews_storeTcbReceiveComplete {st st' : SystemState} {t : SeLe4n.ThreadId}
    {m : Option IpcMessage} (hInv : st.objects.invExt) (h : storeTcbReceiveComplete st t m = .ok st') :
    st'.replyViews = ReplyViews.setServer st.replyViews t none :=
  replyViews_modifyTcb hInv h (fun _ => rfl)

/-- **Send keeps the reply-waiter queues consistent**: the receiver it wakes
was blocked on a receive and the sender it blocks was running, so neither waits
on a server before or after. -/
theorem endpointSendDualOnCore_preserves_replyWaitersConsistent (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hSender : ReplyViews.serverFree st.replyViews sender)
    (hHead : ∀ ep r, st.objects[endpointId]? = some (.endpoint ep) → ep.receiveQ.head = some r →
      ReplyViews.serverFree st.replyViews r) :
    (endpointSendDualOnCore endpointId sender msg c st).1.replyWaitersConsistent := by
  unfold endpointSendDualOnCore
  split
  · exact hC
  split
  · exact hC
  split
  · rename_i ep hEp
    have hObj := (getEndpoint?_eq_some_iff st endpointId ep).1 hEp
    split
    · rename_i r hR
      split
      · exact hC
      · split
        · exact hC
        · rename_i rcv _ st' hPop
          have hRr : rcv = r :=
            endpointQueuePopHead_popped_eq_head _ _ _ _ ep _ _ _ hObj (by simpa using hR) hPop
          subst hRr
          have hSF := hHead ep rcv hObj hR
          have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
          have hV1 := endpointQueuePopHead_replyViews_eq hInv hPop
          split
          · exact hC
          · rename_i st'' hStore
            have hI2 := storeTcbReceiveComplete_preserves_objects_invExt _ _ _ _ hI1 hStore
            have hV2 : st''.replyViews = st.replyViews := by
              rw [replyViews_storeTcbReceiveComplete hI1 hStore, hV1]
              exact ReplyViews.setServer_of_server hSF
            dsimp only
            refine replyWaitersConsistent.of_views ?_ hC
            rw [wakeThread_replyViews_eq _ _ _ hI2 (by rw [hV2]; exact hSF), hV2]
    · split
      · exact hC
      · rename_i st' hEnq
        have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hInv hEnq
        have hV1 := endpointQueueEnqueue_replyViews_eq hInv hEnq
        split
        · exact hC
        · rename_i st'' hStore
          refine replyWaitersConsistent.of_views ?_ hC
          rw [recordSendCap_replyViews_eq, removeRunnableOnCore_replyViews_eq, replyViews_storeTcbIpcStateAndMessage hI1 hStore,
            hV1]
          exact ReplyViews.setServer_of_server hSender
  · split <;> exact hC

theorem endpointSendDualWithCapsOnCore_preserves_replyWaitersConsistent
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hSender : ReplyViews.serverFree st.replyViews sender)
    (hHead : ∀ ep r, st.objects[endpointId]? = some (.endpoint ep) → ep.receiveQ.head = some r →
      ReplyViews.serverFree st.replyViews r) :
    (endpointSendDualWithCapsOnCore endpointId sender msg rights base c
      st).1.replyWaitersConsistent := by
  have hB := endpointSendDualOnCore_preserves_replyWaitersConsistent endpointId sender
    { msg with capsGranted := rights.mem .grant } c st hInv hC hSender hHead
  have hI := endpointSendDualOnCore_preserves_objects_invExt endpointId sender
    { msg with capsGranted := rights.mem .grant } c st hInv
  unfold endpointSendDualWithCapsOnCore
  cases hR : endpointSendDualOnCore endpointId sender { msg with capsGranted := rights.mem .grant } c st with
  | mk s1 res =>
    rw [hR] at hB hI
    cases res with
    | error e => exact hB
    | ok sgi =>
      dsimp only
      repeat' split
      all_goals first
        | exact hB
        | (rename_i hU; exact replyWaitersConsistent.of_views
            (ipcUnwrapCaps_replyViews_eq _ _ _ _ hI hU) hB)

-- ============================================================================
-- §5  Notifications: a signalled or waiting thread waits on no server
-- ============================================================================

theorem replyViews_of_ntfnLinksRewritten {st s : SystemState} (h : ntfnLinksRewritten st s) :
    s.replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun _ _ hk => by
      obtain ⟨t', h', hR⟩ := h.tcb_fwd hk
      exact ⟨t', h', replyView_of_tcbNtfnLinkRewrite hR⟩)
    (fun _ _ hk => by
      obtain ⟨t0, h0, -⟩ := h.tcb_bwd hk
      exact ⟨t0, h0⟩)

theorem detachNtfnHead_replyViews_eq (st : SystemState) (hd : SeLe4n.ThreadId)
    (nx : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (detachNtfnHead st hd nx).replyViews = st.replyViews :=
  replyViews_of_ntfnLinksRewritten (detachNtfnHead_linksRewritten st hd nx hInv)

theorem linkNtfnWaiter_replyViews_eq {st st' : SystemState} {w : SeLe4n.ThreadId}
    {tl : Option SeLe4n.ThreadId} (hInv : st.objects.invExt) (h : linkNtfnWaiter st w tl = .ok st') :
    st'.replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun k t0 hk => by
      obtain ⟨t', h', hR⟩ := linkNtfnWaiter_tcb_forward hInv h k t0 hk
      exact ⟨t', h', replyView_of_tcbNtfnLinkRewrite hR⟩)
    (fun k t' hk => by
      obtain ⟨t0, h0, -⟩ := linkNtfnWaiter_tcb_backward hInv h k t' hk
      exact ⟨t0, h0⟩)

/-- A notification store moves no view. -/
theorem replyViews_storeNotification_eq {st st' : SystemState} {nid : SeLe4n.ObjId}
    {n0 n : Notification} (hInv : st.objects.invExt) (hN : st.getNotification? nid = some n0)
    (h : storeObject nid (.notification n) st = .ok ((), st')) : st'.replyViews = st.replyViews :=
  replyViews_storeObject_eq hInv h (by
    unfold replyViews getObject?
    rw [(getNotification?_eq_some_iff st nid n0).1 hN]; rfl) rfl

/-- **Signal keeps the reply-waiter queues consistent**: the waiter it wakes
was blocked on the notification, so it waits on no server before or after. -/
theorem notificationSignalOnCore_preserves_replyWaitersConsistent (nid : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hHead : ∀ n w, st.getNotification? nid = some n → n.waitHead = some w →
      ReplyViews.serverFree st.replyViews w) :
    (notificationSignalOnCore nid badge c st).1.replyWaitersConsistent := by
  unfold notificationSignalOnCore
  split
  · rename_i n hN
    split
    · rename_i w hW
      have hSF := hHead n w hN hW
      dsimp only
      split
      · exact hC
      · rename_i st' hS
        have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
        have hV1 := replyViews_storeNotification_eq hInv hN hS
        split
        · exact hC
        · rename_i st'' hStore
          have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hStore
          have hV2 : st''.replyViews = st.replyViews := by
            rw [replyViews_storeTcbIpcStateAndMessage hI1 hStore, hV1]
            exact ReplyViews.setServer_of_server hSF
          have hV3 := (detachNtfnHead_replyViews_eq st'' w (ntfnSuccessor? st w) hI2).trans hV2
          refine replyWaitersConsistent.of_views ?_ hC
          rw [wakeThread_replyViews_eq _ _ _ (detachNtfnHead_linksRewritten _ _ _ hI2).2.1
            (by rw [hV3]; exact hSF), hV3]
    · dsimp only
      split
      · exact hC
      · rename_i st' hS
        exact replyWaitersConsistent.of_views (replyViews_storeNotification_eq hInv hN hS) hC
  · split <;> exact hC

/-- **Wait keeps the reply-waiter queues consistent**: the waiter is the running
thread, which waits on no server, and it blocks on the notification, which names
none. -/
theorem notificationWaitOnCore_preserves_replyWaitersConsistent (nid : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hWaiter : ReplyViews.serverFree st.replyViews waiter) :
    (notificationWaitOnCore nid waiter c st).1.replyWaitersConsistent := by
  unfold notificationWaitOnCore
  split
  · rename_i n hN
    split
    · dsimp only
      split
      · exact hC
      · rename_i st' hS
        have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
        split
        · exact hC
        · rename_i st'' hStore
          refine replyWaitersConsistent.of_views ?_ hC
          rw [replyViews_storeTcbIpcState hI1 hStore, replyViews_storeNotification_eq hInv hN hS]
          exact ReplyViews.setServer_of_server hWaiter
    · split
      · exact hC
      · rename_i tcb hT
        split
        · exact hC
        · dsimp only
          split
          · exact hC
          · rename_i st1 hS
            have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
            have hO1 : st1.objects[waiter.toObjId]? = some (.tcb tcb) := by
              exact lookupTcb_some_objects st1 waiter tcb
                (lookupTcb_preserved_by_storeObject_notification (pair := ((), st1)) hT
                  ((getNotification?_eq_some_iff st nid n).1 hN) hInv hS)
            split
            · exact hC
            · rename_i st2 hStore
              have hI2 := storeTcbIpcStateAndMessage_fromTcb_objects_invExt hI1 hStore
              split
              · exact hC
              · rename_i st3 hL
                refine replyWaitersConsistent.of_views ?_ hC
                rw [removeRunnableOnCore_replyViews_eq, linkNtfnWaiter_replyViews_eq hI2 hL,
                  replyViews_storeTcbIpcStateAndMessage_fromTcb hI1 hO1 hStore,
                  replyViews_storeNotification_eq hInv hN hS]
                exact ReplyViews.setServer_of_server hWaiter
  · split <;> exact hC

end SeLe4n.Kernel
