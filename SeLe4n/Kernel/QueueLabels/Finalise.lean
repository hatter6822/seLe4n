-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.IpcNotification
import SeLe4n.Kernel.KernelRecords.Finalise

/-! # The finalisation: frames

WS-SX SX11.2.  Finalising an object takes every thread blocked on it off its
queue and makes it `.ready` (or `.Inactive` and `.ready`, a faulted waiter);
a reply waiter orphaned stays blocked on its reply; a finalised thread is
suspended.  So no step moves a thread onto an endpoint.  The proofs follow the
records' own (`KernelRecords/Finalise.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace NtfnLabelsKept

/-- **The in-place endpoint-queue removal**: the neighbours' endpoint-queue
links, the endpoint's ends and the thread's own endpoint-queue links. -/
theorem storeQueueRemove (st : SystemState) (e : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId)
    (ep : Endpoint) (tcb : TCB) (hInv : st.objects.invExt) :
    NtfnLabelsKept st (SeLe4n.Kernel.storeQueueRemove st e q t ep tcb) := by
  have hHead : ∀ c, ∀ o, headAdvancedEndpoint q c o = o ∨
      ∃ ep ep', o = .endpoint ep ∧ headAdvancedEndpoint q c o = .endpoint ep' := by
    intro c o; cases o with
    | endpoint x => exact Or.inr ⟨x, _, rfl, rfl⟩
    | _ => exact Or.inl rfl
  have hEnds : ∀ h t, ∀ o, endsSetEndpoint q h t o = o ∨
      ∃ ep ep', o = .endpoint ep ∧ endsSetEndpoint q h t o = .endpoint ep' := by
    intro h t o; cases o with
    | endpoint x => exact Or.inr ⟨x, _, rfl, rfl⟩
    | _ => exact Or.inl rfl
  have h1 : NtfnLabelsKept st (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st) ∧ (match tcb.queuePPrev with
      | some .endpointHead => st.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
      | none => st).objects.invExt := by
    split
    · exact ⟨modifyObject_endpoint hInv (hHead _), modifyObject_preserves_objects_invExt hInv⟩
    · exact ⟨updateTcb st _ hInv (fun _ _ => TcbNtfnKept.of_fields rfl rfl rfl),
        SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv⟩
    · exact ⟨refl _, hInv⟩
  have h2 : ∀ S : SystemState, NtfnLabelsKept st S → S.objects.invExt →
      NtfnLabelsKept st (match tcb.queueNext with
        | some n => S.updateTcb n (queueUnlinkSuccessor tcb)
        | none => S) ∧ (match tcb.queueNext with
        | some n => S.updateTcb n (queueUnlinkSuccessor tcb)
        | none => S).objects.invExt := by
    intro S k i
    split
    · exact ⟨k.trans (updateTcb S _ i (fun _ _ => TcbNtfnKept.of_fields rfl rfl rfl)),
        SystemState.updateTcb_preserves_objects_invExt _ _ _ i⟩
    · exact ⟨k, i⟩
  obtain ⟨k2, i2⟩ := h2 _ h1.1 h1.2
  exact (k2.trans (modifyObject_endpoint i2 (hEnds _ _))).trans
    (updateTcb _ t (modifyObject_preserves_objects_invExt i2)
      (fun _ _ => TcbNtfnKept.of_fields rfl rfl rfl))

/-- **An endpoint-blocked thread's cancel**: off the queue, then restored. -/
theorem storeEndpointBlockedCancelled (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : s.objects.invExt) :
    NtfnLabelsKept s (SeLe4n.Kernel.storeEndpointBlockedCancelled s e q t ep tcb) := by
  unfold SeLe4n.Kernel.storeEndpointBlockedCancelled
  exact (storeQueueRemove s e q t ep tcb hInv).trans (updateTcb _ t
    (FinaliseFrame.storeQueueRemove s e q t ep tcb hInv).invExt
    fun _ _ => TcbNtfnKept.of_notBlocked (fun _ h => by simp [cancelledEndpointWaiterTcb] at h))

/-- **The unbind's two in-place writes**, each clearing a binding. -/
theorem storeUnbindNotification (s : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (hInv : s.objects.invExt) : NtfnLabelsKept s (SeLe4n.Kernel.storeUnbindNotification s t n) := by
  unfold SeLe4n.Kernel.storeUnbindNotification
  exact (updateTcb s t (f := fun t => { t with boundNotificationCode := 0 }) hInv
    fun _ _ => TcbNtfnKept.of_fields rfl rfl rfl).trans
    (modifyObject (k := n) (f := mapNotificationObject fun n => { n with boundTCBCode := 0 })
      (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv) fun _ o h => by
      cases o with
      | notification x =>
        exact ⟨fun _ hb => by simp [Notification.boundTCB] at hb, h.2.1, h.2.2⟩
      | _ => exact h)

end NtfnLabelsKept

namespace QueueLabelsFrame

/-- **An endpoint waiter's cancel**: the pop, the restore or the fault mark,
and the wake. -/
theorem storeEndpointWaiterCancelled (st : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (faulted : Bool)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.storeEndpointWaiterCancelled st e q t next faulted) := by
  have F1 := RecordsEndpointFrame.storePopHead st e q t next hInv
  unfold SeLe4n.Kernel.storeEndpointWaiterCancelled
  split
  · unfold SeLe4n.Kernel.storeEndpointWaiterFaulted
    exact (of_endpointFrame F1).trans (updateTcb _ t (f := faultedEndpointWaiterTcb) F1.invExt
      (fun _ => TcbWaitsKept.of_noWait (by simp))
      fun _ _ => TcbNtfnKept.of_notBlocked (fun _ h => by simp [faultedEndpointWaiterTcb] at h))
  unfold SeLe4n.Kernel.storeEndpointWaiterRestarted
  have S2 := (of_endpointFrame F1).trans (updateTcb _ t (f := cancelledEndpointWaiterTcb) F1.invExt
    (fun _ => TcbWaitsKept.of_noWait (by simp [cancelledEndpointWaiterTcb]))
    fun _ _ => TcbNtfnKept.of_notBlocked (fun _ h => by simp [cancelledEndpointWaiterTcb] at h))
  refine S2.trans (of_frame (RecordsFrame.enqueueRunnableOnCore _ _ t S2.invExt fun x hx => ?_))
  rw [SystemState.updateTcb_getTcb?_self _ _ _ F1.invExt] at hx
  cases hT : (SeLe4n.Kernel.storePopHead st e q t next).getTcb? t with
  | none => rw [hT] at hx; cases hx
  | some y =>
    rw [hT] at hx; cases hx
    simp [cancelledEndpointWaiterTcb]

/-- **A notification waiter's cancel and wake.** -/
theorem notificationWaiterCancelled (s : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : s.objects.invExt) (hT : s.getTcb? t = some tcb)
    (hC : notificationWaiterCancellable s n t tcb = true) :
    QueueLabelsFrame s (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) := by
  have S1 := cancelIpcBlocking s t tcb hInv
  exact S1.trans (of_frame (RecordsFrame.enqueueRunnableOnCore _ _ t S1.invExt fun x hx =>
    cancelIpcBlocking_victim_ready_of_ipcState s t tcb tcb hInv
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) (notificationWaiterCancellable_parts hC).1 rfl
      x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)))

/-- **A finalised thread's suspend**: off the scheduler, then `.Inactive`. -/
theorem finaliseSuspend (s : SystemState) (t : SeLe4n.ThreadId) (hInv : s.objects.invExt) :
    QueueLabelsFrame s ((descheduleAtPlacement s t).updateTcb t finalisedSuspendMark) := by
  have F := RecordsFrame.descheduleAtPlacement s t hInv
  exact (of_frame F).trans (updateTcb _ t F.invExt fun _ => TcbWaitsKept.of_ipc rfl)

/-- **An endpoint-blocked thread's cancel**: off the queue, restored. -/
theorem storeEndpointBlockedCancelled (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : s.objects.invExt) :
    QueueLabelsFrame s (SeLe4n.Kernel.storeEndpointBlockedCancelled s e q t ep tcb) := by
  have hN := NtfnLabelsKept.storeEndpointBlockedCancelled s e q t ep tcb hInv
  obtain ⟨X, i, k, hEq⟩ := tcbProjKept.storeEndpointBlockedCancelled_split (g := TCB.ipcState)
    s e q t ep tcb hInv (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hEq] at hN ⊢
  have i' := SystemState.updateTcb_preserves_objects_invExt _ t tcbOffQueue i
  have S3 := updateTcb _ t i' (f := cancelledEndpointWaiterTcb)
    (fun _ => TcbWaitsKept.of_noWait (by simp [cancelledEndpointWaiterTcb]))
    fun _ _ => TcbNtfnKept.of_notBlocked (fun _ h => by simp [cancelledEndpointWaiterTcb] at h)
  exact ⟨(EndpointWaitersShrink.of_ipcKept k).trans ((EndpointWaitersShrink.of_ipcKept
    (tcbProjKept.updateTcb _ t (f := tcbOffQueue) i fun _ => rfl)).trans S3.shrink), hN, S3.invExt⟩

/-- **One reply waiter orphaned**: still blocked on its reply. -/
theorem orphanReplyWaiter (s : SystemState) (w x : SeLe4n.ThreadId) (hInv : s.objects.invExt) :
    QueueLabelsFrame s (SeLe4n.Kernel.orphanReplyWaiter s w x) := by
  have S1 := mapTcbInPlace s w (g := TCB.serverForgotten) hInv (fun t =>
    TcbWaitsKept.of_noWait (by rw [TCB.serverForgotten_ipcState]; simp))
    fun t _ => TcbNtfnKept.of_notBlocked (fun _ h => by rw [TCB.serverForgotten_ipcState] at h; cases h)
  exact S1.trans (unlinkReplyWaiter _ w x S1.invExt)

/-- **A reply-blocked caller's cancel**, its lent context handed back and its
holder descheduled, then its server's boost reverted. -/
theorem finaliseReplyCancel (s : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : s.objects.invExt) :
    QueueLabelsFrame s
      (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
  have S1 : QueueLabelsFrame s (cancelIpcBlockingMigrated c t s) := by
    have S := cancelIpcBlocking s c t hInv
    rcases cancelIpcBlockingMigrated_cases c t s with h | ⟨_, _, _, _, h⟩ <;> rw [h]
    · exact S
    · exact S.trans (of_frame (RecordsFrame.settleReturnedContext _ _ _ S.invExt))
  have S2 : QueueLabelsFrame s (cancelIpcBlockingReclaimed c t s) := by
    unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
    split
    · exact S1
    · exact S1.trans (of_frame (RecordsFrame.descheduleAtPlacement _ _ S1.invExt))
  unfold finaliseReplyRevert
  split
  · exact S2.trans (of_frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ S2.invExt))
  · exact S2

/-- **The finalisation moves no thread onto an endpoint.** -/
theorem finaliseFinalObject (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.finaliseFinalObject target st) :=
  finaliseFinalObject_closed (QueueLabelsFrame st)
    (fun e q s _ t tcb h _ _ _ _ => h.trans (storeEndpointWaiterCancelled s e q t _ _ h.invExt))
    (fun n s _ t tcb h _ _ hT hC => h.trans (notificationWaiterCancelled s n t tcb h.invExt hT hC))
    (fun n s _ t h _ _ _ _ => h.trans (of_ipcKept
      (FinaliseFrame.storeUnbindNotification s t n h.invExt).invExt
      (tcbProjKept.storeUnbindNotification s t n h.invExt fun _ => rfl)
      (NtfnLabelsKept.storeUnbindNotification s t n h.invExt)))
    (fun s t _ h _ _ _ _ => h.trans (of_frame (RecordsFrame.descheduleAtPlacement s t h.invExt)))
    (fun _ _ _ _ _ _ h _ _ _ _ hOk =>
      h.trans (of_frame (RecordsFrame.cancelBoundDonationOnCore h.invExt hOk)))
    (fun s _ t tcb _ h _ _ _ _ => h.trans (cancelIpcBlocking s t tcb h.invExt))
    (fun s e q t ep tcb h _ _ _ => h.trans (storeEndpointBlockedCancelled s e q t ep tcb h.invExt))
    (fun s t _ h _ _ _ _ _ => h.trans (finaliseSuspend s t h.invExt))
    (fun s t h => h.trans (of_ipcKept (FinaliseFrame.releaseCores s t h.invExt).invExt
      (tcbProjKept.of_objects (finaliseThreadReleaseCores_objects s t))
      (NtfnLabelsKept.of_objects_eq (finaliseThreadReleaseCores_objects s t))))
    (fun s s1 x _ rid r h _ _ hR _ hS _ _ _ _ => by
      have F := RecordsFrame.storeReply h.invExt
        ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hS
      exact h.trans (of_frame (F.trans (RecordsFrame.updateSchedContext _ _ _ F.invExt))))
    (fun s _ _ c t h _ _ _ _ => h.trans (finaliseReplyCancel s c t h.invExt))
    (fun s s1 _ tid _ h _ _ hEq => by
      subst hEq
      exact h.trans (of_frame (RecordsFrame.updateTcb s tid h.invExt fun _ => rfl)))
    ⟨fun s t h => h.trans (of_frame (RecordsFrame.cancelYieldTo s t h.invExt)),
     fun s c h => h.trans (of_frame (RecordsFrame.completeYieldFrom s c h.invExt))⟩
    (fun s w x _ h _ _ _ => h.trans (orphanReplyWaiter s w x h.invExt))
    (fun s _ r c _ h _ _ _ _ =>
      h.trans (of_frame (RecordsFrame.finaliseReplyUnheldPop s r c h.invExt)))
    (fun s _ _ _ t h _ _ _ _ => h.trans (of_frame (RecordsFrame.cutCancelledCallerHead s t h.invExt)))
    (fun s c h => h.trans (of_frame (RecordsFrame.unbindSchedContextNotification s c h.invExt)))
    target st (refl hInv)

end QueueLabelsFrame

end SeLe4n.Kernel
