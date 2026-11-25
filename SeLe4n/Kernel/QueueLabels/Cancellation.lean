-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.IpcReplyRecv
import SeLe4n.Kernel.KernelRecords.Cancellation

/-! # The cancellation: shrinks

WS-SX SX11.2.  The IPC teardown takes a thread off its endpoint's queue and
restores it `.ready` (its restart record), so it removes a waiter and adds
none; the dequeue, the donation return and the reply-link consume write queue
links, binding codes and reply codes, not an IPC state.  The proofs follow the
records' own (`KernelRecords/Cancellation.lean`), with the thread projection
`TCB.ipcState` in place of the fault fields.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **A step keeping every thread's IPC state moves no thread onto an
endpoint.** -/
theorem EndpointWaitersShrink.of_ipcKept {st st' : SystemState}
    (hK : tcbProjKept TCB.ipcState st' st) : EndpointWaitersShrink st st' := fun u t' e hT hW => by
  have h := hK u
  rw [hT] at h
  cases hs : st.getTcb? u with
  | none => rw [hs] at h; cases h
  | some x =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨x, rfl, h ▸ hW⟩

namespace NtfnLabelsKept

/-- **One object rewritten in its slot** by an update that keeps its share. -/
theorem modifyObject {st : SystemState} {k : SeLe4n.ObjId} {f : KernelObject → KernelObject}
    (hInv : st.objects.invExt)
    (hf : ∀ ctx o, notificationEntryLabelsAgree ctx k o → notificationEntryLabelsAgree ctx k (f o)) :
    NtfnLabelsKept st (st.modifyObject k f) := fun ctx H x o hO => by
  rw [modifyObject_objects_getElem hInv] at hO
  split at hO
  · rename_i hkx
    subst hkx
    cases hG : st.objects[k]? with
    | none => rw [hG] at hO; cases hO
    | some o0 =>
      simp only [hG, Option.map_some, Option.some.injEq] at hO
      subst hO
      exact hf ctx o0 (H _ _ hG)
  · exact H x o hO

/-- An update that rewrites an endpoint, if anything. -/
theorem modifyObject_endpoint {st : SystemState} {k : SeLe4n.ObjId} {f : KernelObject → KernelObject}
    (hInv : st.objects.invExt)
    (hf : ∀ o, f o = o ∨ ∃ ep ep', o = .endpoint ep ∧ f o = .endpoint ep') :
    NtfnLabelsKept st (st.modifyObject k f) :=
  modifyObject hInv fun _ o h => by
    rcases hf o with e | ⟨_, _, rfl, e⟩
    · rw [e]; exact h
    · rw [e]; trivial

/-- **A neighbour's endpoint-queue links patched**, its share kept. -/
theorem queueNeighbourPatch (st : SystemState) (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hU : ∀ t, TcbNtfnKept t (upd t)) (hInv : st.objects.invExt) :
    NtfnLabelsKept st { st with objects := SeLe4n.Kernel.queueNeighbourPatch st.objects nid? upd } := by
  unfold SeLe4n.Kernel.queueNeighbourPatch
  cases nid? with
  | none => exact of_objects_eq rfl
  | some nid =>
    dsimp only
    split
    · rename_i t hRead
      exact insert hInv fun ctx H => hU t ctx _ (H _ _ hRead)
    · exact of_objects_eq rfl

/-- **The mid-queue splice** patches two neighbours' endpoint-queue links. -/
theorem spliceOutMidQueueNode (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    NtfnLabelsKept st (SeLe4n.Kernel.spliceOutMidQueueNode st t) := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact refl _
  · rename_i tcb _
    exact (queueNeighbourPatch st tcb.queuePrev (queueUnlinkPredecessor tcb)
      (fun _ => TcbNtfnKept.of_fields rfl rfl rfl) hInv).trans
      (queueNeighbourPatch { st with objects := (SeLe4n.Kernel.queueNeighbourPatch st.objects
        tcb.queuePrev (queueUnlinkPredecessor tcb)) } tcb.queueNext (queueUnlinkSuccessor tcb)
        (fun _ => TcbNtfnKept.of_fields rfl rfl rfl) (queueNeighbourPatch_invExt _ _ _ hInv))

/-- **The targeted dequeue**: the splice, then the endpoint's ends. -/
theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    NtfnLabelsKept st (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) := fun ctx H k o hO => by
  have hS := spliceOutMidQueueNode st t hInv ctx H
  have hI := spliceOutMidQueueNode_preserves_objects_invExt st t hInv
  cases o with
  | tcb x => exact hS k _ ((removeFromBlockingEndpoint_nonEndpoint st t e hI k _ (fun _ h => by
      cases h)).mp hO)
  | notification n => exact hS k _ ((removeFromBlockingEndpoint_nonEndpoint st t e hI k _
      (fun _ h => by cases h)).mp hO)
  | _ => trivial

/-- **The donation return** pops a reply stack: a records' frame. -/
theorem returnDonationToCancelledCaller (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    NtfnLabelsKept st (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) :=
  Lifecycle.Suspend.returnDonationToCancelledCaller_elimPops (P := NtfnLabelsKept st) (refl _)
    (fun _ _ _ _ _ hPop => of_frame (RecordsFrame.returnDonatedSchedContext hInv hPop))
    (fun _ _ _ _ _ hK => of_frame (RecordsFrame.keepDonatedSchedContext hInv hK))

/-- **The reply frame's cut** writes replies alone. -/
theorem cutThreadReplyFrameOut (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    NtfnLabelsKept st (SeLe4n.Kernel.cutThreadReplyFrameOut st t) := by
  unfold SeLe4n.Kernel.cutThreadReplyFrameOut
  split
  · exact refl _
  · exact of_frame (RecordsFrame.cutReplyFrameOutOrSelf st _ hInv)

/-- **The reply link's consume**: the reply path's own teardown. -/
theorem consumeReplyLink (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) : NtfnLabelsKept st (Lifecycle.Suspend.consumeReplyLink st c t) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact refl _
  · exact of_frame (RecordsFrame.consumeCallerReply hInv (SystemState.consumeCallerReply_eq_link _ _ _))

end NtfnLabelsKept

namespace endpointQueueLabelsAgree

variable {ctx : LabelingContext}

/-- **A neighbour's endpoint-queue links patched**, each new link of its label. -/
theorem queueNeighbourPatch {st : SystemState} (hInv : st.objects.invExt)
    (H : endpointQueueLabelsAgree ctx st) (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hU : ∀ n t, nid? = some n → endpointQueueEntryLabelsAgree ctx n.toObjId (.tcb t) →
      endpointQueueEntryLabelsAgree ctx n.toObjId (.tcb (upd t))) :
    endpointQueueLabelsAgree ctx
      { st with objects := SeLe4n.Kernel.queueNeighbourPatch st.objects nid? upd } := by
  unfold SeLe4n.Kernel.queueNeighbourPatch
  cases nid? with
  | none => exact H
  | some nid =>
    dsimp only
    split
    · rename_i t hRead
      exact insert hInv H (hU nid t rfl (H _ _ hRead))
    · exact H

/-- **A thread's two neighbours unlinked from it**: each inherits a link of the
removed thread's, which carries the removed thread's label, which is the
neighbour's. -/
theorem neighboursUnlinked {st : SystemState} (hInv : st.objects.invExt)
    (H : endpointQueueLabelsAgree ctx st) {t : SeLe4n.ThreadId} {tcb : TCB}
    (hO : st.objects[t.toObjId]? = some (.tcb tcb)) :
    endpointQueueLabelsAgree ctx { st with objects := (SeLe4n.Kernel.queueNeighbourPatch
      (SeLe4n.Kernel.queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb))
      tcb.queueNext (queueUnlinkSuccessor tcb)) } := by
  obtain ⟨hP, hN⟩ := links H hO
  have H1 := queueNeighbourPatch hInv H tcb.queuePrev (queueUnlinkPredecessor tcb)
    fun n x hn hx => tcb_entry (fun u hu => hx.1 u hu)
      (fun u hu => (hN u hu).trans (hP n hn).symm)
  exact queueNeighbourPatch (queueNeighbourPatch_invExt _ _ _ hInv) H1 tcb.queueNext
    (queueUnlinkSuccessor tcb)
    fun n x hn hx => tcb_entry
      (fun u hu => (hP u hu).trans (hN n hn).symm)
      (fun u hu => hx.2 u hu)

/-- **The mid-queue splice** unlinks the thread's neighbours. -/
theorem spliceOutMidQueueNode {st : SystemState} (t : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (H : endpointQueueLabelsAgree ctx st) :
    endpointQueueLabelsAgree ctx (SeLe4n.Kernel.spliceOutMidQueueNode st t) := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact H
  · rename_i tcb hL
    exact neighboursUnlinked hInv H (lookupTcb_some_objects st t tcb hL)

/-- **The timeout's removal** (`endpointQueueRemove`): the neighbours unlinked,
the queue's ends moved to them, the thread's links cleared. -/
theorem endpointQueueRemove {st st' : SystemState} {e : SeLe4n.ObjId} {q : Bool}
    {t : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.endpointQueueRemove e q t st = .ok st')
    (H : endpointQueueLabelsAgree ctx st) : endpointQueueLabelsAgree ctx st' := by
  obtain ⟨ep, hEp⟩ := endpointQueueRemove_ok_getEndpoint? e q t st st' h
  have hEo := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
  cases hL : lookupTcb st t with
  | none =>
    unfold SeLe4n.Kernel.endpointQueueRemove SystemState.getObject? at h
    rw [hEo, hL] at h; cases h
  | some tcb =>
    rw [endpointQueueRemove_eq_patches e q t st ep tcb hEp hL] at h
    cases h
    have hO := lookupTcb_some_objects st t tcb hL
    obtain ⟨hP, hN⟩ := links H hO
    have I1 := queueNeighbourPatch_invExt _ tcb.queueNext (queueUnlinkSuccessor tcb)
      (queueNeighbourPatch_invExt _ tcb.queuePrev (queueUnlinkPredecessor tcb) hInv)
    have H1 := neighboursUnlinked hInv H hO
    have H2 := insert (k := e) I1 H1 (endpoint_entry_withQ q (H _ _ hEo)
      (queueRemoveBoundary_labelled (endsOf H hEo q) hP hN))
    have hC : endpointQueueEntryLabelsAgree ctx t.toObjId (.tcb (tcbWithQueueLinks tcb none none none)) :=
      tcb_entry (fun u hu => by simp at hu) (fun u hu => by simp at hu)
    have H3 := insert (RHTable_insert_preserves_invExt _ _ _ I1) H2 hC
    exact H3

/-- **A queue read through `removeThreadFromQueue`** keeps its ends labelled. -/
theorem removeThreadFromQueue_labelled {st : SystemState} {l : SecurityLabel} {q : IntrusiveQueue}
    {tid : SeLe4n.ThreadId} (H : endpointQueueLabelsAgree ctx st)
    (hq : queueEndsLabelled ctx l q) :
    queueEndsLabelled ctx l (removeThreadFromQueue st q tid) := by
  cases hL : lookupTcb st tid with
  | some tcb =>
    rw [removeThreadFromQueue_eq_queueRemoveBoundary st q tid tcb hL]
    obtain ⟨hP, hN⟩ := links H (lookupTcb_some_objects st tid tcb hL)
    exact queueRemoveBoundary_labelled hq hP hN
  | none =>
    simp only [removeThreadFromQueue, hL]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · dsimp only at hu; split at hu
      · cases hu
      · exact hq.1 u hu
    · dsimp only at hu; split at hu
      · cases hu
      · exact hq.2 u hu

/-- **The targeted dequeue**: the splice, then the endpoint's ends moved to the
removed thread's neighbours. -/
theorem removeFromBlockingEndpoint {st : SystemState} (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (H : endpointQueueLabelsAgree ctx st) :
    endpointQueueLabelsAgree ctx (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) := by
  have HS := spliceOutMidQueueNode t hInv H
  have hI := spliceOutMidQueueNode_preserves_objects_invExt st t hInv
  rcases removeFromBlockingEndpoint_cases st t e with h | ⟨ep, hA, hE, h⟩ <;> rw [h]
  · exact HS
  · obtain ⟨hS, hR⟩ := ends HS hE
    exact insert hI HS ⟨by simpa using removeThreadFromQueue_labelled HS hS,
      by simpa using removeThreadFromQueue_labelled HS hR⟩

end endpointQueueLabelsAgree

namespace EndpointQueueLabelsKept

/-- **One object rewritten in its slot** by an update that keeps its share. -/
theorem modifyObject {st : SystemState} {k : SeLe4n.ObjId} {f : KernelObject → KernelObject}
    (hInv : st.objects.invExt)
    (hf : ∀ ctx o, endpointQueueEntryLabelsAgree ctx k o → endpointQueueEntryLabelsAgree ctx k (f o)) :
    EndpointQueueLabelsKept st (st.modifyObject k f) := fun ctx H x o hO => by
  rw [modifyObject_objects_getElem hInv] at hO
  split at hO
  · rename_i hkx
    subst hkx
    cases hG : st.objects[k]? with
    | none => rw [hG] at hO; cases hO
    | some o0 =>
      simp only [hG, Option.map_some, Option.some.injEq] at hO
      subst hO
      exact hf ctx o0 (H _ _ hG)
  · exact H x o hO

theorem spliceOutMidQueueNode (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    EndpointQueueLabelsKept st (SeLe4n.Kernel.spliceOutMidQueueNode st t) := fun _ H =>
  endpointQueueLabelsAgree.spliceOutMidQueueNode t hInv H

theorem endpointQueueRemove {st st' : SystemState} {e : SeLe4n.ObjId} {q : Bool}
    {t : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.endpointQueueRemove e q t st = .ok st') : EndpointQueueLabelsKept st st' :=
  fun _ H => endpointQueueLabelsAgree.endpointQueueRemove hInv h H

theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    EndpointQueueLabelsKept st (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) := fun _ H =>
  endpointQueueLabelsAgree.removeFromBlockingEndpoint t e hInv H

/-- The notification-queue neighbours' unlink writes notification links alone. -/
theorem unlinkNtfnNeighbours (st : SystemState) (hInv : st.objects.invExt)
    (prev next : Option SeLe4n.ThreadId) :
    EndpointQueueLabelsKept st (SeLe4n.Kernel.unlinkNtfnNeighbours st prev next) := by
  unfold SeLe4n.Kernel.unlinkNtfnNeighbours
  cases prev with
  | none =>
    cases next with
    | none => exact refl _
    | some n => exact updateTcb _ _ hInv (by tcb_endpoint_links_kept)
  | some p =>
    cases next with
    | none => exact updateTcb _ _ hInv (by tcb_endpoint_links_kept)
    | some n =>
      exact (updateTcb _ _ hInv (by tcb_endpoint_links_kept)).trans
        (updateTcb _ _ (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv)
          (by tcb_endpoint_links_kept))

/-- **A thread taken out of its notification queue** writes a notification and
notification links alone. -/
theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    EndpointQueueLabelsKept st (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) := by
  unfold SeLe4n.Kernel.removeFromNotificationWaitQueue
  split
  · split
    · split
      · dsimp only
        exact (insert (o := .notification _) hInv fun _ _ => trivial).trans ((updateTcb _ t
          (RHTable_insert_preserves_invExt _ _ _ hInv) (by tcb_endpoint_links_kept)).trans
          (unlinkNtfnNeighbours _ (SystemState.updateTcb_preserves_objects_invExt _ _ _
            (RHTable_insert_preserves_invExt _ _ _ hInv)) _ _))
      · exact refl _
    · exact refl _
  · exact refl _

end EndpointQueueLabelsKept

namespace QueueLabelsFrame

theorem of_ipcKept {st st' : SystemState} (hI : st'.objects.invExt)
    (hK : tcbProjKept TCB.ipcState st' st) (hN : NtfnLabelsKept st st')
    (hQ : EndpointQueueLabelsKept st st') : QueueLabelsFrame st st' :=
  ⟨.of_ipcKept hK, hN, hQ, hI⟩

/-- **The restore** makes the thread `.ready`. -/
theorem restoreToReadyStaging (st : SystemState) (t : SeLe4n.ThreadId)
    (restart : Bool) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.restoreToReadyStaging st t restart) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb st t hInv (fun x => TcbWaitsKept.of_noWait (by
    cases restart <;> simp [TCB.restoredToReady, TCB.restoredToRestart]))
    (fun x _ => by
      cases restart <;> exact TcbNtfnKept.of_notBlocked (by simp [TCB.restoredToReady,
        TCB.restoredToRestart]) (by simp [TCB.restoredToReady, TCB.restoredToRestart])
        (by simp [TCB.restoredToReady, TCB.restoredToRestart]))
    (fun x _ => by
      cases restart <;> exact TcbEndpointLinksKept.of_cleared
        (by simp [TCB.restoredToReady, TCB.restoredToRestart])
        (by simp [TCB.restoredToReady, TCB.restoredToRestart]))

theorem restoreToReadyCancelled (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.restoreToReadyCancelled st t) :=
  restoreToReadyStaging st t _ hInv

theorem restoreToReady (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.restoreToReady st t) :=
  restoreToReadyStaging st t _ hInv

/-- The targeted dequeue writes queue links and an endpoint. -/
theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) :=
  of_ipcKept (removeFromBlockingEndpoint_preserves_objects_invExt st t e hInv) (fun x => by
    rw [removeFromBlockingEndpoint_getTcb?_eq_splice st t e hInv x]
    exact spliceOutMidQueueNode_tcbField_frame TCB.ipcState (fun _ _ _ _ _ _ => rfl) st t hInv x)
    (NtfnLabelsKept.removeFromBlockingEndpoint st t e hInv)
    (EndpointQueueLabelsKept.removeFromBlockingEndpoint st t e hInv)

theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) :=
  of_ipcKept (removeFromNotificationWaitQueue_preserves_objects_invExt st t hInv)
    (removeFromNotificationWaitQueue_tcbField_frame TCB.ipcState (fun _ _ _ _ _ _ => rfl) st t hInv)
    (NtfnLabelsKept.removeFromNotificationWaitQueue st t hInv)
    (EndpointQueueLabelsKept.removeFromNotificationWaitQueue st t hInv)

/-- **The IPC teardown** restores the thread `.ready` and writes no other IPC
state. -/
theorem cancelIpcBlocking (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
  cases hB : tcb.ipcState with
  | ready => unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]; exact refl hInv
  | blockedOnSend e | blockedOnReceive e | blockedOnCall e =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    exact (removeFromBlockingEndpoint st t e hInv).andThen fun h => restoreToReadyCancelled _ t h
  | blockedOnReply ep rt =>
    rw [cancelIpcBlocking_replyArm_unfold st t tcb hB]
    have F0 := FinaliseFrameAny.returnDonationToCancelledCaller st t tcb hInv
    have S0 := of_ipcKept F0.invExt
      (tcbProjKept.returnDonationToCancelledCaller st t tcb hInv fun _ _ _ => rfl)
      (NtfnLabelsKept.returnDonationToCancelledCaller st t tcb hInv)
      (Lifecycle.Suspend.returnDonationToCancelledCaller_elimPops
        (P := EndpointQueueLabelsKept st) (EndpointQueueLabelsKept.refl _)
        (fun _ _ _ _ _ hPop => .of_frame (RecordsFrame.returnDonatedSchedContext hInv hPop))
        (fun _ _ _ _ _ hK => .of_frame (RecordsFrame.keepDonatedSchedContext hInv hK)))
    have F1 := FinaliseFrameAny.cutThreadReplyFrameOut _ tcb S0.invExt
    have S1 := S0.trans (of_ipcKept F1.invExt (tcbProjKept.of_fwd_bwd
      (fun k t0 hk => ⟨t0, cutThreadReplyFrameOut_tcb_eq _ tcb S0.invExt k t0 hk, rfl⟩)
      (fun k t' hk => ⟨t', cutThreadReplyFrameOut_tcb_backward _ tcb S0.invExt k t' hk⟩))
      (NtfnLabelsKept.cutThreadReplyFrameOut _ tcb S0.invExt)
      (by
        unfold SeLe4n.Kernel.cutThreadReplyFrameOut
        split
        · exact .refl _
        · exact .of_frame (RecordsFrame.cutReplyFrameOutOrSelf _ _ S0.invExt)))
    have S2 := S1.trans (restoreToReadyCancelled _ t S1.invExt)
    have F3 := FinaliseFrameAny.consumeReplyLink _ t tcb S2.invExt
    have S3 := S2.trans (of_ipcKept F3.invExt
      (tcbProjKept.consumeReplyLink _ t tcb S2.invExt fun _ => rfl)
      (NtfnLabelsKept.consumeReplyLink _ t tcb S2.invExt)
      (by
        unfold Lifecycle.Suspend.consumeReplyLink
        split
        · exact .refl _
        · exact .of_frame (RecordsFrame.consumeCallerReply S2.invExt
            (SystemState.consumeCallerReply_eq_link _ _ _))))
    exact S3.trans (unlinkReplyWaiterOpt _ t _ S3.invExt)
  | blockedOnNotification n =>
    have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled
          (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [hEq]
    exact (removeFromNotificationWaitQueue st t hInv).andThen fun h => restoreToReadyCancelled _ t h

end QueueLabelsFrame

end SeLe4n.Kernel
