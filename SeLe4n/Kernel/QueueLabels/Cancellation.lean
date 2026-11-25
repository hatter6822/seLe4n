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

namespace QueueLabelsFrame

theorem of_ipcKept {st st' : SystemState} (hI : st'.objects.invExt)
    (hK : tcbProjKept TCB.ipcState st' st) (hN : NtfnLabelsKept st st') : QueueLabelsFrame st st' :=
  ⟨.of_ipcKept hK, hN, hI⟩

/-- **The restore** makes the thread `.ready`. -/
theorem restoreToReadyStaging (st : SystemState) (t : SeLe4n.ThreadId)
    (restart : Bool) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (Lifecycle.Suspend.restoreToReadyStaging st t restart) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb st t hInv (fun x => TcbWaitsKept.of_noWait (by
    cases restart <;> simp [TCB.restoredToReady, TCB.restoredToRestart])) fun x _ => by
    cases restart <;> exact TcbNtfnKept.of_notBlocked (by simp [TCB.restoredToReady,
      TCB.restoredToRestart]) (by simp [TCB.restoredToReady, TCB.restoredToRestart])
      (by simp [TCB.restoredToReady, TCB.restoredToRestart])

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

theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) :=
  of_ipcKept (removeFromNotificationWaitQueue_preserves_objects_invExt st t hInv)
    (removeFromNotificationWaitQueue_tcbField_frame TCB.ipcState (fun _ _ _ _ _ _ => rfl) st t hInv)
    (NtfnLabelsKept.removeFromNotificationWaitQueue st t hInv)

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
    have F1 := FinaliseFrameAny.cutThreadReplyFrameOut _ tcb S0.invExt
    have S1 := S0.trans (of_ipcKept F1.invExt (tcbProjKept.of_fwd_bwd
      (fun k t0 hk => ⟨t0, cutThreadReplyFrameOut_tcb_eq _ tcb S0.invExt k t0 hk, rfl⟩)
      (fun k t' hk => ⟨t', cutThreadReplyFrameOut_tcb_backward _ tcb S0.invExt k t' hk⟩))
      (NtfnLabelsKept.cutThreadReplyFrameOut _ tcb S0.invExt))
    have S2 := S1.trans (restoreToReadyCancelled _ t S1.invExt)
    have F3 := FinaliseFrameAny.consumeReplyLink _ t tcb S2.invExt
    have S3 := S2.trans (of_ipcKept F3.invExt
      (tcbProjKept.consumeReplyLink _ t tcb S2.invExt fun _ => rfl)
      (NtfnLabelsKept.consumeReplyLink _ t tcb S2.invExt))
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
