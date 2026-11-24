-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.EndpointWaiters.IpcReplyRecv
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

namespace EndpointWaitersFrame

theorem of_ipcKept {st st' : SystemState} (hI : st'.objects.invExt)
    (hK : tcbProjKept TCB.ipcState st' st) : EndpointWaitersFrame st st' :=
  ⟨.of_ipcKept hK, hI⟩

/-- **The restore** makes the thread `.ready`. -/
theorem restoreToReadyStaging (st : SystemState) (t : SeLe4n.ThreadId)
    (restart : Bool) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (Lifecycle.Suspend.restoreToReadyStaging st t restart) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb st t hInv fun x => TcbWaitsKept.of_noWait (by
    cases restart <;> simp [TCB.restoredToReady, TCB.restoredToRestart])

theorem restoreToReadyCancelled (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (Lifecycle.Suspend.restoreToReadyCancelled st t) :=
  restoreToReadyStaging st t _ hInv

theorem restoreToReady (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (Lifecycle.Suspend.restoreToReady st t) :=
  restoreToReadyStaging st t _ hInv

/-- The targeted dequeue writes queue links and an endpoint. -/
theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) :=
  of_ipcKept (removeFromBlockingEndpoint_preserves_objects_invExt st t e hInv) fun x => by
    rw [removeFromBlockingEndpoint_getTcb?_eq_splice st t e hInv x]
    exact spliceOutMidQueueNode_tcbField_frame TCB.ipcState (fun _ _ _ _ _ _ => rfl) st t hInv x

theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) :=
  of_ipcKept (removeFromNotificationWaitQueue_preserves_objects_invExt st t hInv)
    (removeFromNotificationWaitQueue_tcbField_frame TCB.ipcState (fun _ _ _ _ _ _ => rfl) st t hInv)

/-- **The IPC teardown** restores the thread `.ready` and writes no other IPC
state. -/
theorem cancelIpcBlocking (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
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
    have F1 := FinaliseFrameAny.cutThreadReplyFrameOut _ tcb S0.invExt
    have S1 := S0.trans (of_ipcKept F1.invExt (tcbProjKept.of_fwd_bwd
      (fun k t0 hk => ⟨t0, cutThreadReplyFrameOut_tcb_eq _ tcb S0.invExt k t0 hk, rfl⟩)
      (fun k t' hk => ⟨t', cutThreadReplyFrameOut_tcb_backward _ tcb S0.invExt k t' hk⟩)))
    have S2 := S1.trans (restoreToReadyCancelled _ t S1.invExt)
    have F3 := FinaliseFrameAny.consumeReplyLink _ t tcb S2.invExt
    have S3 := S2.trans (of_ipcKept F3.invExt
      (tcbProjKept.consumeReplyLink _ t tcb S2.invExt fun _ => rfl))
    exact S3.trans (unlinkReplyWaiterOpt _ t _ S3.invExt)
  | blockedOnNotification n =>
    have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled
          (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [hEq]
    exact (removeFromNotificationWaitQueue st t hInv).andThen fun h => restoreToReadyCancelled _ t h

end EndpointWaitersFrame

end SeLe4n.Kernel
