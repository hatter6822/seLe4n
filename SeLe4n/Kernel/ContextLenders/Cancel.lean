-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Call
import SeLe4n.Kernel.ContextLenders.Timer
import SeLe4n.Kernel.KernelRecords.Dispatch

/-! # seL4's `cancelIPC` keeps the lenders' flow

WS-SX SX8.  The IPC cancel a suspend, a reply holder's cancel and the
finalisation run (`cancelIpcKeepingContexts`, seL4-MCS's `cancelIPC` with
`reply_remove_tcb` first) only removes: the head cut
(`cutHeadFrameKeepingContext`), the endpoint and notification dequeues, the
restore, the donation return, the frame cut and the caller consume.  Each is a
links shrink (`contextStackLinksShrink`), so the cancel is a `LendersFrame` with
no premise but the store's invariant, which each step's records frame carries
(`RecordsStep`). -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace LendersFrame

theorem of_shrink {st st' : SystemState} (L : contextStackLinksShrink st st')
    (h : st'.objects.invExt) : LendersFrame st st' := ⟨L, h⟩

theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) : LendersFrame st (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) := by
  have key : ∀ (k : SeLe4n.ObjId) (o : KernelObject), (∀ x, o ≠ .endpoint x) → (∀ x, o ≠ .tcb x) →
      (SeLe4n.Kernel.removeFromBlockingEndpoint st t e).objects[k]? = some o →
        st.objects[k]? = some o := fun k o hE hT h =>
    (spliceOutMidQueueNode_nonTcb st t hInv k o hT).mp
      ((removeFromBlockingEndpoint_nonEndpoint st t e
        (spliceOutMidQueueNode_preserves_objects_invExt st t hInv) k o hE).mp h)
  exact of_shrink (chainObjectsKept.linksShrink
      ⟨fun x r h => key x _ (fun _ e => by cases e) (fun _ e => by cases e) h,
       fun x sc h => key x _ (fun _ e => by cases e) (fun _ e => by cases e) h⟩)
    (removeFromBlockingEndpoint_preserves_objects_invExt st t e hInv)

theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersFrame st (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) :=
  of_shrink (chainObjectsKept.linksShrink
      ⟨fun x r h => (removeFromNotificationWaitQueue_other_slot st t hInv x _
          (fun _ e => by cases e) (fun _ e => by cases e)).mp h,
       fun x sc h => (removeFromNotificationWaitQueue_other_slot st t hInv x _
          (fun _ e => by cases e) (fun _ e => by cases e)).mp h⟩)
    (removeFromNotificationWaitQueue_preserves_objects_invExt st t hInv)

theorem restoreToReadyCancelled (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (Lifecycle.Suspend.restoreToReadyCancelled st t) :=
  of_shrink (chainObjectsKept.updateTcb st t _ hInv).linksShrink
    (RecordsStep.restoreToReadyCancelled st t hInv).invExt

theorem unlinkReplyWaiterOpt (st : SystemState) (w : SeLe4n.ThreadId) (s? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersFrame st (st.unlinkReplyWaiterOpt w s?) := by
  cases s? with
  | none => exact refl hInv
  | some s => exact unlinkReplyWaiter st w s hInv

theorem cutThreadReplyFrameOut (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    LendersFrame st (SeLe4n.Kernel.cutThreadReplyFrameOut st t) :=
  of_shrink (cutThreadReplyFrameOut_linksShrink st t hInv)
    (FinaliseFrameAny.cutThreadReplyFrameOut st t hInv).invExt

theorem consumeReplyLink (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) : LendersFrame st (Lifecycle.Suspend.consumeReplyLink st c t) := by
  refine of_shrink ?_ (FinaliseFrameAny.consumeReplyLink st c t hInv).invExt
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact .refl _
  · exact consumeCallerReplyLink_linksShrink st c _ hInv

theorem returnDonationToCancelledCaller (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    LendersFrame st (Lifecycle.Suspend.returnDonationToCancelledCaller st c t) := by
  refine of_shrink ?_ (FinaliseFrameAny.returnDonationToCancelledCaller st c t hInv).invExt
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · split
    · rename_i hOk
      obtain ⟨_, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      exact returnDonatedSchedContext_linksShrink hInv hPop
    · exact .refl _
  · exact .refl _

theorem cutCancelledCallerHead (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    LendersFrame st (Lifecycle.Suspend.cutCancelledCallerHead st t) := by
  refine of_shrink ?_ (RecordsFrame.cutCancelledCallerHead st t hInv).invExt
  unfold Lifecycle.Suspend.cutCancelledCallerHead
  split
  · unfold Lifecycle.Suspend.cutThreadHeadFrameKeepingContext
    split
    · exact .refl _
    · exact cutHeadFrameKeepingContext_linksShrink st _ hInv
  · exact .refl _

/-- **The IPC teardown is a links shrink**: every arm of `cancelIpcBlocking`. -/
theorem cancelIpcBlocking (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) : LendersFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
  cases hB : tcb.ipcState with
  | ready => unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]; exact refl hInv
  | blockedOnSend e | blockedOnReceive e | blockedOnCall e =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    exact (removeFromBlockingEndpoint st t e hInv).andThen fun h => restoreToReadyCancelled _ t h
  | blockedOnReply ep rt =>
    rw [cancelIpcBlocking_replyArm_unfold st t tcb hB]
    exact ((((returnDonationToCancelledCaller st t tcb hInv).andThen fun h =>
      cutThreadReplyFrameOut _ tcb h).andThen fun h => restoreToReadyCancelled _ t h).andThen
        fun h => consumeReplyLink _ t tcb h).andThen fun h => unlinkReplyWaiterOpt _ t _ h
  | blockedOnNotification n =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    exact (removeFromNotificationWaitQueue st t hInv).andThen fun h => restoreToReadyCancelled _ t h

/-- **seL4-MCS's `cancelIPC` as the suspend runs it**: the head cut, then the
teardown. -/
theorem cancelIpcKeepingContexts (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    LendersFrame st (Lifecycle.Suspend.cancelIpcKeepingContexts st t tcb) :=
  (cutCancelledCallerHead st tcb hInv).andThen fun h => cancelIpcBlocking _ t tcb h

theorem propagatePipChainCrossCore (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    LendersFrame st (PriorityInheritance.propagatePipChainCrossCore st t ec fuel).1 :=
  of_kept (chainObjectsKept.propagatePipChainCrossCore st t ec fuel hInv)
    (RecordsFrame.propagatePipChainCrossCore st t ec fuel hInv)

/-- The suspend's cancel and its priority revert. -/
theorem suspendCancelRevert (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (ec : CoreId)
    (hInv : st.objects.invExt) :
    LendersFrame st (Lifecycle.Suspend.suspendCancelRevert st t tcb ec) := by
  unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
  · exact (cancelIpcKeepingContexts st t tcb hInv).andThen fun h => propagatePipChainCrossCore _ _ ec _ h
  · exact cancelIpcKeepingContexts st t tcb hInv

/-- **A reply holder's cancel** (seL4-MCS `cancelIPC` on the reply's holder):
the suspend's cancel and revert, then the `Inactive` write. -/
theorem cancelReplyHolder (st : SystemState) (holder : SeLe4n.ThreadId) (ec : CoreId)
    (hInv : st.objects.invExt) : LendersFrame st (SeLe4n.Kernel.cancelReplyHolder st holder ec) := by
  rcases cancelReplyHolder_cases st holder ec with e | ⟨tcb, -, -, e⟩ <;> rw [e]
  · exact refl hInv
  · exact (suspendCancelRevert st holder tcb ec hInv).andThen fun h =>
      of_shrink (chainObjectsKept.updateTcb _ holder _ h).linksShrink
        (SystemState.updateTcb_preserves_objects_invExt _ _ _ h)

end LendersFrame

end SeLe4n.Kernel
