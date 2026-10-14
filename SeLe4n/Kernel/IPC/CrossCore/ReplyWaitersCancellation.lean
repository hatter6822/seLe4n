-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersPreservation
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape

/-!
# Cancellation keeps the reply-waiter queues consistent (WS-ZA ZA4.6)

A cancelled thread blocked on a reply leaves its server's queue as its block
ends (`unlinkReplyWaiterOpt`, an `UnlinkStep`); a thread blocked on anything
else waited on no server, and readying it moves no view.  Every other write of
the teardown (the queue sweeps, the donation return, the reply-frame splice and
consume, the deschedules) keeps the views.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.Lifecycle.Suspend

theorem replyView_of_tcbQueueLinkRewrite {a b : TCB} (h : tcbQueueLinkRewrite a b) :
    a.replyView = b.replyView := by
  obtain ⟨_, _, _, _, _, rfl⟩ := h; rfl

theorem replyView_of_tcbNtfnLinkRewrite {a b : TCB} (h : tcbNtfnLinkRewrite a b) :
    a.replyView = b.replyView := by
  obtain ⟨_, _, rfl⟩ := h; rfl

theorem spliceOutMidQueueNode_replyViews_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : (spliceOutMidQueueNode st tid).replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun k t0 hk => by
      obtain ⟨t', h', hR⟩ := spliceOutMidQueueNode_tcb_lookup st tid k t0 hInv hk
      exact ⟨t', h', replyView_of_tcbQueueLinkRewrite hR⟩)
    (fun k t' hk => by
      obtain ⟨t0, h0, -⟩ := spliceOutMidQueueNode_tcb_backward st tid k t' hInv hk
      exact ⟨t0, h0⟩)

theorem removeFromAllEndpointQueues_replyViews_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (removeFromAllEndpointQueues st tid).replyViews = st.replyViews := by
  have hS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  rw [← spliceOutMidQueueNode_replyViews_eq st tid hInv]
  exact replyViews_eq_of_tcbs
    (fun k t0 hk => ⟨t0, removeFromAllEndpointQueues_tcb_frame st tid hS k t0 hk, rfl⟩)
    (fun k t' hk => ⟨t', removeFromAllEndpointQueues_tcb_source st tid hS k t' hk⟩)

theorem removeFromNotificationWaitQueue_replyViews_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (removeFromNotificationWaitQueue st tid).replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun k t0 hk => by
      obtain ⟨t', h', hR⟩ := removeFromNotificationWaitQueue_tcb_forward st tid k t0 hInv hk
      exact ⟨t', h', replyView_of_tcbNtfnLinkRewrite hR⟩)
    (fun k t' hk => by
      obtain ⟨t0, h0, -⟩ := removeFromNotificationWaitQueue_tcb_backward st tid k t' hInv hk
      exact ⟨t0, h0⟩)

/-- **The cancellation restore readies the thread**: it clears the thread's
server and nothing else a view reads. -/
theorem restoreToReadyCancelled_replyViews (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (restoreToReadyCancelled st tid).replyViews = ReplyViews.setServer st.replyViews tid none := by
  unfold restoreToReadyCancelled restoreToReadyStaging SystemState.updateTcb
  split
  · rename_i t hT _
    have hO := (getTcb?_eq_some_iff st tid t).1 hT
    funext x
    rw [replyViews_rewriteObject _ _ _ _ hInv]
    unfold ReplyViews.setServer ReplyViews.mapAt
    split
    · rename_i hx; subst hx
      rw [replyViews_of_tcb hO]
      simp only [objReplyView_tcb, Option.map_some]
      simp only [TCB.replyView, TCB.restoredToReady, TCB.withReturnFrame, TCB.blockingServer?]
    · rfl
  · rename_i hN
    have hV : st.replyViews tid.toObjId = none := by
      cases hv : st.replyViews tid.toObjId with
      | none => rfl
      | some v =>
        obtain ⟨t, hO, -⟩ := tcb_of_replyViews hv
        have := (getTcb?_eq_some_iff st tid t).2 hO
        rw [SystemState.getTcbWitnessed?_eq_some this] at hN; cases hN
    exact (ReplyViews.setServer_of_server (fun v hv => by rw [hV] at hv; cases hv)).symm

theorem consumeReplyLink_replyViews_eq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) : (consumeReplyLink st tid tcb).replyViews = st.replyViews := by
  unfold consumeReplyLink
  split
  · rfl
  · rename_i rid _
    exact consumeCallerReply_replyViews_eq hInv (SystemState.consumeCallerReply_eq_link st tid rid)

theorem spliceThreadReplyFrameOut_replyViews_eq (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) : (spliceThreadReplyFrameOut st tcb).replyViews = st.replyViews := by
  unfold spliceThreadReplyFrameOut
  split
  · rfl
  · exact spliceReplyFrameOutOrSelf_replyViews_eq _ _ hInv

/-- The holder's abort ends a send or call, which waits on no server. -/
theorem abortHolderPendingIpc_replyViews_eq (st : SystemState) (holder : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : (abortHolderPendingIpc st holder).replyViews = st.replyViews := by
  unfold abortHolderPendingIpc
  split
  · rfl
  · rename_i htcb hL
    split
    all_goals first
      | rfl
      | (split
         · rename_i st' hA
           obtain ⟨v, hW, hV, hSrv⟩ := abortPendingIpcOnEndpoint_replyViews hInv hA
           rw [hV]
           refine ReplyViews.setServer_of_server (fun v' hv' => ?_)
           rw [hW] at hv'; cases hv'
           rw [← hSrv]; unfold timeoutBlockingServerOf?; rw [hL]; unfold timeoutBlockingServer?
           simp_all
         · rfl)

theorem returnDonationToCancelledCaller_replyViews_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    (returnDonationToCancelledCaller st tid tcb).replyViews = st.replyViews := by
  unfold returnDonationToCancelledCaller
  split
  · rename_i scId holder _ _ _
    split
    · rename_i st' hR
      exact (returnDonatedSchedContextResolved_replyViews_eq
        (abortHolderPendingIpc_preserves_objects_invExt st holder hInv) hR).trans
        (abortHolderPendingIpc_replyViews_eq st holder hInv)
    · rfl
  · rfl

theorem replyViews_unlinkReplyWaiterOpt (st : SystemState) (w : SeLe4n.ThreadId)
    (s? : Option SeLe4n.ThreadId) :
    (st.unlinkReplyWaiterOpt w s?).replyViews =
      match s? with
      | some s => ReplyViews.unlink st.replyViews w s
      | none => st.replyViews := by
  cases s? with
  | none => rfl
  | some s => exact replyViews_unlinkReplyWaiter st w s

/-- **The teardown keeps the reply-waiter queues consistent**, for the thread's
own TCB. -/
theorem cancelIpcBlocking_preserves_replyWaitersConsistent (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hT : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent) :
    (cancelIpcBlocking st tid tcb).replyWaitersConsistent := by
  have hW0 : st.replyViews tid.toObjId = some tcb.replyView :=
    replyViews_of_tcb ((getTcb?_eq_some_iff st tid tcb).1 hT)
  have hReady : ∀ st' : SystemState, st'.replyViews = st.replyViews → tcb.blockingServer? = none →
      (ReplyViews.setServer st'.replyViews tid none) = st.replyViews := by
    intro st' h hN; rw [h]
    exact ReplyViews.setServer_of_server (fun v hv => by rw [hW0] at hv; cases hv; exact hN)
  unfold cancelIpcBlocking
  split
  · exact hC
  all_goals rename_i hIpc
  all_goals first
    | (refine replyWaitersConsistent.of_views ?_ hC
       rw [restoreToReadyCancelled_replyViews _ _ (removeFromAllEndpointQueues_preserves_objects_invExt _ _ hInv)]
       exact hReady _ (removeFromAllEndpointQueues_replyViews_eq _ _ hInv)
         (by simp [TCB.blockingServer?, hIpc]))
    | (refine replyWaitersConsistent.of_views ?_ hC
       rw [restoreToReadyCancelled_replyViews _ _ (removeFromNotificationWaitQueue_preserves_objects_invExt _ _ hInv)]
       exact hReady _ (removeFromNotificationWaitQueue_replyViews_eq _ _ hInv)
         (by simp [TCB.blockingServer?, hIpc]))
    | skip
  -- The reply arm.
  have hI1 := returnDonationToCancelledCaller_preserves_objects_invExt st tid tcb hInv
  have hI2 := spliceThreadReplyFrameOut_preserves_objects_invExt _ tcb hI1
  have hI3 := restoreToReadyCancelled_invExt _ tid hI2
  have hV3 : (restoreToReadyCancelled (spliceThreadReplyFrameOut
      (returnDonationToCancelledCaller st tid tcb) tcb) tid).replyViews =
      ReplyViews.setServer st.replyViews tid none := by
    rw [restoreToReadyCancelled_replyViews _ _ hI2, spliceThreadReplyFrameOut_replyViews_eq _ _ hI1,
      returnDonationToCancelledCaller_replyViews_eq _ _ _ hInv]
  show ReplyViews.consistent _
  rw [replyViews_unlinkReplyWaiterOpt, consumeReplyLink_replyViews_eq _ _ _ hI3, hV3]
  cases hS : tcb.blockingServer? with
  | none =>
    simp only []
    rw [ReplyViews.setServer_of_server (fun v hv => by rw [hW0] at hv; cases hv; exact hS)]
    exact hC
  | some s =>
    simp only []
    obtain ⟨vs0, hS0⟩ := hC.2.1 tid _ s hW0 hS
    exact (ReplyViews.unlinkStep_of_unlink hC hW0 hS hS0).consistent hC

theorem descheduleAtPlacement_replyViews_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (descheduleAtPlacement st tid).replyViews = st.replyViews := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_replyViews_eq _ _ _
  · rfl

theorem descheduleUnboundHolder_replyViews_eq (stPre stPost : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) :
    (descheduleUnboundHolder stPre stPost victim tcb).replyViews = stPost.replyViews := by
  unfold descheduleUnboundHolder
  split
  · rfl
  · exact descheduleAtPlacement_replyViews_eq _ _

theorem cancelIpcBlockingMigrated_replyViews_eq (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) :
    (cancelIpcBlockingMigrated victim tcb st).replyViews = (cancelIpcBlocking st victim tcb).replyViews := by
  unfold cancelIpcBlockingMigrated
  split
  · exact migrateSchedContextReplenishment_replyViews_eq _ _ _ _
  · rfl

/-- **The per-core cancellation keeps the reply-waiter queues consistent.** -/
theorem cancelIpcBlockingOnCore_preserves_replyWaitersConsistent (victim : SeLe4n.ThreadId)
    (tcb : TCB) (c : CoreId) (st : SystemState) (hT : st.getTcb? victim = some tcb)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent) :
    (cancelIpcBlockingOnCore victim tcb c st).1.replyWaitersConsistent := by
  refine replyWaitersConsistent.of_views ?_
    (cancelIpcBlocking_preserves_replyWaitersConsistent st victim tcb hT hInv hC)
  unfold cancelIpcBlockingOnCore cancelIpcBlockingReclaimed
  rw [descheduleThread_state_eq, descheduleAtPlacement_replyViews_eq,
    descheduleUnboundHolder_replyViews_eq, cancelIpcBlockingMigrated_replyViews_eq]

end SeLe4n.Kernel
