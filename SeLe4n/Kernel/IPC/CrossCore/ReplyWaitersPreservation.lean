-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.Invariant.ReplyWaitersFrame

/-!
# The IPC transitions keep the reply-waiter queues consistent (WS-ZA ZA4.6)

Each transition that blocks a thread on a reply links it into its server's
queue in the same step, and each that ends the block unlinks it; every other
write in the transition keeps the reply views (`IPC.Invariant.ReplyWaitersFrame`).
So the view the transition leaves is a `LinkStep` or an `UnlinkStep` of the one
it found, and the queues stay consistent.

The hypotheses are pre-state facts the IPC invariant gives: the caller runs, so
it waits on no server, and a thread blocked on receive waits on none either.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId)

/-- Thread `t` waits on no server in the views (or has none). -/
def _root_.SeLe4n.Model.ReplyViews.serverFree (V : ReplyViews) (t : SeLe4n.ThreadId) : Prop :=
  ∀ v, V t.toObjId = some v → v.server = none

/-- A thread a `modifyTcb` resolves has a view. -/
theorem replyViews_some_of_modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId}
    {f : TCB → TCB} (h : modifyTcb st t f = .ok st') : ∃ v, st.replyViews t.toObjId = some v := by
  obtain ⟨tcb, hL, -⟩ := modifyTcb_ok_decompose h
  exact ⟨_, replyViews_of_tcb (lookupTcb_some_objects st t tcb hL)⟩

theorem _root_.SeLe4n.Model.ReplyViews.serverFree_setServer_none (V : ReplyViews) (t : SeLe4n.ThreadId) :
    ReplyViews.serverFree (V.setServer t none) t := by
  intro v hv
  unfold ReplyViews.setServer ReplyViews.mapAt at hv
  rw [if_pos rfl] at hv
  cases h : V t.toObjId with
  | none => rw [h] at hv; cases hv
  | some u => rw [h] at hv; cases hv; rfl

theorem migrateSchedContextReplenishment_replyViews_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (a b : CoreId) :
    (migrateSchedContextReplenishment st scId a b).replyViews = st.replyViews := by
  unfold migrateSchedContextReplenishment; split <;> rfl

theorem cleanupPreReceiveDonationMigrated_replyViews_eq {st st' : SystemState}
    {r : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : cleanupPreReceiveDonationMigrated st r = .ok st') : st'.replyViews = st.replyViews := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  rw [← cleanupPreReceiveDonationChecked_replyViews_eq hInv hC]
  unfold preReceiveReturnMigration; split
  · exact migrateSchedContextReplenishment_replyViews_eq _ _ _ _
  · rfl

/-- **The call keeps the reply-waiter queues consistent.**  On a rendezvous the
woken receiver (blocked on receive, so waiting on no server) becomes the
caller's server and the caller joins its queue: a `LinkStep`.  With no receiver
the caller blocks on the send queue and waits on no server. -/
theorem endpointCallOnCore_preserves_replyWaitersConsistent (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hCaller : ReplyViews.serverFree st.replyViews caller)
    (hHead : ∀ ep r, st.objects[endpointId]? = some (.endpoint ep) → ep.receiveQ.head = some r →
      r ≠ caller ∧ ReplyViews.serverFree st.replyViews r) :
    (endpointCallOnCore endpointId caller msg c st).1.replyWaitersConsistent := by
  unfold endpointCallOnCore
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
      · rename_i receiver _tcb st' hPop
        have hRr : receiver = r :=
          endpointQueuePopHead_popped_eq_head _ _ _ _ ep _ _ _ hObj (by simpa using hR) hPop
        subst hRr
        obtain ⟨hne, hRF⟩ := hHead ep receiver hObj hR
        have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
        have hV1 := endpointQueuePopHead_replyViews_eq hInv hPop
        split
        · exact hC
        · rename_i st'' hStore
          have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hStore
          have hV2 : st''.replyViews = st.replyViews := by
            rw [replyViews_storeTcbIpcStateAndMessage hI1 hStore, hV1]
            exact ReplyViews.setServer_of_server hRF
          have hV3 : (wakeThread st'' receiver c).1.replyViews = st.replyViews := by
            rw [wakeThread_replyViews_eq _ _ _ hI2 (by rw [hV2]; exact hRF), hV2]
          obtain ⟨vs0, hS0⟩ := replyViews_some_of_modifyTcb hStore
          rw [hV1] at hS0
          split
          · exact hC
          · rename_i st4 hCS
            have hI4 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _
              (wakeThread_preserves_objects_invExt _ _ _ hI2) hCS
            obtain ⟨vw0, hW0⟩ := replyViews_some_of_modifyTcb hCS
            rw [hV3] at hW0
            have hV4 : st4.replyViews = ReplyViews.setServer st.replyViews caller (some receiver) := by
              rw [replyViews_storeTcbIpcStateAndMessage
                (wakeThread_preserves_objects_invExt _ _ _ hI2) hCS, hV3]; rfl
            split
            · exact hC
            · rename_i st5 hLk
              show ReplyViews.consistent _
              rw [replyViews_linkReplyWaiter, removeRunnableOnCore_replyViews_eq,
                linkServerStashedReply_replyViews_eq hI4 hLk, hV4]
              exact (ReplyViews.linkStep_of_link hC hW0 (hCaller _ hW0) hS0 (hRF _ hS0)
                (Ne.symm hne)).consistent hC
    · split
      · exact hC
      · rename_i st' hEnq
        have hI1 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hInv hEnq
        split
        · exact hC
        · rename_i st'' hStore
          show ReplyViews.consistent _
          rw [removeRunnableOnCore_replyViews_eq, replyViews_storeTcbIpcStateAndMessage hI1 hStore,
            endpointQueueEnqueue_replyViews_eq hInv hEnq]
          exact (ReplyViews.setServer_of_server hCaller).symm ▸ hC
  · split <;> exact hC

theorem _root_.SeLe4n.Model.ReplyViews.serverFree_setServer_ne {V : ReplyViews}
    {t y : SeLe4n.ThreadId} {srv : Option SeLe4n.ThreadId} (hy : y ≠ t)
    (h : ReplyViews.serverFree V y) : ReplyViews.serverFree (V.setServer t srv) y := by
  intro v hv
  unfold ReplyViews.setServer at hv; rw [ReplyViews.mapAt_ne _ _ hy] at hv
  exact h v hv

theorem _root_.SeLe4n.Model.ReplyViews.setServer_apply_ne {V : ReplyViews}
    {t y : SeLe4n.ThreadId} {srv : Option SeLe4n.ThreadId} (hy : y ≠ t) :
    (V.setServer t srv) y.toObjId = V y.toObjId := by
  unfold ReplyViews.setServer; rw [ReplyViews.mapAt_ne _ _ hy]

/-- **The receive keeps the reply-waiter queues consistent.**  A calling sender
popped off the send queue becomes the receiver's reply waiter: a `LinkStep`.
Any other rendezvous readies a sender and the receiver, both waiting on no
server; the block waits on no server either. -/
theorem endpointReceiveDualOnCore_preserves_replyWaitersConsistent (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent)
    (hRecv : ReplyViews.serverFree st.replyViews receiver)
    (hHead : ∀ ep s, st.objects[endpointId]? = some (.endpoint ep) → ep.sendQ.head = some s →
      s ≠ receiver ∧ ReplyViews.serverFree st.replyViews s) :
    (endpointReceiveDualOnCore endpointId receiver replyId c st).1.replyWaitersConsistent := by
  unfold endpointReceiveDualOnCore
  split
  · rename_i ep hEp
    have hObj := (getEndpoint?_eq_some_iff st endpointId ep).1 hEp
    split
    · rename_i s hS
      split
      · exact hC
      · rename_i sender senderTcb st' hPop
        have hSs : sender = s :=
          endpointQueuePopHead_popped_eq_head _ _ _ _ ep _ _ _ hObj (by simpa using hS) hPop
        subst hSs
        obtain ⟨hne, hSF⟩ := hHead ep sender hObj hS
        have hI1 := endpointQueuePopHead_preserves_objects_invExt _ _ _ _ _ _ hInv hPop
        have hV1 := endpointQueuePopHead_replyViews_eq hInv hPop
        dsimp only
        split
        · rw [if_pos rfl]
          split
          · exact hC
          · rename_i st'' hStore
            have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hStore
            obtain ⟨vw0, hW0⟩ := replyViews_some_of_modifyTcb hStore
            rw [hV1] at hW0
            have hV2 : st''.replyViews = ReplyViews.setServer st.replyViews sender (some receiver) := by
              rw [replyViews_storeTcbIpcStateAndMessage hI1 hStore, hV1]; rfl
            split
            · exact hC
            · rename_i rid
              split
              · exact hC
              · rename_i stL hL
                have hIL := linkCallerReply_objects_invExt hI2 hL
                have hVL := (linkCallerReply_replyViews_eq hI2 hL).trans hV2
                split
                · rename_i st3 hR
                  obtain ⟨vs0, hS0⟩ := replyViews_some_of_modifyTcb hR
                  rw [hVL, ReplyViews.setServer_apply_ne (Ne.symm hne)] at hS0
                  show ReplyViews.consistent _
                  rw [replyViews_linkReplyWaiter, replyViews_storeTcbIpcStateAndMessage hIL hR, hVL]
                  show ReplyViews.consistent
                    (ReplyViews.link (ReplyViews.setServer _ receiver none) sender receiver)
                  rw [ReplyViews.setServer_of_server
                    (ReplyViews.serverFree_setServer_ne (Ne.symm hne) hRecv)]
                  exact (ReplyViews.linkStep_of_link hC hW0 (hSF _ hW0) hS0 (hRecv _ hS0)
                    hne).consistent hC
                · exact hC
        · rw [if_neg Bool.false_ne_true]
          split
          · exact hC
          · rename_i st'' hStore
            have hI2 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI1 hStore
            have hV2 : st''.replyViews = st.replyViews := by
              rw [replyViews_storeTcbIpcStateAndMessage hI1 hStore, hV1]
              exact ReplyViews.setServer_of_server hSF
            have hV3 : (wakeThread st'' sender c).1.replyViews = st.replyViews := by
              rw [wakeThread_replyViews_eq _ _ _ hI2 (by rw [hV2]; exact hSF), hV2]
            split
            · rename_i st4 hR
              refine replyWaitersConsistent.of_views ?_ hC
              rw [replyViews_storeTcbIpcStateAndMessage
                (wakeThread_preserves_objects_invExt _ _ _ hI2) hR, hV3]
              exact ReplyViews.setServer_of_server hRecv
            · exact hC
    · split
      · exact hC
      · rename_i stClean hClean
        have hI1 := cleanupPreReceiveDonationMigrated_preserves_objects_invExt _ _ _ hInv hClean
        have hV1 := cleanupPreReceiveDonationMigrated_replyViews_eq hInv hClean
        split
        · exact hC
        · rename_i st' hEnq
          have hI2 := endpointQueueEnqueue_preserves_objects_invExt _ _ _ _ _ hI1 hEnq
          have hV2 := (endpointQueueEnqueue_replyViews_eq hI1 hEnq).trans hV1
          split
          · exact hC
          · rename_i st'' hStore
            have hI3 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hI2 hStore
            have hV3 : st''.replyViews = st.replyViews := by
              rw [replyViews_storeTcbIpcStateAndMessage hI2 hStore, hV2]
              exact ReplyViews.setServer_of_server hRecv
            split
            · refine replyWaitersConsistent.of_views ?_ hC
              rw [removeRunnableOnCore_replyViews_eq, hV3]
            · rename_i rTcb hT
              split
              · split
                · exact hC
                · rename_i stS hSt
                  refine replyWaitersConsistent.of_views ?_ hC
                  rw [removeRunnableOnCore_replyViews_eq, replyViews_storeTcb_eq hI3 hT hSt rfl, hV3]
              · exact hC
  · split <;> exact hC

/-- **The reply keeps the reply-waiter queues consistent.**  The answered thread
leaves its server's queue as its block ends: an `UnlinkStep`.  No hypothesis:
the reply reads the server off the answered thread's own block. -/
theorem endpointReplyOnCore_preserves_replyWaitersConsistent (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hC : st.replyWaitersConsistent) :
    (endpointReplyOnCore replier target msg c st).1.replyWaitersConsistent := by
  unfold endpointReplyOnCore
  split
  · exact hC
  split
  · exact hC
  split
  · exact hC
  · rename_i tcb hL
    have hO := lookupTcb_some_objects st target tcb hL
    split
    · rename_i ep rt hIpc
      split
      · exact hC
      · rename_i server
        have hW0 := replyViews_of_tcb hO
        have hWSrv : tcb.replyView.server = some server := by
          show tcb.blockingServer? = some server
          rw [blockingServer?_eq_ipcServer?, hIpc]; rfl
        obtain ⟨vs0, hS0⟩ := hC.2.1 target _ server hW0 hWSrv
        have hU := (ReplyViews.unlinkStep_of_unlink hC hW0 hWSrv hS0).consistent hC
        split
        · exact hC
        · rename_i st' hStore
          have hI1 := storeTcbIpcStateAndMessage_fromTcb_objects_invExt hInv hStore
          have hV1 := replyViews_storeTcbIpcStateAndMessage_fromTcb hInv hO hStore
          have hV2 : (wakeThread st' target c).1.replyViews = ReplyViews.setServer st.replyViews target none := by
            rw [wakeThread_replyViews_eq _ _ _ hI1 (by
              rw [hV1]; exact ReplyViews.serverFree_setServer_none _ _), hV1]; rfl
          split
          · show ReplyViews.consistent _
            rw [replyViews_unlinkReplyWaiter, hV2]; exact hU
          · split
            · rename_i st'' hRm
              show ReplyViews.consistent _
              rw [replyViews_unlinkReplyWaiter, removeCallerReplyFrame_replyViews_eq
                (wakeThread_preserves_objects_invExt _ _ _ hI1) hRm, hV2]
              exact hU
            · exact hC
    · exact hC

end SeLe4n.Kernel
