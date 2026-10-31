-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.IPC.Invariant.TimeoutAbortPreservation

/-!
# The IPC teardown's placement frame

The cancellation teardown (`Lifecycle.Suspend.cancelIpcBlocking`) rewrites
TCBs, but never a thread's placement fields (`TCB.placement`: its affinity and
its run-queue links).  Stated per step and then for the whole teardown, below
the cross-core cancellation module, because that module resolves the victim's
placement on the post-teardown state and the run-queue membership it reads
lives in those links (WS-ZA ZA4.5).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- WS-ZA ZA4.6: what no step of the cancellation reads or writes beside the
blocking state: a thread's placement (home core and run-queue links) and its
reply-waiter links.  The frames below are stated over this pair so the
placement and the reply-waiter links carry through one proof. -/
def _root_.SeLe4n.Model.TCB.linkFrame (t : TCB) :=
  (t.placement, t.replyWaiterPrevCode, t.replyWaiterNextCode, t.replyWaitersHeadCode,
    t.replyWaitersCount)

theorem _root_.SeLe4n.Model.TCB.map_placement_of_linkFrame {o o' : Option TCB}
    (h : o.map TCB.linkFrame = o'.map TCB.linkFrame) :
    o.map TCB.placement = o'.map TCB.placement := by
  cases o <;> cases o' <;> simp_all [TCB.linkFrame]

/-- The reply-waiter link codes, as one tuple. -/
def _root_.SeLe4n.Model.TCB.replyLinkCodes (t : TCB) : Nat × Nat × Nat × Nat :=
  (t.replyWaiterPrevCode, t.replyWaiterNextCode, t.replyWaitersHeadCode, t.replyWaitersCount)

theorem _root_.SeLe4n.Model.TCB.map_replyLinkCodes_of_linkFrame {o o' : Option TCB}
    (h : o.map TCB.linkFrame = o'.map TCB.linkFrame) :
    o.map TCB.replyLinkCodes = o'.map TCB.replyLinkCodes := by
  cases o <;> cases o' <;> simp_all [TCB.linkFrame, TCB.replyLinkCodes]

/-- Two states whose lookups agree on `w`'s link frame agree on `w`'s
reply-waiter neighbour codes. -/
theorem _root_.SeLe4n.Model.SystemState.replyNeighbourCodes_of_linkFrame
    {a b : SystemState} {w : SeLe4n.ThreadId}
    (h : (a.getTcb? w).map TCB.linkFrame = (b.getTcb? w).map TCB.linkFrame) :
    a.replyPrevCode w = b.replyPrevCode w ∧ a.replyNextCode w = b.replyNextCode w := by
  rw [SystemState.replyPrevCode_eq_getTcb?, SystemState.replyPrevCode_eq_getTcb?,
    SystemState.replyNextCode_eq_getTcb?, SystemState.replyNextCode_eq_getTcb?]
  revert h
  cases a.getTcb? w <;> cases b.getTcb? w <;> simp_all [TCB.linkFrame]

/-- WS-RR RR8.11: the restore rewrites the victim's own TCB and writes nothing
where no TCB was. -/
private theorem restoreToReadyStaging_linkFrame_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.restoreToReadyStaging st tid frame).getTcb? x).map TCB.linkFrame
      = (st.getTcb? x).map TCB.linkFrame := by
  cases hT : st.getTcb? tid with
  | none =>
    rw [Lifecycle.Suspend.restoreToReadyStaging_eq_self_of_getTcb?_none st tid frame hT]
  | some tcb =>
    by_cases hk : x = tid
    · subst hk
      have hPost : (Lifecycle.Suspend.restoreToReadyStaging st x frame).getTcb? x
          = some (restoredTcb tcb frame) := by
        rw [restoreToReadyStaging_eq]
        simp only [hT]
        exact (SystemState.getTcb?_eq_some_iff _ x _).mpr
          (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects x.toObjId _ hInv)
      rw [hPost, hT]
      cases frame with
      | none => simp [restoredTcb, TCB.placement, TCB.linkFrame]
      | some f => simp [restoredTcb, TCB.withReturnFrame, TCB.placement, TCB.linkFrame]
    · have hPost : (Lifecycle.Suspend.restoreToReadyStaging st tid frame).getTcb? x
          = st.getTcb? x := by
        unfold SystemState.getTcb?
        rw [restoreToReadyStaging_objects_ne st tid frame x.toObjId hInv
          (fun hc => hk (SeLe4n.ThreadId.toObjId_injective x tid hc))]
      rw [hPost]

/-- WS-RR RR8.11: a store of one TCB at a key that already held a TCB with the same
`TCB.placement` frames every thread's home core and run-queue links. -/
private theorem storeObject_tcb_linkFrame_frame {st st' : SystemState} {k : SeLe4n.ObjId}
    {t t' : TCB}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.tcb t))
    (hAff : t'.linkFrame = t.linkFrame)
    (hStore : storeObject k (.tcb t') st = .ok ((), st')) (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.linkFrame = (st.getTcb? x).map TCB.linkFrame := by
  by_cases hk : x.toObjId = k
  · subst hk
    rw [show st'.getTcb? x = some t' from
        (SystemState.getTcb?_eq_some_iff _ x t').mpr
          (storeObject_objects_eq' st x.toObjId (.tcb t') ((), st') hInv hStore),
      show st.getTcb? x = some t from (SystemState.getTcb?_eq_some_iff st x t).mpr hPre]
    simp [hAff]
  · unfold SystemState.getTcb?
    rw [storeObject_objects_ne st st' k x.toObjId (.tcb t') hk hInv hStore]

/-- WS-RR RR8.11: the guarded endpoint-queue removal patches queue links only, in
**both** directions — the `FieldRefines` pair WS-OD OD1.4 built, whose backward half
is what says the removal materialises no thread. -/
theorem endpointQueueRemove_map_frame {α : Type} (f : TCB → α)
    (hLinkFree : ∀ (t : TCB) (qp qpp qn : Nat),
      f { t with queuePrevCode := qp, queuePPrevCode := qpp, queueNextCode := qn } = f t)
    {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map f = (st.getTcb? x).map f := by
  refine SystemState.map_tcbField_eq_of_refines f (fun t0 hT0 => ?_) (fun t' hT' => ?_)
  · obtain ⟨ot', hL', hAff'⟩ := endpointQueueRemove_getTcb_upToField f hLinkFree endpointId
      isReceiveQ tid st st' hInv h x.toObjId t0
      (by rw [← RHTable_getElem?_eq_get?]; exact (SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    exact ⟨ot', (SystemState.getTcb?_eq_some_iff _ x ot').mpr
      (by rw [RHTable_getElem?_eq_get?]; exact hL'), hAff'.symm⟩
  · obtain ⟨ot, hL, _⟩ := endpointQueueRemove_getTcb_backward_upToField f hLinkFree
      endpointId isReceiveQ tid st st' hInv h x.toObjId t'
      ((SystemState.getTcb?_eq_some_iff _ x t').mp hT')
    exact ⟨ot, (SystemState.getTcb?_eq_some_iff st x ot).mpr hL⟩

private theorem endpointQueueRemove_linkFrame_frame {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.linkFrame = (st.getTcb? x).map TCB.linkFrame :=
  endpointQueueRemove_map_frame TCB.linkFrame (fun _ _ _ _ => rfl) hInv h x

/-- The queue removal writes queue links alone: every thread's state fields
stay. -/
theorem endpointQueueRemove_stateMono {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    SystemState.StateMono st st' :=
  SystemState.StateMono.of_stateFields
    (endpointQueueRemove_map_frame (fun x => (x.ipcState, x.threadState, x.cpuAffinity)) (fun _ _ _ _ => rfl)
      hInv h)

/-- The IPC abort a timeout or a reclaim runs: the queue removal patches queue
links, and the aborted thread's TCB is stored over itself with the same
placement. -/
theorem abortPendingIpcOnEndpoint_linkFrame_frame {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.linkFrame = (st.getTcb? x).map TCB.linkFrame := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  rw [storeObject_tcb_linkFrame_frame (hInv := hInv1)
        (hPre := lookupTcb_some_objects _ _ _ hLook) (hStore := hStore)
        (hAff := by simp [TCB.withReturnFrame, TCB.placement, TCB.linkFrame]) (x := x),
    endpointQueueRemove_linkFrame_frame hInv hRem x]

theorem abortPendingIpcOnEndpoint_placement_frame {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement :=
  TCB.map_placement_of_linkFrame (abortPendingIpcOnEndpoint_linkFrame_frame hInv hA x)

/-- The abort makes the aborted thread ready and leaves it active. -/
theorem abortPendingIpcOnEndpoint_stateMono {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    SystemState.StateMono st st' := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  refine (endpointQueueRemove_stateMono hInv hRem).trans ?_
  unfold storeObject at hStore; cases hStore
  refine SystemState.StateMono.insert hInv1 rfl ?_
  rw [lookupTcb_some_objects _ _ _ hLook]
  exact SystemState.objStateMono_tcb ⟨fun _ => rfl, fun _ => by
    simp [TCB.Active, TCB.withReturnFrame], rfl⟩

/-- The timeout's abort keeps the table references: the splice's frame, then a
thread stored over the removed thread. -/
theorem abortPendingIpcOnEndpoint_tableReferenceFrame {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    SystemState.TableReferenceFrame st st' := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  exact (endpointQueueRemove_tableReferenceFrame hInv hRem).trans
    (.storeObject hInv1 hStore
      (SystemState.TableReferenceFrame.tcb_over (lookupTcb_some_objects _ _ _ hLook)))

/-- The timeout's abort holds the release queues: the splice's frame, then a
thread stored over the removed thread. -/
theorem abortPendingIpcOnEndpoint_releaseStateAgree {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    SystemState.releaseStateAgree st' st := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  exact (SystemState.releaseStateAgree.storeObject_tcb hInv1 hStore
    (lookupTcb_some_objects _ _ _ hLook)).trans (endpointQueueRemove_releaseStateAgree hInv hRem)

/-- The timeout's abort keeps every context's refill view: the splice writes
no context and the thread is stored over a thread. -/
theorem abortPendingIpcOnEndpoint_refillViewsKept {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    RefillViewsKept st' st := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  exact (RefillViewsKept.storeObject hInv1 hStore (by rw [lookupTcb_some_objects _ _ _ hLook]; rfl)).trans
    (.of_schedContexts_backward (endpointQueueRemove_schedContext_backward _ _ _ _ _ hInv hRem))

/-- WS-ZA ZA6.6: the queue splice keeps every slot's yield codes: it writes
threads over threads with their yield-to codes kept, and no context. -/
theorem endpointQueueRemove_yieldLinksKept (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState) (hInv : st.objects.invExt)
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') : YieldLinksKept st' st :=
  .of_frames
    (fun a t ha => by
      rw [RHTable_getElem?_eq_get?] at ha
      obtain ⟨t', h', e⟩ := endpointQueueRemove_getTcb_upToField TCB.yieldToCode
        (fun _ _ _ _ => rfl) endpointId isReceiveQ tid st st' hInv h a t ha
      exact ⟨t', by rw [RHTable_getElem?_eq_get?]; exact h', e⟩)
    (fun a t' ha => endpointQueueRemove_getTcb_backward_upToField TCB.yieldToCode
      (fun _ _ _ _ => rfl) endpointId isReceiveQ tid st st' hInv h a t' ha)
    (fun a sc ha => endpointQueueRemove_schedContext_forward endpointId isReceiveQ tid st st'
      hInv h a sc ha)
    (fun a sc ha => endpointQueueRemove_schedContext_backward endpointId isReceiveQ tid st st'
      hInv h a sc ha)

/-- ...and so does the timeout's abort: the thread is stored over itself with
its yield-to code kept. -/
theorem abortPendingIpcOnEndpoint_yieldLinksKept {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    YieldLinksKept st' st := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  exact (YieldLinksKept.storeObject hInv1 hStore (by rw [lookupTcb_some_objects _ _ _ hLook]; rfl)).trans
    (endpointQueueRemove_yieldLinksKept _ _ _ _ _ hInv hRem)

/-- ...so it keeps the run queues in agreement with the links. -/
theorem abortPendingIpcOnEndpoint_runQueueStage {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    SystemState.RunQueueStage st st' :=
  have hS := abortPendingIpcOnEndpoint_scheduler_eq epId isReceiveQ tid st st' hA
  SystemState.RunQueueStage.of_placement
    (fun hInv => abortPendingIpcOnEndpoint_preserves_objects_invExt epId isReceiveQ tid st st'
      hInv hA)
    (by rw [hS]) (by rw [hS]) (fun hInv x => abortPendingIpcOnEndpoint_placement_frame hInv hA x)
    (fun hInv => abortPendingIpcOnEndpoint_stateMono hInv hA)
    (fun hInv => abortPendingIpcOnEndpoint_tableReferenceFrame hInv hA)
    (fun hInv => abortPendingIpcOnEndpoint_releaseStateAgree hInv hA)
    (fun hInv => abortPendingIpcOnEndpoint_refillViewsKept hInv hA)
    (fun hInv => abortPendingIpcOnEndpoint_yieldLinksKept hInv hA)

/-- WS-RR RR8.11: the reclaim moves no thread's home core — the pop rebinds
scheduling contexts (`returnDonatedSchedContext_getTcb?_placement_eq`). -/
private theorem returnDonationToCancelledCaller_linkFrame_frame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).getTcb? x).map TCB.linkFrame
      = (st.getTcb? x).map TCB.linkFrame := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => rfl
  | some p =>
    obtain ⟨scId, holder⟩ := p
    cases hT : st.getTcb? v with
    | none => rfl
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved st holder scId v with
      | error _ => rfl
      | ok st' =>
        obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_getTcb?_map_eq TCB.linkFrame (fun _ _ _ => rfl) _ st'
          holder scId v hInv newOwner? hPop x

/-- WS-RR RR8.11: **the consume materialises no thread.**  The backward half the
tree lacked: its two stores are at keys their own lookups found occupied, so a TCB
the post-state holds had a TCB at the same key before. -/
private theorem consumeCallerReply_getTcb?_backward {st st' : SystemState}
    {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st'))
    (x : SeLe4n.ThreadId) (t' : TCB) (hT' : st'.getTcb? x = some t') :
    ∃ t0, st.getTcb? x = some t0 := by
  unfold SystemState.consumeCallerReply at hStep
  cases hCons : SystemState.consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hInv1 := SystemState.consumeReply_preserves_objects_invExt st st1 rid hInv hCons
    have hMid : ∀ (y : SeLe4n.ThreadId) (t : TCB), st1.getTcb? y = some t → st.getTcb? y = some t := by
      intro y t hy
      unfold SystemState.consumeReply at hCons
      cases hG : st.getReply? rid with
      | none => rw [hG] at hCons; cases hCons; exact hy
      | some r0 =>
        rw [hG] at hCons
        by_cases hk : y.toObjId = rid.toObjId
        · exfalso
          have hPost : st1.objects[y.toObjId]? = some (.reply r0.consumed) := by
            rw [hk]; exact storeObject_objects_eq' st _ _ _ hInv hCons
          rw [(SystemState.getTcb?_eq_some_iff st1 y t).mp hy] at hPost
          exact absurd hPost (by simp)
        · refine (SystemState.getTcb?_eq_some_iff st y t).mpr ?_
          rw [← storeObject_objects_ne st st1 rid.toObjId y.toObjId _ hk hInv hCons]
          exact (SystemState.getTcb?_eq_some_iff st1 y t).mp hy
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep] at hT'
      exact ⟨t', hMid x t' hT'⟩
    | some tcb =>
      simp only [hT] at hStep
      by_cases hk : x.toObjId = caller.toObjId
      · refine ⟨tcb, hMid x tcb ?_⟩
        rw [show x = caller from SeLe4n.ThreadId.toObjId_injective x caller hk]
        exact hT
      · refine ⟨t', hMid x t' ?_⟩
        refine (SystemState.getTcb?_eq_some_iff st1 x t').mpr ?_
        rw [← storeObject_objects_ne st1 st' caller.toObjId x.toObjId _ hk hInv1 hStep]
        exact (SystemState.getTcb?_eq_some_iff st' x t').mp hT'

/-- WS-RR RR8.11: the reply-link teardown clears one TCB field and consumes one
Reply, so it frames every projection that ignores the reply link. -/
theorem consumeReplyLink_map_frame {α : Type} (f : TCB → α)
    (hf : ∀ t : TCB, f { t with replyObjectCode := 0 } = f t) (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.consumeReplyLink st tid tcb).getTcb? x).map f
      = (st.getTcb? x).map f := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases hR : tcb.replyObject with
  | none => rfl
  | some rid =>
    have hStep := SystemState.consumeCallerReply_eq_link st tid rid
    refine SystemState.map_tcbField_eq_of_refines f (fun t0 hT0 => ?_)
      (fun t' hT' => consumeCallerReply_getTcb?_backward hInv hStep x t' hT')
    by_cases hk : x.toObjId = tid.toObjId
    · refine ⟨{ t0 with replyObjectCode := 0 }, ?_, hf t0⟩
      refine (SystemState.getTcb?_eq_some_iff _ x _).mpr ?_
      rw [hk]
      exact SystemState.consumeCallerReply_tcb_caller st _ tid rid hInv hStep t0
        (by rw [← hk]; exact (SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    · exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ x t0).mpr
        (SystemState.consumeCallerReply_tcb_other st _ tid rid hInv hStep x.toObjId t0 hk
          ((SystemState.getTcb?_eq_some_iff st x t0).mp hT0)), rfl⟩

/-- **WS-ZA ZA4.6**: the reply arm's prefix — reclaim, splice, restore and the
reply-link teardown — leaves every thread's placement and reply-waiter links
alone; only the final unlink writes reply-waiter links. -/
theorem cancelReplyPrefix_linkFrame (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyStaging
          (spliceThreadReplyFrameOut
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v frame)
        v tcbV).getTcb? x).map TCB.linkFrame
      = (st.getTcb? x).map TCB.linkFrame := by
  have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
    st v tcbV hInv
  have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
    (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
  rw [consumeReplyLink_map_frame TCB.linkFrame (fun _ => rfl) _ v tcbV
      (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS) x,
    restoreToReadyStaging_linkFrame_frame _ v _ hS x,
    spliceThreadReplyFrameOut_getTcb?_eq _ tcbV hR x,
    returnDonationToCancelledCaller_linkFrame_frame st v tcbV hInv x]

/-- **WS-RR RR8.11: the teardown moves no thread's home core.**  The composite of
the per-step frames above, stated in the `Option.map` form so its `none` case is
the statement that the teardown materialises no thread — which is what a reader of
`replenishQueueAffinityConsistentOnCore` needs, since a scheduling context's
`boundThread` is tied to no stored TCB by any invariant. -/
theorem cancelIpcBlocking_placement_frame (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement := by
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => rfl
  | blockedOnSend _ =>
    rw [TCB.map_placement_of_linkFrame (restoreToReadyStaging_linkFrame_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x),
      removeFromAllEndpointQueues_placement_frame st v hInv x]
  | blockedOnReceive _ =>
    rw [TCB.map_placement_of_linkFrame (restoreToReadyStaging_linkFrame_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x),
      removeFromAllEndpointQueues_placement_frame st v hInv x]
  | blockedOnCall _ =>
    rw [TCB.map_placement_of_linkFrame (restoreToReadyStaging_linkFrame_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x),
      removeFromAllEndpointQueues_placement_frame st v hInv x]
  | blockedOnNotification _ =>
    rw [TCB.map_placement_of_linkFrame (restoreToReadyStaging_linkFrame_frame _ v _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv) x),
      removeFromNotificationWaitQueue_placement_frame st v hInv x]
  | blockedOnReply ep rt =>
    rw [(SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks _ v _).getTcb?_map
        TCB.placement (fun _ => rfl) x]
    exact TCB.map_placement_of_linkFrame (cancelReplyPrefix_linkFrame st v tcbV _ hInv x)

/-- **WS-ZA ZA4.5**: the teardown moves no thread's run-queue core. -/
theorem cancelIpcBlocking_runCoresAgree (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.RunCoresAgree (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st := fun y => by
  have h := cancelIpcBlocking_placement_frame st v tcbV hInv y
  revert h
  cases (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getTcb? y <;>
    cases st.getTcb? y <;> simp_all [TCB.placement]

/-- The restore makes its thread ready and leaves it active. -/
theorem restoreToReadyStaging_stateMono (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    SystemState.StateMono st (Lifecycle.Suspend.restoreToReadyStaging st tid frame) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact SystemState.StateMono.updateTcb hInv tid fun x =>
    ⟨fun _ => by cases frame <;> rfl, fun h => by cases frame <;> exact h,
      by cases frame <;> rfl⟩

/-- The reclaim's pop rebinds scheduling contexts and blocks no thread. -/
private theorem returnDonationToCancelledCaller_stateMono (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.StateMono st (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => exact SystemState.StateMono.refl _
  | some p =>
    obtain ⟨scId, holder⟩ := p
    cases hT : st.getTcb? v with
    | none => exact SystemState.StateMono.refl _
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved st holder scId v with
      | error _ => exact SystemState.StateMono.refl _
      | ok st' =>
        obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact SystemState.StateMono.of_stateFields
          (returnDonatedSchedContext_getTcb?_stateFields_eq _ st' holder scId v hInv
            newOwner? hPop)

/-- **The teardown blocks and suspends no thread**: it readies the victim and,
on the reply arm, the donation holder, and otherwise patches queue links,
scheduling-context bindings and the reply link. -/
theorem cancelIpcBlocking_stateMono (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.StateMono st (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  have hQ : SystemState.StateMono st (removeFromAllEndpointQueues st v) :=
    SystemState.StateMono.of_stateFields fun t => by
      rw [removeFromAllEndpointQueues_getTcb?_eq_splice st v hInv t]
      exact spliceOutMidQueueNode_tcbField_frame (fun x => (x.ipcState, x.threadState, x.cpuAffinity))
        (fun _ _ _ _ _ _ => rfl) st v hInv t
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => exact SystemState.StateMono.refl _
  | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ =>
    exact hQ.trans (restoreToReadyStaging_stateMono _ v _
      (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv))
  | blockedOnNotification _ =>
    exact (SystemState.StateMono.of_stateFields fun t =>
      removeFromNotificationWaitQueue_tcbField_frame (fun x => (x.ipcState, x.threadState, x.cpuAffinity))
        (fun _ _ _ _ _ _ => rfl) st v hInv t).trans
      (restoreToReadyStaging_stateMono _ v _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv))
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    exact (((returnDonationToCancelledCaller_stateMono st v tcbV hInv).trans
      (SystemState.StateMono.of_getTcb (spliceThreadReplyFrameOut_getTcb?_eq _ tcbV hR))).trans
      (restoreToReadyStaging_stateMono _ v _ hS)).trans
      ((SystemState.StateMono.of_stateFields fun t =>
        consumeReplyLink_map_frame (fun x => (x.ipcState, x.threadState, x.cpuAffinity)) (fun _ => rfl) _ v tcbV
          (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS) t).trans
        (SystemState.StateMono.of_stateFields fun t =>
          (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks _ v _).getTcb?_map
            (fun x => (x.ipcState, x.threadState, x.cpuAffinity)) (fun _ => rfl) t))

end SeLe4n.Kernel
