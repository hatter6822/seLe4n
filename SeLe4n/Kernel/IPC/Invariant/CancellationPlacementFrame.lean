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

/-- WS-RR RR8.11: the restore rewrites the victim's own TCB and writes nothing
where no TCB was. -/
private theorem restoreToReadyStaging_placement_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.restoreToReadyStaging st tid frame).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement := by
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
      | none => simp [restoredTcb, TCB.placement]
      | some f => simp [restoredTcb, TCB.withReturnFrame, TCB.placement]
    · have hPost : (Lifecycle.Suspend.restoreToReadyStaging st tid frame).getTcb? x
          = st.getTcb? x := by
        unfold SystemState.getTcb?
        rw [restoreToReadyStaging_objects_ne st tid frame x.toObjId hInv
          (fun hc => hk (SeLe4n.ThreadId.toObjId_injective x tid hc))]
      rw [hPost]

/-- WS-RR RR8.11: a store of one TCB at a key that already held a TCB with the same
`TCB.placement` frames every thread's home core and run-queue links. -/
private theorem storeObject_tcb_placement_frame {st st' : SystemState} {k : SeLe4n.ObjId}
    {t t' : TCB}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.tcb t))
    (hAff : t'.placement = t.placement)
    (hStore : storeObject k (.tcb t') st = .ok ((), st')) (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement := by
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
private theorem endpointQueueRemove_placement_frame {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement := by
  refine SystemState.map_tcbField_eq_of_refines TCB.placement (fun t0 hT0 => ?_) (fun t' hT' => ?_)
  · obtain ⟨ot', hL', hAff'⟩ := endpointQueueRemove_getTcb_upToPlacement endpointId isReceiveQ
      tid st st' hInv h x.toObjId t0
      (by rw [← RHTable_getElem?_eq_get?]; exact (SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    exact ⟨ot', (SystemState.getTcb?_eq_some_iff _ x ot').mpr
      (by rw [RHTable_getElem?_eq_get?]; exact hL'), hAff'.symm⟩
  · obtain ⟨ot, hL, _⟩ := endpointQueueRemove_getTcb_backward_upToField
      TCB.placement
      (fun _ _ _ _ => rfl) endpointId isReceiveQ tid st st' hInv h x.toObjId t'
      ((SystemState.getTcb?_eq_some_iff _ x t').mp hT')
    exact ⟨ot, (SystemState.getTcb?_eq_some_iff st x ot).mpr hL⟩

/-- The IPC abort a timeout or a reclaim runs: the queue removal patches queue
links, and the aborted thread's TCB is stored over itself with the same
placement. -/
theorem abortPendingIpcOnEndpoint_placement_frame {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hA : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map TCB.placement = (st.getTcb? x).map TCB.placement := by
  obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  rw [storeObject_tcb_placement_frame (hInv := hInv1)
        (hPre := lookupTcb_some_objects _ _ _ hLook) (hStore := hStore)
        (hAff := by simp [TCB.withReturnFrame, TCB.placement]) (x := x),
    endpointQueueRemove_placement_frame hInv hRem x]

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

/-- WS-RR RR8.11: the holder abort ends an outstanding send or call and moves no
thread's home core. -/
private theorem abortHolderPendingIpc_placement_frame (st : SystemState)
    (holder : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.abortHolderPendingIpc st holder).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement := by
  have hArm : ∀ (epId : SeLe4n.ObjId),
      (((match abortPendingIpcOnEndpoint epId false holder st with
        | .ok s => s
        | .error _ => st : SystemState)).getTcb? x).map TCB.placement
        = (st.getTcb? x).map TCB.placement := by
    intro epId
    cases hA : abortPendingIpcOnEndpoint epId false holder st with
    | error _ => rfl
    | ok stA => exact abortPendingIpcOnEndpoint_placement_frame hInv hA x
  unfold Lifecycle.Suspend.abortHolderPendingIpc
  split
  · rfl
  · rename_i holderTcb _
    split
    · rename_i epId _; exact hArm epId
    · rename_i epId _; exact hArm epId
    · rfl

/-- WS-RR RR8.11: the reclaim moves no thread's home core — its abort prefix
patches queue links and blocking state, and the pop rebinds scheduling contexts
(`returnDonatedSchedContext_getTcb?_placement_eq`). -/
private theorem returnDonationToCancelledCaller_placement_frame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => rfl
  | some p =>
    obtain ⟨scId, holder⟩ := p
    cases hT : st.getTcb? v with
    | none => rfl
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved
          (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder scId v with
      | error _ => rfl
      | ok st' =>
        obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        rw [returnDonatedSchedContext_getTcb?_placement_eq _ st' holder scId v
            (Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv)
            newOwner? hPop x,
          abortHolderPendingIpc_placement_frame st holder hInv x]

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
Reply, so it moves no thread's home core. -/
private theorem consumeReplyLink_placement_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.consumeReplyLink st tid tcb).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases hR : tcb.replyObject with
  | none => rfl
  | some rid =>
    have hStep := SystemState.consumeCallerReply_eq_link st tid rid
    refine SystemState.map_tcbField_eq_of_refines TCB.placement (fun t0 hT0 => ?_)
      (fun t' hT' => consumeCallerReply_getTcb?_backward hInv hStep x t' hT')
    by_cases hk : x.toObjId = tid.toObjId
    · refine ⟨{ t0 with replyObject := none }, ?_, rfl⟩
      refine (SystemState.getTcb?_eq_some_iff _ x _).mpr ?_
      rw [hk]
      exact SystemState.consumeCallerReply_tcb_caller st _ tid rid hInv hStep t0
        (by rw [← hk]; exact (SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    · exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ x t0).mpr
        (SystemState.consumeCallerReply_tcb_other st _ tid rid hInv hStep x.toObjId t0 hk
          ((SystemState.getTcb?_eq_some_iff st x t0).mp hT0)), rfl⟩

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
    rw [restoreToReadyStaging_placement_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x,
      removeFromAllEndpointQueues_placement_frame st v hInv x]
  | blockedOnReceive _ =>
    rw [restoreToReadyStaging_placement_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x,
      removeFromAllEndpointQueues_placement_frame st v hInv x]
  | blockedOnCall _ =>
    rw [restoreToReadyStaging_placement_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x,
      removeFromAllEndpointQueues_placement_frame st v hInv x]
  | blockedOnNotification _ =>
    rw [restoreToReadyStaging_placement_frame _ v _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv) x,
      removeFromNotificationWaitQueue_placement_frame st v hInv x]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    rw [consumeReplyLink_placement_frame _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS) x,
      restoreToReadyStaging_placement_frame _ v _ hS x,
      spliceThreadReplyFrameOut_getTcb?_eq _ tcbV hR x,
      returnDonationToCancelledCaller_placement_frame st v tcbV hInv x]

/-- **WS-ZA ZA4.5**: the teardown moves no thread's run-queue core. -/
theorem cancelIpcBlocking_runCoresAgree (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.RunCoresAgree (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st := fun y => by
  have h := cancelIpcBlocking_placement_frame st v tcbV hInv y
  revert h
  cases (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getTcb? y <;>
    cases st.getTcb? y <;> simp_all [TCB.placement]

end SeLe4n.Kernel
