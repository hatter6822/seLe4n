-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR2.6 / RR2.11: PRODUCTION.  The IPC-bundle preservation surface of the
-- live cross-core `.call` and `.reply` dispatch chains.

import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.CapTransferBundle
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInvariant
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-!
# WS-RR RR2.6 / RR2.11 — the live dispatch chains preserve `ipcInvariantFull`

`endpointCallCrossCoreDispatch` and `endpointReplyCrossCoreDispatch` are the two
operations the live SMP `.call` and `.reply` arms route through.  Each is a
three-stage chain, and until RR2 only its *first* stage carried a bundle
theorem: the donation stage had none at all (RR2.5 built it), and the
priority-inheritance stage had frames for the object-store invariant and the
blocking graph but nothing for the IPC bundle.

This module supplies the missing middle and end, and composes the chains.

## Structure

* §1 — the PIP chain: `updatePipBoostOnCore` writes one TCB's `pipBoost` and
  migrates its run-queue bucket, so it establishes a `donationReadAgreement`
  and a `passiveServerIdleFrame`; the chain walk folds that over its fuel.
* §2 — `applyReplyDonationOnCore`, the per-core donation return.
* §3 — the `.call` chain (RR2.6).
* §4 — the `.reply` chain (RR2.11).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId SgiKind)
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §1  The cross-core priority-inheritance chain walk
-- ============================================================================

/-- WS-RR RR2.6: `updatePipBoostOnCore` preserves the whole IPC bundle.

It writes one TCB's `pipBoost` — a field no conjunct reads — and re-keys that
thread's run-queue bucket on its home core, which changes the queue *value* but
no thread's membership.  Everything the bundle reads is therefore intact. -/
theorem updatePipBoostOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (updatePipBoostOnCore st c tid) := by
  have hSelf : st.getTcb? tid = none → ipcInvariantFull (updatePipBoostOnCore st c tid) := by
    intro hNone
    rw [updatePipBoostOnCore_eq_self_of_getTcb?_none st c tid hNone]
    exact hInv
  cases hAt : st.objects[tid.toObjId]? with
  | none => exact hSelf (by unfold SystemState.getTcb?; rw [hAt])
  | some obj =>
    cases obj with
    | tcb tcb =>
        obtain ⟨p, hPost⟩ := updatePipBoostOnCore_objects_at st c tid tcb hAt hObjInv
        have hFrame : ∀ (oid : SeLe4n.ObjId), oid ≠ tid.toObjId →
            (updatePipBoostOnCore st c tid).objects[oid]? = st.objects[oid]? := fun oid hNe =>
          updatePipBoostOnCore_objects_ne st c tid oid
            (by simpa using fun h => hNe h.symm) hObjInv
        refine ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb _ hInv hAt hPost hFrame
          rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
        refine passiveServerIdleFrame_of_backward_monotone (fun x tcb' hTcb' => ?_)
          (fun y hy => (updatePipBoostOnCore_mem_runQueueOnCore st c bootCoreId tid y).mpr hy)
          (updatePipBoostOnCore_currentOnCore st c bootCoreId tid)
        by_cases hEq : x.toObjId = tid.toObjId
        · rw [hEq] at hTcb'
          obtain rfl : { tcb with pipBoost := p } = tcb' := by
            simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hPost.symm.trans hTcb'
          exact ⟨tcb, by rw [hEq]; exact hAt, rfl, rfl⟩
        · exact ⟨tcb', by rw [← hFrame x.toObjId hEq]; exact hTcb', rfl, rfl⟩
    | _ => exact hSelf (by unfold SystemState.getTcb?; rw [hAt])

/-- WS-RR RR2.6: the cross-core PIP boost with wake preserves the bundle — its
state component is exactly `updatePipBoostOnCore` on the thread's home core; the
SGI it returns is a notification for the runtime, not a state change. -/
theorem pipBoostWithWake_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (pipBoostWithWake st tid ec).1 :=
  updatePipBoostOnCore_preserves_ipcInvariantFull st (determineTargetCore st tid) tid
    hObjInv hInv

/-- **WS-RR RR2.6 / RR2.11**: the cross-core priority-inheritance chain walk
preserves the whole IPC bundle.

The walk is a fold of `pipBoostWithWake` boosts along the blocking chain, so the
induction is on the fuel with the per-step theorem above.  This is the stage both
live dispatch chains end on, and it had no bundle theorem before RR2 — only the
object-store and blocking-graph frames. -/
theorem propagatePipChainCrossCore_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (propagatePipChainCrossCore st tid ec fuel).1 := by
  show ipcInvariantFull (propagatePipChainCrossCoreState st tid ec fuel)
  induction fuel generalizing st tid with
  | zero => simpa using hInv
  | succ n ih =>
    rw [propagatePipChainCrossCoreState_step]
    have hInv' := pipBoostWithWake_preserves_ipcInvariantFull st tid ec hObjInv hInv
    have hObj' := pipBoostWithWake_preserves_objects_invExt st tid ec hObjInv
    cases blockingServer st tid with
    | none => exact hInv'
    | some nextServer => exact ih _ nextServer hObj' hInv'


-- ============================================================================
-- §2  RR2.11 — the per-core donation return
-- ============================================================================

/-- **WS-RR RR2.11**: `applyReplyDonationOnCore` preserves the whole IPC bundle.

Three stages, and only the first touches an object: the SchedContext return
(RR2.5's `returnDonatedSchedContext_preserves_ipcInvariantFull`), the RR2.8
replenishment migration (a per-core replenish-queue write — no object, no run
queue, no `current`), and the replier's deschedule on its own core.

`hReplierIdleAllowed` is the same single precondition the single-core form
carries, and for the same reason: the deschedule hands `passiveServerIdle` an
obligation for a thread it previously had none for. -/
theorem applyReplyDonationOnCore_preserves_ipcInvariantFull
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, st', hRet, hR, hEq⟩
  · rw [hEq]; exact hInv
  · have hFull' : ipcInvariantFull st' :=
      returnDonatedSchedContext_preserves_ipcInvariantFull st st' replierVtid scId owner
        hObjInv hInv hRet hReplierIdleAllowed hR
    obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
      replyDonationReturn?_some_char st replierVtid.val scId owner hInv.donationOwnerValid hRet
    obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
      returnDonatedSchedContext_getTcb?_char st st' replierVtid.val scId owner hObjInv hNe hR
    have hPEq : pTcb0 = pTcb := Option.some.inj (hPPre0.symm.trans hPPre)
    rw [hPEq] at hPPost
    -- The migration writes only per-core replenish queues.
    let stM : SystemState := migrateSchedContextReplenishment st' scId replierHome ownerHome
    have hMObjs : stM.objects = st'.objects := migrateSchedContextReplenishment_objects _ _ _ _
    have hMRq := migrateSchedContextReplenishment_runQueue_current_eq st' scId replierHome
      ownerHome bootCoreId
    have hFullM : ipcInvariantFull stM :=
      ipcInvariantFull_of_descheduleFrame st' stM hFull' hMObjs
        (passiveServerIdleFrame.of_objects_scheduler_eq hMObjs hMRq.1 hMRq.2)
    -- The deschedule writes only the executing core's queue and `current` slot.
    rw [hEq]
    refine ipcInvariantFull_of_descheduleFrame stM _ hFullM
      (removeRunnableOnCore_preserves_objects stM replierVtid.val executingCore)
      (removeRunnableOnCore_passiveServerIdleFrame stM replierVtid.val executingCore
        (fun tcb hTcb => ?_))
    rw [hMObjs] at hTcb
    have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
      Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
    exact Or.inr (by rw [← hEqT]; exact hReplierIdleAllowed pTcb hPPre)


-- ============================================================================
-- §3  RR2.6 — what the `.call` rendezvous leaves behind
-- ============================================================================

/-- WS-RR RR2.6: a successful `endpointCallOnCore` on an endpoint with a waiting
receiver took the rendezvous path, and its four intermediate states are exposed.

The forward companion of `endpointCallOnCore_rendezvous_eq`, which reduces the
call *given* the intermediates; this one produces them from success. -/
theorem endpointCallOnCore_ok_rendezvous_decompose
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint) (receiver : SeLe4n.ThreadId)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hHead : ep.receiveQ.head = some receiver)
    (sgi : Option (CoreId × SgiKind))
    (hOk : (endpointCallOnCore endpointId caller msg executingCore st).2 = .ok sgi) :
    ∃ (recvTcb0 : TCB) (st' st'' st4 st5 : SystemState),
      endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st') ∧
      storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'' ∧
      storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1 caller
        (.blockedOnReply endpointId (some receiver)) none = .ok st4 ∧
      SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5) ∧
      (endpointCallOnCore endpointId caller msg executingCore st).1
        = removeRunnableOnCore st5 caller executingCore := by
  revert hOk
  unfold endpointCallOnCore
  split
  · intro hOk; cases hOk
  · split
    · intro hOk; cases hOk
    · rw [hEp]
      simp only []
      rw [hHead]
      simp only []
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => intro hOk; cases hOk
      | ok triple =>
        obtain ⟨recvId, recvTcb0, st'⟩ := triple
        simp only []
        cases hStore : storeTcbIpcStateAndMessage st' recvId .ready (some msg) with
        | error e => intro hOk; cases hOk
        | ok st'' =>
          simp only []
          cases hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' recvId executingCore).1
              caller (.blockedOnReply endpointId (some recvId)) none with
          | error e => intro hOk; cases hOk
          | ok st4 =>
            simp only []
            cases hLink : SystemState.linkServerStashedReply caller recvId st4 with
            | error e => intro hOk; cases hOk
            | ok pair =>
              obtain ⟨u, st5⟩ := pair; cases u
              simp only []
              intro _
              have hRecvEq : recvId = receiver :=
                endpointQueuePopHead_popped_eq_head endpointId true st st' ep recvId receiver
                  recvTcb0 ((getEndpoint?_eq_some_iff st endpointId ep).mp hEp)
                  (by simpa using hHead) hPop
              subst hRecvEq
              exact ⟨recvTcb0, st', st'', st4, st5,
                by first | rfl | assumption, by first | rfl | assumption,
                by first | rfl | assumption, by first | rfl | assumption, rfl⟩


/-- **WS-RR RR2.6**: what the `.call` rendezvous leaves the two participants in —
the caller blocked awaiting the reply, the receiver `.ready`.

These are exactly the two facts RR2.5's donation theorems need about the state
the donation runs on, and proving them here is what keeps
`endpointCallCrossCoreDispatch_preserves_ipcInvariantFull` from having to assume
them:

* the caller is `.blockedOnReply` — `donationOwnerValid` requires a donation's
  owner to be recoverable through the reply it waits on;
* the receiver is `.ready` — so, by `donationOwnerValid` on the pre-donation
  state, no thread already names the receiver as *its* donation owner (an owner
  is `.blockedOnReply`, which `.ready` is not).

`hNe` is discharged by the caller of this lemma from
`queueHeadBlockedConsistent` (the receive-queue head is `.blockedOnReceive`) and
the caller's own non-blocked state. -/
theorem endpointCallOnCore_rendezvous_post_ipcState
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hHead : ep.receiveQ.head = some receiver)
    (hNe : caller ≠ receiver)
    (sgi : Option (CoreId × SgiKind))
    (hOk : (endpointCallOnCore endpointId caller msg executingCore st).2 = .ok sgi) :
    (∀ tcb, (endpointCallOnCore endpointId caller msg executingCore st).1.getTcb? caller
        = some tcb → ∃ e rt, tcb.ipcState = .blockedOnReply e rt) ∧
    (∀ tcb, (endpointCallOnCore endpointId caller msg executingCore st).1.getTcb? receiver
        = some tcb → tcb.ipcState = .ready) := by
  obtain ⟨recvTcb0, st', st'', st4, st5, hPop, hStore, hCallerStore, hLink, hEq⟩ :=
    endpointCallOnCore_ok_rendezvous_decompose endpointId caller msg executingCore st ep
      receiver hEp hHead sgi hOk
  -- Object-store invariants along the chain.
  have hInv' : st'.objects.invExt :=
    endpointQueuePopHead_preserves_objects_invExt endpointId true st st' receiver recvTcb0
      hObjInv hPop
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' receiver _ _ hInv' hStore
  -- The receiver is `.ready` in `st''`, so the wake is object-invisible.
  obtain ⟨recvTcb'', hRecv'', hRecvReady⟩ :=
    storeTcbIpcStateAndMessage_getTcb?_ipcState st' st'' receiver .ready (some msg) hInv' hStore
  have hWakeObjs : ∀ oid, (wakeThread st'' receiver executingCore).1.objects[oid]?
      = st''.objects[oid]? :=
    wakeThread_objects_getElem_eq_of_ready st'' receiver executingCore recvTcb'' hRecv''
      hRecvReady hInv''
  have hWakeInv : (wakeThread st'' receiver executingCore).1.objects.invExt :=
    wakeThread_preserves_objects_invExt st'' receiver executingCore hInv''
  have hInv4 : st4.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt _ st4 caller _ _ hWakeInv hCallerStore
  -- The caller's blocking store fixes its `ipcState` in `st4`.
  obtain ⟨callerTcb4, hCaller4, hCallerBlocked⟩ :=
    storeTcbIpcStateAndMessage_getTcb?_ipcState (wakeThread st'' receiver executingCore).1 st4
      caller (.blockedOnReply endpointId (some receiver)) none hWakeInv hCallerStore
  rw [hEq]
  constructor
  · intro tcb hTcb
    rw [removeRunnableOnCore_getTcb?] at hTcb
    obtain ⟨tcb4, hTcb4, hIpcEq⟩ := linkServerStashedReply_tcb_ipcState_backward st4 st5
      caller receiver caller tcb hInv4 hLink ((getTcb?_eq_some_iff st5 caller tcb).mp hTcb)
    have : tcb4 = callerTcb4 :=
      Option.some.inj (((getTcb?_eq_some_iff st4 caller tcb4).mpr hTcb4).symm.trans hCaller4)
    exact ⟨endpointId, some receiver, by rw [← hIpcEq, this]; exact hCallerBlocked⟩
  · intro tcb hTcb
    rw [removeRunnableOnCore_getTcb?] at hTcb
    obtain ⟨tcb4, hTcb4, hIpcEq⟩ := linkServerStashedReply_tcb_ipcState_backward st4 st5
      caller receiver receiver tcb hInv4 hLink ((getTcb?_eq_some_iff st5 receiver tcb).mp hTcb)
    obtain ⟨tcbW, hTcbW, _, hIpcW⟩ := storeTcbIpcStateAndMessage_getTcb?_backward
      (wakeThread st'' receiver executingCore).1 st4 caller
      (.blockedOnReply endpointId (some receiver)) none hWakeInv hCallerStore receiver tcb4
      ((getTcb?_eq_some_iff st4 receiver tcb4).mpr hTcb4)
    have hTcbW'' : st''.getTcb? receiver = some tcbW := by
      rw [getTcb?_eq_some_iff] at hTcbW ⊢
      rw [← hWakeObjs receiver.toObjId]; exact hTcbW
    have : tcbW = recvTcb'' := Option.some.inj (hTcbW''.symm.trans hRecv'')
    rw [← hIpcEq, ← hIpcW (Ne.symm hNe), this]
    exact hRecvReady


-- ============================================================================
-- §4  RR2.6 — the cross-core `.call` chain
-- ============================================================================

/-- WS-RR RR2.6: `endpointCallWithCapsOnCore` preserves the bundle — the
cross-core rendezvous, then (on the arm that carries capabilities) the transfer.

The transfer's two input conditions are stated over the post-rendezvous state,
which is what it actually runs on; see
`endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull` for the same pair on
the `.send` side. -/
theorem endpointCallWithCapsOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hBare : ipcInvariantFull (endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1)
    (hRecvRootCNode : ∀ (t : SeLe4n.ThreadId) (r : SeLe4n.ObjId),
      lookupCspaceRoot (endpointCallOnCore endpointId caller
        { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1 t
        = some r →
      ∃ cn, (endpointCallOnCore endpointId caller
        { msg with capsGranted := endpointRights.mem AccessRight.grant }
        executingCore st).1.objects[r]? = some (.cnode cn))
    (hCapBadges : ∀ (i : Nat) (c : TransferCap), msg.caps[i]? = some c →
      ∀ b, c.cap.badge = some b → b.valid) :
    ipcInvariantFull (endpointCallWithCapsOnCore endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st).1 := by
  have hBareInv := endpointCallOnCore_preserves_objects_invExt endpointId caller
    { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st hObjInv
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    rw [hCall] at hBare hBareInv hRecvRootCNode
    cases res with
    | error e => exact hBare
    | ok sgi =>
      simp only
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only; split <;> exact hBare
      | some ep =>
        simp only
        cases hHead : ep.receiveQ.head with
        | none => simp only; split <;> exact hBare
        | some receiverId =>
          simp only
          split
          · exact hBare
          · cases hRoot : lookupCspaceRoot stCall receiverId with
            | none => exact hBare
            | some recvRoot =>
              simp only
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem AccessRight.grant }
                  callerCspaceRoot recvRoot receiverSlotBase
                  (endpointRights.mem AccessRight.grant) stCall with
              | error e => exact hBare
              | ok pair =>
                obtain ⟨summary, stFinal⟩ := pair
                simp only
                obtain ⟨cn, hCn⟩ := hRecvRootCNode receiverId recvRoot hRoot
                exact ipcUnwrapCaps_preserves_ipcInvariantFull _ callerCspaceRoot recvRoot
                  receiverSlotBase _ stCall stFinal summary cn hBare hBareInv hCn
                  (by simpa using hCapBadges) hUnwrap

/-- WS-RR RR2.6: `endpointCallWithCapsOnCore` preserves the object store's
extended invariant. -/
theorem endpointCallWithCapsOnCore_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st).1.objects.invExt := by
  have hBareInv := endpointCallOnCore_preserves_objects_invExt endpointId caller
    { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st hObjInv
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    rw [hCall] at hBareInv
    cases res with
    | error e => exact hBareInv
    | ok sgi =>
      simp only
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only; split <;> exact hBareInv
      | some ep =>
        simp only
        cases hHead : ep.receiveQ.head with
        | none => simp only; split <;> exact hBareInv
        | some receiverId =>
          simp only
          split
          · exact hBareInv
          · cases hRoot : lookupCspaceRoot stCall receiverId with
            | none => exact hBareInv
            | some recvRoot =>
              simp only
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem AccessRight.grant }
                  callerCspaceRoot recvRoot receiverSlotBase
                  (endpointRights.mem AccessRight.grant) stCall with
              | error e => exact hBareInv
              | ok pair =>
                obtain ⟨summary, stFinal⟩ := pair
                simp only
                exact ipcUnwrapCaps_preserves_objects_invExt _ callerCspaceRoot recvRoot
                  receiverSlotBase _ stCall stFinal summary hBareInv hUnwrap

/-- WS-RR RR2.6: `endpointCallWithCapsOnCore` frames every thread's `ipcState` —
the capability transfer writes only the receiver's CSpace CNode, never a TCB, so
the two rendezvous facts §3 establishes survive it. -/
theorem endpointCallWithCapsOnCore_getTcb?_ipcState_eq
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (t : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : (endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st).1.getTcb? t = some tcb) :
    SystemState.getTcb? (endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1
      t = some tcb := by
  have hBareInv := endpointCallOnCore_preserves_objects_invExt endpointId caller
    { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st hObjInv
  revert hTcb
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    rw [hCall] at hBareInv
    cases res with
    | error e => exact id
    | ok sgi =>
      simp only
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only; split <;> exact id
      | some ep =>
        simp only
        cases hHead : ep.receiveQ.head with
        | none => simp only; split <;> exact id
        | some receiverId =>
          simp only
          split
          · exact id
          · cases hRoot : lookupCspaceRoot stCall receiverId with
            | none => exact id
            | some recvRoot =>
              simp only
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem AccessRight.grant }
                  callerCspaceRoot recvRoot receiverSlotBase
                  (endpointRights.mem AccessRight.grant) stCall with
              | error e => exact id
              | ok pair =>
                obtain ⟨summary, stFinal⟩ := pair
                simp only
                intro hTcb
                -- The transfer writes only `recvRoot`, and a TCB is not stored there.
                rw [getTcb?_eq_some_iff] at hTcb ⊢
                by_cases hEqRoot : t.toObjId = recvRoot
                · rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode _ callerCspaceRoot recvRoot
                    receiverSlotBase _ stCall stFinal summary hBareInv hUnwrap with
                    hSame | ⟨cn', hCn'⟩
                  · rw [hEqRoot] at hTcb ⊢; rw [← hSame]; exact hTcb
                  · exfalso
                    rw [hEqRoot, hCn'] at hTcb
                    exact KernelObject.noConfusion (Option.some.inj hTcb)
                · rw [← ipcUnwrapCaps_preserves_objects_ne _ callerCspaceRoot recvRoot
                    receiverSlotBase _ stCall stFinal summary t.toObjId hEqRoot hBareInv hUnwrap]
                  exact hTcb


/-- WS-RR RR2.6: a `endpointCallWithCapsOnCore` that returns `.ok` had a `.ok`
rendezvous underneath it — every arm that reaches the capability transfer went
through a successful `endpointCallOnCore`, and every failing arm propagates the
error. -/
theorem endpointCallWithCapsOnCore_ok_implies_call_ok
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (summary : CapTransferSummary) (sgi : Option (CoreId × SgiKind))
    (hOk : (endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st).2 = .ok (summary, sgi)) :
    ∃ sgi', (endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).2
      = .ok sgi' := by
  revert hOk
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    cases res with
    | error e => intro hOk; cases hOk
    | ok sgi0 => intro _; exact ⟨sgi0, rfl⟩

/-- **WS-RR RR2.6: the live cross-core `.call` dispatch preserves
`ipcInvariantFull`.**

The chain is WithCaps → SchedContext donation → priority-inheritance walk, and
before RR2 only its first stage carried a bundle theorem.  The donation's two
preconditions are **not** hypotheses here: §3 derives them from the rendezvous
this very chain performs — the caller is `.blockedOnReply` because the call
blocked it, and no thread owns a donation on the receiver because the call woke
the receiver `.ready` and `donationOwnerValid` puts an owner `.blockedOnReply`.

`hNe` (caller ≠ receiver) is the one structural fact the chain does not itself
witness; a caller cannot be the receiver it rendezvouses with, and the dispatch's
own `queueHeadBlockedConsistent` reading is where a caller discharges it. -/
theorem endpointCallCrossCoreDispatch_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hBare : ipcInvariantFull (endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1)
    (hRecvRootCNode : ∀ (t : SeLe4n.ThreadId) (r : SeLe4n.ObjId),
      lookupCspaceRoot (endpointCallOnCore endpointId caller
        { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1 t
        = some r →
      ∃ cn, (endpointCallOnCore endpointId caller
        { msg with capsGranted := endpointRights.mem AccessRight.grant }
        executingCore st).1.objects[r]? = some (.cnode cn))
    (hCapBadges : ∀ (i : Nat) (c : TransferCap), msg.caps[i]? = some c →
      ∀ b, c.cap.badge = some b → b.valid)
    (hNe : ∀ ep receiverTid, st.getEndpoint? endpointId = some ep →
      ep.receiveQ.head = some receiverTid → caller ≠ receiverTid) :
    ipcInvariantFull (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st).1 := by
  have hWithCaps : ipcInvariantFull (endpointCallWithCapsOnCore endpointId caller msg
      endpointRights callerCspaceRoot receiverSlotBase executingCore st).1 :=
    endpointCallWithCapsOnCore_preserves_ipcInvariantFull endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st hObjInv hBare hRecvRootCNode hCapBadges
  have hWithCapsInv : (endpointCallWithCapsOnCore endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st).1.objects.invExt :=
    endpointCallWithCapsOnCore_preserves_objects_invExt endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st hObjInv
  -- The rendezvous facts, transported through the capability transfer.
  have hIpcFrame := endpointCallWithCapsOnCore_getTcb?_ipcState_eq endpointId caller msg
    endpointRights callerCspaceRoot receiverSlotBase executingCore st hObjInv
  unfold endpointCallCrossCoreDispatch
  cases hWc : endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st with
  | mk stWc res =>
    rw [hWc] at hWithCaps hWithCapsInv hIpcFrame
    cases res with
    | error e => exact hWithCaps
    | ok summarySgi =>
      obtain ⟨summary, sgi⟩ := summarySgi
      simp only
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only; exact hWithCaps
      | some ep =>
        simp only
        cases hHead : ep.receiveQ.head with
        | none => simp only; exact hWithCaps
        | some receiverTid =>
          simp only
          cases hCV : SeLe4n.ThreadId.toValid? caller with
          | none => simp only; exact hWithCaps
          | some callerV =>
            cases hRV : SeLe4n.ThreadId.toValid? receiverTid with
            | none => simp only; exact hWithCaps
            | some receiverV =>
              simp only
              -- The bare call succeeded, so the rendezvous ran.
              have hCallOk : ∃ sgi', (endpointCallOnCore endpointId caller
                  { msg with capsGranted := endpointRights.mem AccessRight.grant }
                  executingCore st).2 = .ok sgi' :=
                endpointCallWithCapsOnCore_ok_implies_call_ok endpointId caller msg
                  endpointRights callerCspaceRoot receiverSlotBase executingCore st summary sgi
                  (by rw [hWc])
              obtain ⟨sgi', hCallOk⟩ := hCallOk
              obtain ⟨hCallerBlk, hRecvReady⟩ :=
                endpointCallOnCore_rendezvous_post_ipcState endpointId caller
                  { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore
                  st ep receiverTid hObjInv hEp hHead (hNe ep receiverTid hEp hHead) sgi' hCallOk
              have hCallerV : callerV.val = caller :=
                SeLe4n.ThreadId.toValid?_some_val_eq caller callerV hCV
              have hReceiverV : receiverV.val = receiverTid :=
                SeLe4n.ThreadId.toValid?_some_val_eq receiverTid receiverV hRV
              -- Donation precondition 1: the caller awaits the reply.
              have hDon1 : ∀ tcb, stWc.getTcb? callerV.val = some tcb →
                  ∃ e rt, tcb.ipcState = .blockedOnReply e rt := by
                intro tcb hTcb
                rw [hCallerV] at hTcb
                exact hCallerBlk tcb (hIpcFrame caller tcb hTcb)
              -- Donation precondition 2: nothing owns a donation on the receiver.
              have hDon2 : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
                  stWc.getTcb? tid = some tcb →
                  tcb.schedContextBinding ≠ .donated scId receiverV.val := by
                intro tid tcb scId hTcb hBind
                obtain ⟨_, ownerTcb, hOwner, _, ep', rt, hOwnerIpc⟩ :=
                  hWithCaps.donationOwnerValid tid tcb scId receiverV.val
                    ((getTcb?_eq_some_iff stWc tid tcb).mp hTcb) hBind
                have hReady := hRecvReady ownerTcb
                  (hIpcFrame receiverTid ownerTcb
                    (by rw [← hReceiverV]; exact (getTcb?_eq_some_iff stWc _ ownerTcb).mpr hOwner))
                rw [hReady] at hOwnerIpc
                cases hOwnerIpc
              cases hDon : applyCallDonationOnCore stWc callerV receiverV
                  (determineTargetCore st caller) (determineTargetCore st receiverTid) with
              | error e => simp only; exact hWithCaps
              | ok stDon =>
                simp only
                have hDonFull : ipcInvariantFull stDon :=
                  applyCallDonationOnCore_preserves_ipcInvariantFull stWc stDon callerV receiverV
                    _ _ hWithCapsInv hWithCaps hDon1 hDon2 hDon
                have hDonInv : stDon.objects.invExt := by
                  obtain ⟨stMid, hMid, _⟩ := applyCallDonationOnCore_ok_decompose stWc stDon
                    callerV receiverV _ _ hDon
                  have hMidInv := applyCallDonation_preserves_objects_invExt stWc stMid callerV
                    receiverV hWithCapsInv hMid
                  rw [show stDon.objects = stMid.objects from
                    applyCallDonationOnCore_objects_eq stWc stMid stDon callerV receiverV _ _
                      hMid hDon]
                  exact hMidInv
                exact propagatePipChainCrossCore_preserves_ipcInvariantFull stDon receiverTid
                  executingCore _ hDonInv hDonFull


-- ============================================================================
-- §5  RR2.11 — the cross-core `.reply` chain
-- ============================================================================

/-- WS-RR RR2.11: `applyReplyDonationOnCore` preserves the object store's
extended invariant — the return through `returnDonatedSchedContext`, the
migration and the deschedule through their object frames. -/
theorem applyReplyDonationOnCore_preserves_objects_invExt
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    st''.objects.invExt := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, st', _, hR, hEq⟩
  · rw [hEq]; exact hObjInv
  · have hInv' := returnDonatedSchedContext_preserves_objects_invExt st st' replierVtid.val scId
      owner hObjInv hR
    rw [hEq, removeRunnableOnCore_preserves_objects, migrateSchedContextReplenishment_objects]
    exact hInv'

/-- **WS-RR RR2.11: the live cross-core `.reply` dispatch preserves
`ipcInvariantFull`.**

The chain is reply delivery → SchedContext donation return → priority-inheritance
reversion, and as on the `.call` side only the first stage carried a bundle
theorem before RR2.

`hServerIdleAllowed` is stated on the **pre**-state and transported through the
reply by `endpointReplyOnCore_tcb_backward`, whose dichotomy is exactly what
makes that sound: the reply either leaves a thread's `ipcState` alone or sets it
`.ready`, and `.ready` is itself a `passiveServerIdleAllowed` state.  What it
rules out is a recorded server parked in `.blockedOnSend` / `.blockedOnCall`,
which the donation return would strand `.unbound` off the run queue in a state
`passiveServerIdle` forbids. -/
theorem endpointReplyCrossCoreDispatch_preserves_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : blockedThreadsPendingMessageConsistent
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hDOV' : donationOwnerValid
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hServerIdleAllowed : ∀ (expected : SeLe4n.ThreadId), recordedReplyServer? st target
        = some expected →
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hReply : ipcInvariantFull (endpointReplyOnCore replier target msg executingCore st).1 :=
    endpointReplyOnCore_preserves_ipcInvariantFull replier target msg executingCore st hInv
      hObjInv hWtpmn' hDOV' hAllBudgetsNone
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  have hBack := endpointReplyOnCore_tcb_backward replier target msg executingCore st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply hReplyInv hBack
    cases res with
    | error e => exact hInv
    | ok replySgi =>
      simp only
      cases hRec : recordedReplyServer? st target with
      | none => simp only; exact hInv
      | some expected =>
        simp only
        cases hEV : SeLe4n.ThreadId.toValid? expected with
        | none => simp only; exact hInv
        | some expectedV =>
          simp only
          have hExpV : expectedV.val = expected :=
            SeLe4n.ThreadId.toValid?_some_val_eq expected expectedV hEV
          -- Transport the allowed-state condition across the reply.
          have hAllowed : ∀ tcb, st1.getTcb? expectedV.val = some tcb →
              passiveServerIdleAllowed tcb.ipcState := by
            intro tcb hTcb
            rw [hExpV] at hTcb
            obtain ⟨tcb0, hTcb0, _, _, hDich⟩ := hBack expected tcb hTcb
            rcases hDich with hReady | ⟨hSame, _⟩
            · exact Or.inl hReady
            · rw [hSame]; exact hServerIdleAllowed expected hRec tcb0 hTcb0
          cases hDon : applyReplyDonationOnCore st1 expectedV (determineExecutingCore st expected)
              (determineTargetCore st expected) (replyDonationOwnerHome st expected) with
          | error e => simp only; exact hInv
          | ok st2 =>
            simp only
            have hDonFull : ipcInvariantFull st2 :=
              applyReplyDonationOnCore_preserves_ipcInvariantFull st1 st2 expectedV _ _ _
                hReplyInv hReply hAllowed hDon
            have hDonInv : st2.objects.invExt :=
              applyReplyDonationOnCore_preserves_objects_invExt st1 st2 expectedV _ _ _
                hReplyInv hDon
            exact propagatePipChainCrossCore_preserves_ipcInvariantFull st2 expected executingCore
              _ hDonInv hDonFull

end SeLe4n.Kernel
