-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-RR RR2.6 — the IPC-bundle preservation surface of the
-- live cross-core `.call` dispatch chain.  Staged because it composes the staged
-- `EndpointCallInvariant` surface (pending the SM10.1 runtime seam); everything
-- else it builds on is production.  The `.reply` chain's bundle, which used to
-- cohabit here, needs nothing staged and lives in the production
-- `EndpointReplyDispatchInvariant.lean`; the priority-inheritance walk's bundle
-- both chains end on lives beside its driver in
-- `IPC/Invariant/DonationPreservation.lean` §8.

import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.CapTransferBundle
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInvariant

/-!
# WS-RR RR2.6 — the live `.call` dispatch chain preserves `ipcInvariantFull`

`endpointCallCrossCoreDispatch` is the operation the live SMP `.call` arm routes
through: capability-carrying delivery → SchedContext donation (with the RR2.2
replenishment migration) → priority-inheritance chain walk.  Until RR2 only the
first stage carried a bundle theorem; this module derives what the rendezvous
leaves behind (§1) and composes the chain (§2).  The donation stage's bundle is
`IPC/Invariant/DonationPreservation.lean` §6, and the PIP walk's is §8 of the
same file — both production; only the WithCaps delivery surface this module
reads (`EndpointCallInvariant`) is staged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId SgiKind)
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §1  RR2.6 — what the `.call` rendezvous leaves behind
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
-- §2  RR2.6 — the cross-core `.call` chain
-- ============================================================================

/-- WS-RR RR2.6: `endpointCallWithCapsOnCore` preserves the bundle — the
cross-core rendezvous, then (on the arm that carries capabilities) the transfer.

**States the rendezvous' own hypotheses, not its conclusion.**  An earlier cut
took the whole post-rendezvous `ipcInvariantFull` as a hypothesis `hBare`, which
made the theorem say only "*if* the bundle survives the rendezvous, the transfer
keeps it" — true, dischargeable from
`endpointCallOnCore_preserves_ipcInvariantFull`, and yet not what the name
claims, since a reader counting `_preserves_ipcInvariantFull` theorems to
measure live-arm coverage would have read a presence for a relation (`CLAUDE.md`,
*a presence check is not a relation check*).  It also made this the one bundle
in the RR2 surface that did not take a pre-state bundle, asymmetric with its own
`.send` sibling — and the rule for two paths handling the same condition
asymmetrically is to make them symmetric, not to document the asymmetry.  The
rendezvous' obligations are therefore threaded and discharged here, exactly as
`endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull` does.

`hWtpmn'` / `hRCLRecip'` remain post-rendezvous hypotheses: they are the two
conjuncts the whole `ipcInvariantFull` surface still threads (WS-DT, closure
target RR3), and this theorem inherits that debt rather than adding to it.

The transfer's two input conditions are stated over the post-rendezvous state,
which is what it actually runs on; see
`endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull` for the same pair on
the `.send` side. -/
theorem endpointCallWithCapsOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : blockedThreadsPendingMessageConsistent
      (endpointCallOnCore endpointId caller
        { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (endpointCallOnCore endpointId caller
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
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    -- Stated with the typed `getTcb?` reader rather than a raw object-store
    -- index, matching `hCallerNotRecv` above and the AK7 typed-helper
    -- migration; the raw form the rendezvous theorem wants is recovered by
    -- `getTcb?_eq_some_iff` at the application below.
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.ipcState = .ready)
    (hCallerNotReply : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.schedContextBinding ≠ .unbound) :
    ipcInvariantFull (endpointCallWithCapsOnCore endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st).1 := by
  have hBare := endpointCallOnCore_preserves_ipcInvariantFull endpointId caller
    { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st _
    hInv hObjInv hFreshCaller hSendTailFresh rfl hWtpmn' hAllBudgetsNone hRCLRecip'
    hCallerNotRecv
    (fun tcb h => hCallerReady tcb ((SystemState.getTcb?_eq_some_iff st caller tcb).mpr h))
    (fun tcb h => hCallerNotReply tcb ((SystemState.getTcb?_eq_some_iff st caller tcb).mpr h))
    (fun tcb h => hCallerNotUnbound tcb ((SystemState.getTcb?_eq_some_iff st caller tcb).mpr h))
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
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : blockedThreadsPendingMessageConsistent
      (endpointCallOnCore endpointId caller
        { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (endpointCallOnCore endpointId caller
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
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.ipcState = .ready)
    (hCallerNotReply : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hNe : ∀ ep receiverTid, st.getEndpoint? endpointId = some ep →
      ep.receiveQ.head = some receiverTid → caller ≠ receiverTid) :
    ipcInvariantFull (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st).1 := by
  have hWithCaps : ipcInvariantFull (endpointCallWithCapsOnCore endpointId caller msg
      endpointRights callerCspaceRoot receiverSlotBase executingCore st).1 :=
    endpointCallWithCapsOnCore_preserves_ipcInvariantFull endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st hInv hObjInv hWtpmn' hAllBudgetsNone
      hRCLRecip' hRecvRootCNode hCapBadges hFreshCaller hSendTailFresh hCallerNotRecv
      hCallerReady hCallerNotReply hCallerNotUnbound
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


end SeLe4n.Kernel
