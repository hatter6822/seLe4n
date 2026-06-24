-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.A cross-core IPC (runtime dispatch wiring
-- gated on the SM5.I FFI seam; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Concurrency.Locks.Serializability

/-!
# WS-SM SM6.A — Cross-core endpoint-call invariant preservation

`endpointCallOnCore` preserves the kernel's IPC invariants.  The structural
content is the **keystone** that the cross-core receiver wake
(`wakeThread`/`enqueueRunnableOnCore`) is *object-invisible* on the rendezvous
path: the receiver was already set `.ready` by the preceding
`storeTcbIpcStateAndMessage`, so the wake's `ipcState := .ready` write inserts
the *same* value it found — every object-store **lookup** is unchanged (the
Robin-Hood array representation may differ, so this is pointwise `[·]?`
agreement, not structural object equality; see the §5 congruences).

The cross-core operation differs from the single-core `endpointCall` only in the
scheduler placement of the woken receiver / blocked caller.  Fourteen of the
fifteen `ipcInvariantFull` conjuncts (and `ipcInvariant`) are **lookup-only**
predicates — they read the state solely through `objects[·]?` — so the wake and
the per-core deschedule cannot disturb them, and this file derives them
(`ipcInvariant`, `dualQueueSystemInvariant`, `allPendingMessagesBounded`,
`badgeWellFormed` are proved here; the rest are lookup-only by the same
congruence).  The scheduler-sensitive `passiveServerIdle` — which reads the
per-core run queue and current thread — is now **established** from the pre-state
too (IPC de-threading D6, v0.32.9): `endpointCallOnCore_passiveServerIdleFrame`
discharges it via the per-core scheduler frames (`wakeThread` only *adds* to a
run queue; `removeRunnableOnCore` frames the boot-core queue/current by per-core
locality whether or not `executingCore` is the boot core), carrying the
dischargeable `hCallerNotUnbound` exactly as the single-core
`endpointCall_preserves_ipcInvariantFull` does.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  `objects.invExt` preservation (object-store integrity)
-- ============================================================================

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves object-store
integrity (`invExt`).  On every control path the post-state's object store is
either `st`'s (an error / no-op leaf) or the result of the
pop / store / wake / store / deschedule chain, each step of which preserves
`invExt`.  Unconditional: an error leaf returns the pre-state unchanged. -/
theorem endpointCallOnCore_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (endpointCallOnCore endpointId caller msg executingCore st).1.objects.invExt := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hObjInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hObjInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hObjInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hObjInv
      | ok st' =>
        simp only
        have h1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hObjInv
        | ok st'' =>
          simp only
          have h2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' caller _ _ h1 hMsg
          show (removeRunnableOnCore st'' caller executingCore).objects.invExt
          rw [removeRunnableOnCore_preserves_objects]; exact h2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hObjInv
      | ok pair =>
        simp only
        have h1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hObjInv
        | ok st2 =>
          simp only
          have h2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ h1 hMsg
          have hW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore h2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hObjInv
          | ok st4 =>
            simp only
            have h4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hW hCS
            -- WS-SM SM6.D (#7.3b fold): thread the server-first reply link
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hObjInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have h5 := linkServerStashedReply_preserves_objects_invExt st4 st5 caller pair.1 h4 hLink
              show (removeRunnableOnCore st5 caller executingCore).objects.invExt
              rw [removeRunnableOnCore_preserves_objects]; exact h5

-- ============================================================================
-- §2  Keystone: the cross-core receiver wake is object-invisible
-- ============================================================================

-- WS-SM SM6.A.1 (keystone): `enqueueRunnableOnCore` / `wakeThread` of an
-- already-`.ready` thread is invisible to every object-store lookup
-- (`{enqueueRunnableOnCore,wakeThread}_objects_getElem_eq_of_ready`).  These
-- moved to `Scheduler.Operations.PerCoreWake` (beside `wakeThread`) so the SM6.A
-- endpoint-call and SM6.B notification cross-core invariant proofs both share
-- them without either side's heavy invariant module entering the other's
-- production import closure.

-- ============================================================================
-- §3  `ipcInvariant` (notification well-formedness) preservation
-- ============================================================================

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves the notification
invariant.  Mirrors the single-core `endpointCall_preserves_ipcInvariant`, with
the receiver wake discharged through the §2 object-invisibility keystone (the
receiver is already `.ready` after the message store) and the caller deschedule
through `removeRunnableOnCore`'s object-store frame. -/
theorem endpointCallOnCore_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false caller st st' hInv hObjInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st' st'' caller _ _ hInv1 hObj1 hMsg
          show ipcInvariant (removeRunnableOnCore st'' caller executingCore)
          exact fun oid ntfn h => hInv2 oid ntfn (by rwa [removeRunnableOnCore_preserves_objects] at h)
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2.2 pair.1 hInv hObjInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2.2 st2 pair.1 _ _ hInv1 hObj1 hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hInvW : ipcInvariant (wakeThread st2 pair.1 executingCore).1 :=
            fun oid ntfn h => hInv2 oid ntfn
              (by rwa [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2 oid] at h)
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hInv4 := storeTcbIpcStateAndMessage_preserves_ipcInvariant
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hInvW hObjW hCS
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hInv5 := linkServerStashedReply_preserves_ipcInvariant st4 st5 caller pair.1 hInv4 hObjInv4 hLink
              show ipcInvariant (removeRunnableOnCore st5 caller executingCore)
              exact fun oid ntfn h => hInv5 oid ntfn (by rwa [removeRunnableOnCore_preserves_objects] at h)

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2 (per-core): the cross-core `wakeThread` of an already-`.ready`
thread frames the third clause — it is object-invisible
(`wakeThread_objects_getElem_eq_of_ready`).  Used for the receiver wake on
`endpointCallOnCore`'s rendezvous path (the receiver is `.ready` from the preceding
message store). -/
theorem wakeThread_preserves_blockedOnReplyHasReplyObject_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st) :
    blockedOnReplyHasReplyObject (wakeThread st wtid ec).1 := by
  intro tid tcb ep rt hTcb hBlk
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv tid.toObjId] at hTcb
  exact hInv tid tcb ep rt hTcb hBlk

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2 (per-core): `endpointCallOnCore` **establishes** the third clause
of `replyCallerLinkage` — the per-core analogue of
`endpointCall_establishes_blockedOnReplyHasReplyObject`.  Identical object-store backbone:
the per-core scheduler ops (`wakeThread` of the `.ready` receiver, `removeRunnableOnCore`)
are object-framing, so the same frame family composes (pop / non-blocked store / wake /
caller `.blockedOnReply` store breaking the clause only for the caller / atomic
`linkServerStashedReply` re-establishing it / `removeRunnableOnCore`). -/
theorem endpointCallOnCore_establishes_blockedOnReplyHasReplyObject
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : blockedOnReplyHasReplyObject st) (hObjInv : st.objects.invExt) :
    blockedOnReplyHasReplyObject (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hP1 := endpointQueueEnqueue_preserves_blockedOnReplyHasReplyObject endpointId false caller st st' hObjInv hInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hP2 := storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
            st' st'' caller (.blockedOnCall endpointId) (some msg) hObj1 hP1 (by simp) hMsg
          show blockedOnReplyHasReplyObject (removeRunnableOnCore st'' caller executingCore)
          exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnableOnCore_preserves_objects st'' caller executingCore) hP2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hP1 := endpointQueuePopHead_preserves_blockedOnReplyHasReplyObject endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hP2 := storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
            pair.2.2 st2 pair.1 .ready (some msg) hObj1 hP1 (by simp) hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hPW := wakeThread_preserves_blockedOnReplyHasReplyObject_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hP2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hThirdExc := storeTcbIpcStateAndMessage_off_preserves_blockedOnReplyHasReplyObject
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjW hPW hCS
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hP5 := linkServerStashedReply_establishes_blockedOnReplyHasReplyObject st4 st5 caller pair.1 hObjInv4 hThirdExc hLink
              show blockedOnReplyHasReplyObject (removeRunnableOnCore st5 caller executingCore)
              exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnableOnCore_preserves_objects st5 caller executingCore) hP5

open SeLe4n.Model.SystemState in
/-- D3 (per-core): the cross-core `wakeThread` of an already-`.ready` thread frames
`blockedOnReplyHasTarget`. -/
theorem wakeThread_preserves_blockedOnReplyHasTarget_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (wakeThread st wtid ec).1 := by
  intro tid tcb ep rt hTcb hBlk
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv tid.toObjId] at hTcb
  exact hInv tid tcb ep rt hTcb hBlk

-- IPC de-threading D8 (cross-core receive/reply prep): the scheduler-op frames for the
-- lookup-only conjuncts whose `removeRunnableOnCore`/`wakeThread` frames were not yet built
-- (`blockedOnReplyHasTarget` / `pendingReceiveReplyWellFormed` / `donationOwnerUnique`).  These are
-- consumed by the cross-core receive/reply bundles' Send-rendezvous (wake) and block (deschedule) legs.

/-- `removeRunnableOnCore` preserves `blockedOnReplyHasTarget` (pure scheduler op, objects unchanged). -/
theorem removeRunnableOnCore_preserves_blockedOnReplyHasTarget
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (removeRunnableOnCore st tid c) :=
  blockedOnReplyHasTarget_of_objects_eq (by rw [removeRunnableOnCore_preserves_objects]) h

/-- `removeRunnableOnCore` preserves `pendingReceiveReplyWellFormed` (objects unchanged). -/
theorem removeRunnableOnCore_preserves_pendingReceiveReplyWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed (removeRunnableOnCore st tid c) :=
  pendingReceiveReplyWellFormed_of_objects_eq (by rw [removeRunnableOnCore_preserves_objects]) h

/-- `removeRunnableOnCore` preserves `donationOwnerUnique` (objects unchanged). -/
theorem removeRunnableOnCore_preserves_donationOwnerUnique
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : donationOwnerUnique st) :
    donationOwnerUnique (removeRunnableOnCore st tid c) :=
  donationOwnerUnique_of_objects_eq (by rw [removeRunnableOnCore_preserves_objects]) h

/-- The cross-core wake of an already-`.ready` thread preserves `donationOwnerUnique`
(object-lookup-invisible re-insert — the §2 keystone — and the invariant reads only
`objects[·.toObjId]?`). -/
theorem wakeThread_preserves_donationOwnerUnique_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) (hInv : donationOwnerUnique st) :
    donationOwnerUnique (wakeThread st wtid ec).1 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv tid1.toObjId] at h1
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv tid2.toObjId] at h2
  exact hInv tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

open SeLe4n.Model.SystemState in
/-- D6 (per-core): a `wakeThread` of a `.ready` thread preserves every TCB's binding (its state
effect is `enqueueRunnableOnCore` — a scheduler-only step that leaves the object store
pointwise-unchanged for a `.ready` target). -/
theorem wakeThread_sameSchedContextBindings_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st (wakeThread st wtid ec).1 := by
  intro y tcY hY
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv y.toObjId] at hY
  exact ⟨tcY, hY, rfl⟩

open SeLe4n.Model.SystemState in
/-- D5 (per-core): a `wakeThread` of a `.ready` thread preserves every TCB's `timeoutBudget` (its
state effect is `enqueueRunnableOnCore` — a scheduler-only step leaving the object store
pointwise-unchanged for a `.ready` target). -/
theorem wakeThread_timeoutBudgetFrame_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    timeoutBudgetFrame st (wakeThread st wtid ec).1 := by
  intro y tcY hY
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv y.toObjId] at hY
  exact ⟨tcY, hY, rfl⟩

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `wakeThread` frames the SchedContext/owner side forward when the woken thread
is already `.ready` — it then leaves the object map element-wise unchanged. -/
theorem wakeThread_donationOwnerFrame_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    donationOwnerFrame st (wakeThread st wtid ec).1 :=
  ⟨fun scId sc hSc => by
     rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv scId.toObjId]; exact hSc,
   fun owner ownerTcb hOwner hU hR =>
     ⟨ownerTcb, by
       rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv owner.toObjId]; exact hOwner,
       hU, hR⟩⟩

/-- D6 (per-core): `enqueueRunnableOnCore` only *adds* `tid` to core `c`'s run queue — it never
removes any thread from any core's queue.  So every pre-state run-queue member is preserved. -/
theorem enqueueRunnableOnCore_mem_old (st : SystemState) (c c' : CoreId)
    (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runQueueOnCore c') :
    x ∈ (enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c' := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]; exact hMem
  | some tcb =>
    simp only [enqueueRunnableOnCore, hTcb]
    split
    · exact hMem
    · by_cases hcc : c' = c
      · subst hcc
        simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inl hMem)
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne st.scheduler c c' _ (Ne.symm hcc)]
        exact hMem

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `wakeThread` frames `passiveServerIdle` when the woken thread is already
`.ready`.  It then leaves the object map element-wise unchanged, preserves every core's `current`
(`enqueueRunnableOnCore_currentOnCore`), and only *adds* the woken thread to its target core's run
queue (`enqueueRunnableOnCore_mem_old`) — so every descheduled thread in the post-state was
descheduled in the pre-state.  No pullback exclusion is needed: even the woken thread pulls back
(its object is unchanged, and the wake cannot have *removed* it from the boot queue). -/
theorem wakeThread_passiveServerIdleFrame_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    passiveServerIdleFrame st (wakeThread st wtid ec).1 := by
  refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' _ => ?_⟩
  have hObjEq : (wakeThread st wtid ec).1.objects[tid.toObjId]? = st.objects[tid.toObjId]? :=
    wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv tid.toObjId
  refine ⟨tcb', by rw [← hObjEq]; exact hTcb', hUnbound', ?_, ?_, rfl⟩
  · intro hIn
    exact hNotInQ' (enqueueRunnableOnCore_mem_old st (determineTargetCore st wtid) bootCoreId wtid tid hIn)
  · rwa [show (wakeThread st wtid ec).1 = enqueueRunnableOnCore st (determineTargetCore st wtid) wtid from rfl,
      enqueueRunnableOnCore_currentOnCore st (determineTargetCore st wtid) wtid bootCoreId] at hNotCurrent'

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `removeRunnableOnCore` on core `c` frames `passiveServerIdle` given the removed
thread is **bound or already in an allowed state** (`hRemoved`).  The object map is untouched; the
only thread whose descheduled-status changes is the removed one (on core `c` — which may or may not
be the boot core), and the pullback filter excludes it. -/
theorem removeRunnableOnCore_passiveServerIdleFrame
    (st : SystemState) (removed : SeLe4n.ThreadId) (c : CoreId)
    (hRemoved : ∀ tcb, st.objects[removed.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed tcb.ipcState) :
    passiveServerIdleFrame st (removeRunnableOnCore st removed c) := by
  refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' hNA => ?_⟩
  rw [removeRunnableOnCore_preserves_objects st removed c] at hTcb'
  by_cases hEq : tid = removed
  · subst hEq
    rcases hRemoved tcb' hTcb' with hB | hA
    · exact absurd hUnbound' hB
    · exact absurd hA hNA
  · refine ⟨tcb', hTcb', hUnbound', ?_, ?_, rfl⟩
    · intro hIn
      apply hNotInQ'
      by_cases hcb : c = bootCoreId
      · subst hcb
        rw [removeRunnableOnCore_runQueueOnCore_self]
        exact (RunQueue.mem_remove _ _ _).mpr ⟨hIn, hEq⟩
      · rw [removeRunnableOnCore_runQueueOnCore_ne st removed c bootCoreId hcb]; exact hIn
    · intro hCur
      apply hNotCurrent'
      by_cases hcb : c = bootCoreId
      · subst hcb
        rw [removeRunnableOnCore_currentOnCore_self, hCur, if_neg (fun h => hEq (Option.some.inj h))]
      · rw [removeRunnableOnCore_currentOnCore_ne st removed c bootCoreId hcb]; exact hCur

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `endpointCallOnCore` preserves every TCB's `schedContextBinding` (the cross-core
mirror of `endpointCall_sameSchedContextBindings`; `wakeThread`/`removeRunnableOnCore` are
scheduler-only, the store/link ops never write a binding). -/
theorem endpointCallOnCore_sameSchedContextBindings
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact sameSchedContextBindings.refl st
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact sameSchedContextBindings.refl st
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact sameSchedContextBindings.refl st
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact sameSchedContextBindings.refl st
      | ok st' =>
        simp only
        have hS1 := endpointQueueEnqueue_sameSchedContextBindings endpointId false caller st st' hObjInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact sameSchedContextBindings.refl st
        | ok st'' =>
          simp only
          have hS2 := hS1.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings st' st'' caller (.blockedOnCall endpointId) (some msg) hObj1 hMsg)
          show sameSchedContextBindings st (removeRunnableOnCore st'' caller executingCore)
          exact hS2.trans (sameSchedContextBindings.of_objects_eq (removeRunnableOnCore_preserves_objects st'' caller executingCore))
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact sameSchedContextBindings.refl st
      | ok pair =>
        simp only
        have hS1 := endpointQueuePopHead_sameSchedContextBindings endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact sameSchedContextBindings.refl st
        | ok st2 =>
          simp only
          have hS2 := hS1.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg)
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hS3 := hS2.trans (wakeThread_sameSchedContextBindings_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2)
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact sameSchedContextBindings.refl st
          | ok st4 =>
            simp only
            have hS4 := hS3.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjW hCS)
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact sameSchedContextBindings.refl st
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hS5 := hS4.trans (linkServerStashedReply_sameSchedContextBindings st4 st5 caller pair.1 hObjInv4 hLink)
              show sameSchedContextBindings st (removeRunnableOnCore st5 caller executingCore)
              exact hS5.trans (sameSchedContextBindings.of_objects_eq (removeRunnableOnCore_preserves_objects st5 caller executingCore))

open SeLe4n.Model.SystemState in
/-- D5 (per-core): `endpointCallOnCore` frames `timeoutBudgetFrame` (the cross-core mirror of
`endpointCall_timeoutBudgetFrame`; `wakeThread`/`removeRunnableOnCore` are scheduler-only, the
store/link ops never write any TCB's `timeoutBudget`). -/
theorem endpointCallOnCore_timeoutBudgetFrame
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    timeoutBudgetFrame st (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact timeoutBudgetFrame.refl st
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact timeoutBudgetFrame.refl st
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact timeoutBudgetFrame.refl st
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact timeoutBudgetFrame.refl st
      | ok st' =>
        simp only
        have hS1 := endpointQueueEnqueue_timeoutBudgetFrame endpointId false caller st st' hObjInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact timeoutBudgetFrame.refl st
        | ok st'' =>
          simp only
          have hS2 := hS1.trans (storeTcbIpcStateAndMessage_timeoutBudgetFrame st' st'' caller (.blockedOnCall endpointId) (some msg) hObj1 hMsg)
          show timeoutBudgetFrame st (removeRunnableOnCore st'' caller executingCore)
          exact hS2.trans (timeoutBudgetFrame.of_objects_eq (removeRunnableOnCore_preserves_objects st'' caller executingCore))
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact timeoutBudgetFrame.refl st
      | ok pair =>
        simp only
        have hS1 := endpointQueuePopHead_timeoutBudgetFrame endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact timeoutBudgetFrame.refl st
        | ok st2 =>
          simp only
          have hS2 := hS1.trans (storeTcbIpcStateAndMessage_timeoutBudgetFrame pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg)
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hS3 := hS2.trans (wakeThread_timeoutBudgetFrame_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2)
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact timeoutBudgetFrame.refl st
          | ok st4 =>
            simp only
            have hS4 := hS3.trans (storeTcbIpcStateAndMessage_timeoutBudgetFrame (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjW hCS)
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact timeoutBudgetFrame.refl st
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hS5 := hS4.trans (linkServerStashedReply_timeoutBudgetFrame st4 st5 caller pair.1 hObjInv4 hLink)
              show timeoutBudgetFrame st (removeRunnableOnCore st5 caller executingCore)
              exact hS5.trans (timeoutBudgetFrame.of_objects_eq (removeRunnableOnCore_preserves_objects st5 caller executingCore))

open SeLe4n.Model.SystemState in
/-- IPC de-threading D5 (per-core): `endpointCallOnCore` preserves `blockedThreadTimeoutConsistent`
from the pre-state `allTimeoutBudgetsNone`. -/
theorem endpointCallOnCore_preserves_blockedThreadTimeoutConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hAll : allTimeoutBudgetsNone st) :
    blockedThreadTimeoutConsistent (endpointCallOnCore endpointId caller msg executingCore st).1 :=
  blockedThreadTimeoutConsistent_of_frame
    (endpointCallOnCore_timeoutBudgetFrame endpointId caller msg executingCore st hObjInv) hAll

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `endpointCallOnCore` frames `passiveServerIdle` (the cross-core mirror of
`endpointCall_passiveServerIdleFrame`).  Rendezvous: pop + complete the receiver `.ready` +
`wakeThread` it onto its home core (clean — only *adds* to a run queue) + set the caller
`.blockedOnReply` (allowed) + stash the reply + `removeRunnableOnCore` the caller.  Block: enqueue
the caller + set it `.blockedOnCall` (non-allowed) + `removeRunnableOnCore` — the descheduled
`.blockedOnCall` caller holds a SchedContext (`hCallerNotUnbound`).  The per-core `removeRunnableOnCore`
frames `passiveServerIdle` whether or not `executingCore` is the boot core (per-core locality). -/
theorem endpointCallOnCore_passiveServerIdleFrame
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        tcb.schedContextBinding ≠ .unbound) :
    passiveServerIdleFrame st (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact passiveServerIdleFrame.refl st
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact passiveServerIdleFrame.refl st
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact passiveServerIdleFrame.refl st
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact passiveServerIdleFrame.refl st
      | ok st' =>
        simp only
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        have hF1 := endpointQueueEnqueue_passiveServerIdleFrame endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact passiveServerIdleFrame.refl st
        | ok st'' =>
          simp only
          show passiveServerIdleFrame st (removeRunnableOnCore st'' caller executingCore)
          refine (hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrame st' st'' caller
            (.blockedOnCall endpointId) (some msg) (Or.inr (fun tcb hTcb => ?_)) hObj1 hMsg)).trans
            (removeRunnableOnCore_passiveServerIdleFrame st'' caller executingCore (fun tcb hTcb => Or.inl ?_))
          · obtain ⟨tcb0, hTcb0, hBindEq⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId false caller st st' hObjInv hEnq caller tcb hTcb
            exact hBindEq ▸ hCallerNotUnbound tcb0 hTcb0
          · obtain ⟨tcb1, hTcb1, hBindEq1⟩ := storeTcbIpcStateAndMessage_sameSchedContextBindings st' st'' caller (.blockedOnCall endpointId) (some msg) hObj1 hMsg caller tcb hTcb
            obtain ⟨tcb0, hTcb0, hBindEq0⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId false caller st st' hObjInv hEnq caller tcb1 hTcb1
            exact hBindEq1 ▸ hBindEq0 ▸ hCallerNotUnbound tcb0 hTcb0
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact passiveServerIdleFrame.refl st
      | ok pair =>
        simp only
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hF1 := endpointQueuePopHead_passiveServerIdleFrame endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact passiveServerIdleFrame.refl st
        | ok st2 =>
          simp only
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          have hF2 := hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrame pair.2.2 st2 pair.1
            .ready (some msg) (Or.inl (Or.inl rfl)) hObj1 hMsg)
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hF3 := hF2.trans (wakeThread_passiveServerIdleFrame_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2)
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact passiveServerIdleFrame.refl st
          | ok st4 =>
            simp only
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            have hF4 := hF3.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrame
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1)) none
              (Or.inl (Or.inr (Or.inr ⟨endpointId, some pair.1, rfl⟩))) hObjW hCS)
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact passiveServerIdleFrame.refl st
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              show passiveServerIdleFrame st (removeRunnableOnCore st5 caller executingCore)
              have hF5 := hF4.trans (linkServerStashedReply_passiveServerIdleFrame st4 st5 caller pair.1 hObjInv4 hLink)
              refine hF5.trans (removeRunnableOnCore_passiveServerIdleFrame st5 caller executingCore (fun tcb hTcb => Or.inr ?_))
              obtain ⟨tcb4, hTcb4, hIpc4⟩ := linkServerStashedReply_tcb_ipcState_backward st4 st5 caller pair.1 caller tcb hObjInv4 hLink hTcb
              have hRep := storeTcbIpcStateAndMessage_ipcState_eq (wakeThread st2 pair.1 executingCore).1 st4 caller _ none hObjW hCS tcb4 hTcb4
              rw [← hIpc4, hRep]; exact Or.inr (Or.inr ⟨endpointId, some pair.1, rfl⟩)

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `endpointCallOnCore` preserves `passiveServerIdle`. -/
theorem endpointCallOnCore_preserves_passiveServerIdle
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        tcb.schedContextBinding ≠ .unbound)
    (hInv : passiveServerIdle st) :
    passiveServerIdle (endpointCallOnCore endpointId caller msg executingCore st).1 :=
  passiveServerIdle_of_frame
    (endpointCallOnCore_passiveServerIdleFrame endpointId caller msg executingCore st hObjInv hCallerNotUnbound) hInv

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `endpointCallOnCore` frames the SchedContext/owner side forward (cross-core
mirror of `endpointCall_donationOwnerFrame`).  The rendezvous receiver is the receiveQ **head**
(`.blockedOnReceive` via `hQHBC`) and the caller is running (`hCallerNotReply`); `wakeThread`
(woken thread `.ready`) and `removeRunnableOnCore` leave the object map unchanged. -/
theorem endpointCallOnCore_donationOwnerFrame
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hQHBC : queueHeadBlockedConsistent st)
    (hCallerNotReply : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt) :
    donationOwnerFrame st (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact donationOwnerFrame.refl st
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact donationOwnerFrame.refl st
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact donationOwnerFrame.refl st
  | some ep =>
    simp only
    have hObjEp : st.objects[endpointId]? = some (.endpoint ep) := (getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact donationOwnerFrame.refl st
      | ok st' =>
        simp only
        have hF1 := endpointQueueEnqueue_donationOwnerFrame endpointId false caller st st' hObjInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact donationOwnerFrame.refl st
        | ok st'' =>
          simp only
          show donationOwnerFrame st (removeRunnableOnCore st'' caller executingCore)
          refine (hF1.trans (storeTcbIpcStateAndMessage_donationOwnerFrame st' st'' caller (.blockedOnCall endpointId) (some msg)
            (fun tcb hTcb_s1 ep' rt => ?_) hObj1 hMsg)).trans
            (donationOwnerFrame.of_objects_eq (removeRunnableOnCore_preserves_objects st'' caller executingCore))
          obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueueEnqueue_tcb_ipcState_backward endpointId false caller st st'
            caller tcb hObjInv hEnq hTcb_s1
          exact fun hc => hCallerNotReply tcb0 hTcb0 ep' rt (hIpc0.trans hc)
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact donationOwnerFrame.refl st
      | ok pair =>
        simp only
        have hF1 := endpointQueuePopHead_donationOwnerFrame endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hHeadEq := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObjEp hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact donationOwnerFrame.refl st
        | ok st2 =>
          simp only
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          have hF2 := storeTcbIpcStateAndMessage_donationOwnerFrame pair.2.2 st2 pair.1 .ready (some msg)
            (fun tcb hTcb_p ep' rt => by
              obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId true st
                pair.2.2 pair.1 pair.1 tcb hObjInv hPop hTcb_p
              have hBlk := (hQHBC endpointId ep pair.1 tcb0 hObjEp hTcb0).1 (by simpa using hHeadEq)
              intro hc
              have hRecv : tcb.ipcState = .blockedOnReceive endpointId := hIpc0 ▸ hBlk
              rw [hc] at hRecv; cases hRecv) hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hF3 := wakeThread_donationOwnerFrame_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact donationOwnerFrame.refl st
          | ok st4 =>
            simp only
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            have hF4 := storeTcbIpcStateAndMessage_donationOwnerFrame (wakeThread st2 pair.1 executingCore).1 st4 caller
              (.blockedOnReply endpointId (some pair.1)) none
              (fun tcb hTcb_w ep' rt => by
                rw [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2 caller.toObjId] at hTcb_w
                by_cases hCR : caller.toObjId = pair.1.toObjId
                · have hReady := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg)
                    hObj1 hMsg tcb (hCR ▸ hTcb_w)
                  intro hc; rw [hReady] at hc; cases hc
                · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready
                    (some msg) caller.toObjId hCR hObj1 hMsg).symm.trans hTcb_w
                  obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId true st
                    pair.2.2 pair.1 caller tcb hObjInv hPop hTcbPre
                  exact fun hc => hCallerNotReply tcb0 hTcb0 ep' rt (hIpc0.trans hc)) hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact donationOwnerFrame.refl st
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hF5 := linkServerStashedReply_donationOwnerFrame st4 st5 caller pair.1 hObjInv4 hLink
              show donationOwnerFrame st (removeRunnableOnCore st5 caller executingCore)
              exact ((((hF1.trans hF2).trans hF3).trans hF4).trans hF5).trans
                (donationOwnerFrame.of_objects_eq (removeRunnableOnCore_preserves_objects st5 caller executingCore))

open SeLe4n.Model.SystemState in
/-- D3 (per-core): `endpointCallOnCore` **establishes** `blockedOnReplyHasTarget`. -/
theorem endpointCallOnCore_establishes_blockedOnReplyHasTarget
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : blockedOnReplyHasTarget st) (hObjInv : st.objects.invExt) :
    blockedOnReplyHasTarget (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hP1 := endpointQueueEnqueue_preserves_blockedOnReplyHasTarget endpointId false caller st st' hObjInv hInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
            st' st'' caller (.blockedOnCall endpointId) (some msg) hObj1 hP1 (by intro ep rt h; cases h) hMsg
          show blockedOnReplyHasTarget (removeRunnableOnCore st'' caller executingCore)
          exact blockedOnReplyHasTarget_of_objects_eq (removeRunnableOnCore_preserves_objects st'' caller executingCore) hP2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hP1 := endpointQueuePopHead_preserves_blockedOnReplyHasTarget endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
            pair.2.2 st2 pair.1 .ready (some msg) hObj1 hP1 (by intro ep rt h; cases h) hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hPW := wakeThread_preserves_blockedOnReplyHasTarget_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hP2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hP4 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjW hPW (by rintro ep rt h; cases h; rfl) hCS
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hP5 := linkServerStashedReply_preserves_blockedOnReplyHasTarget st4 st5 caller pair.1 hObjInv4 hP4 hLink
              show blockedOnReplyHasTarget (removeRunnableOnCore st5 caller executingCore)
              exact blockedOnReplyHasTarget_of_objects_eq (removeRunnableOnCore_preserves_objects st5 caller executingCore) hP5

-- ============================================================================
-- §4  SM6.A.9 — invariant preservation *through* the 2PL lock bracket
-- ============================================================================

/-- WS-SM SM6.A.9 (atomicity, invariant form): under its `withLockSet` bracket
the cross-core endpoint call preserves object-store integrity **through the
entire 2PL acquire/release fold**, not merely the bare action.  Composes the
bare-action `endpointCallOnCore_preserves_objects_invExt` with the lock-acquire /
lock-release insensitivity of `invExt` via the SM3.C.8 metatheorem
`withLockSet_invariant_preserved`.  This is the substantive content behind
"atomic under lock-set": no lock-bookkeeping step of the bracket disturbs the
object-store well-formedness the transition relies on. -/
theorem endpointCallOnCore_withLockSet_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (cnRoot : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId)
    (s : SystemState) (hObjInv : s.objects.invExt) :
    (withLockSet (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?)
        executingCore (endpointCallOnCore endpointId caller msg executingCore) s).1.objects.invExt :=
  withLockSet_invariant_preserved _ executingCore _ s (fun st => st.objects.invExt) hObjInv
    (fun l m s' h => acquireLockOnObject_preserves_invExt s' executingCore l m h)
    (fun s' h => endpointCallOnCore_preserves_objects_invExt endpointId caller msg executingCore s' h)
    (fun l m s' h => releaseLockOnObject_preserves_invExt s' executingCore l m h)

-- ============================================================================
-- §5  Lookup-congruence for the dual-queue structural invariant
-- ============================================================================

/-! `dualQueueSystemInvariant` and its sub-predicates read the system state
*only* through `objects[·]?` lookups — never the scheduler, machine, or
per-core state.  Hence any two states whose object lookups agree pointwise
satisfy them interchangeably.  These congruences are what let the cross-core
wake (object-invisible on a `.ready` thread) and `removeRunnableOnCore`
(object-store frame) carry the dual-queue invariant for free: neither touches
an object lookup, so neither can disturb a lookup-only predicate.  (Distinct
from the existing `*_of_objects_eq` family, which needs *structural* object
equality; the cross-core wake only delivers pointwise lookup equality, since a
Robin-Hood re-insert of an identical value may differ in array representation
while agreeing on every lookup.) -/

/-- Pointwise-lookup transport of a `queueNext` reachability path. -/
theorem QueueNextPath_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath s2 a b) : QueueNextPath s1 a b := by
  induction hp with
  | single x y tcbA hObj hNext => exact .single x y tcbA (by rw [← hEq]; exact hObj) hNext
  | cons x y z tcbA hObj hNext _ ih => exact .cons x y z tcbA (by rw [← hEq]; exact hObj) hNext ih

/-- Pointwise-lookup transport of TCB-queue chain acyclicity. -/
theorem tcbQueueChainAcyclic_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : tcbQueueChainAcyclic s1) : tcbQueueChainAcyclic s2 :=
  fun tid hp => h tid (QueueNextPath_of_getElem_eq hEq hp)

/-- Pointwise-lookup transport of doubly-linked TCB-queue link integrity. -/
theorem tcbQueueLinkIntegrity_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : tcbQueueLinkIntegrity s1) : tcbQueueLinkIntegrity s2 := by
  obtain ⟨hFwd, hRev⟩ := h
  refine ⟨fun a tcbA hA b hNext => ?_, fun b tcbB hB a hPrev => ?_⟩
  · rw [hEq] at hA
    obtain ⟨tcbB, hB, hPrev⟩ := hFwd a tcbA hA b hNext
    exact ⟨tcbB, by rw [hEq]; exact hB, hPrev⟩
  · rw [hEq] at hB
    obtain ⟨tcbA, hA, hNext⟩ := hRev b tcbB hB a hPrev
    exact ⟨tcbA, by rw [hEq]; exact hA, hNext⟩

/-- Pointwise-lookup transport of single-queue well-formedness. -/
theorem intrusiveQueueWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) {q : IntrusiveQueue}
    (h : intrusiveQueueWellFormed q s1) : intrusiveQueueWellFormed q s2 := by
  obtain ⟨hP1, hP2, hP3⟩ := h
  refine ⟨hP1, fun hd hHead => ?_, fun tl hTail => ?_⟩
  · obtain ⟨tcb, hObj, hPrev⟩ := hP2 hd hHead
    exact ⟨tcb, by rw [hEq]; exact hObj, hPrev⟩
  · obtain ⟨tcb, hObj, hNext⟩ := hP3 tl hTail
    exact ⟨tcb, by rw [hEq]; exact hObj, hNext⟩

/-- Pointwise-lookup transport of an endpoint's dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) {epId : SeLe4n.ObjId}
    (h : dualQueueEndpointWellFormed epId s1) : dualQueueEndpointWellFormed epId s2 := by
  unfold dualQueueEndpointWellFormed at h ⊢
  rw [hEq]
  revert h
  cases s1.objects[epId]? with
  | none => exact fun _ => trivial
  | some obj =>
    cases obj with
    | endpoint ep =>
      exact fun h => ⟨intrusiveQueueWellFormed_of_getElem_eq hEq h.1,
                      intrusiveQueueWellFormed_of_getElem_eq hEq h.2⟩
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ | reply _ =>
      exact fun _ => trivial

/-- WS-SM SM6.A.1: the dual-queue system invariant is preserved by any state
change that leaves every object lookup intact.  Assembles the four sub-predicate
congruences above. -/
theorem dualQueueSystemInvariant_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : dualQueueSystemInvariant s1) : dualQueueSystemInvariant s2 := by
  obtain ⟨hEp, hLink, hAcyc⟩ := h
  refine ⟨fun epId ep hObj => ?_,
          tcbQueueLinkIntegrity_of_getElem_eq hEq hLink,
          tcbQueueChainAcyclic_of_getElem_eq hEq hAcyc⟩
  rw [hEq] at hObj
  exact dualQueueEndpointWellFormed_of_getElem_eq hEq (hEp epId ep hObj)

-- ============================================================================
-- §6  SM6.A.1 — `dualQueueSystemInvariant` preservation
-- ============================================================================

/-- `removeRunnableOnCore` preserves the dual-queue invariant: it is an
object-store frame (`objects` unchanged), and the invariant is lookup-only. -/
theorem removeRunnableOnCore_preserves_dualQueueSystemInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (removeRunnableOnCore st tid c) :=
  dualQueueSystemInvariant_of_getElem_eq
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- The cross-core wake of an already-`.ready` thread preserves the dual-queue
invariant: the wake's `ipcState := .ready` re-insert is object-lookup-invisible
(the §2 keystone), and the invariant is lookup-only. -/
theorem wakeThread_preserves_dualQueueSystemInvariant_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (wakeThread st tid ec).1 :=
  dualQueueSystemInvariant_of_getElem_eq
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves the **dual-queue
system invariant** (endpoint queue well-formedness + TCB-queue link integrity +
chain acyclicity).  Mirrors the single-core
`endpointCall_preserves_dualQueueSystemInvariant`, with the receiver wake
discharged through the lookup-only congruence (the receiver is `.ready` after
the message store, so `wakeThread` is object-invisible) and the caller
deschedule through `removeRunnableOnCore`'s object-store frame.  The freshness
side-conditions (`hFreshCaller`, `hSendTailFresh`) are exactly those the
single-core theorem requires for the no-receiver enqueue. -/
theorem endpointCallOnCore_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : dualQueueSystemInvariant st) (hObjInv : st.objects.invExt)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hInv1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
          endpointId false caller st st' hEnq hInv hObjInv hFreshCaller hSendTailFresh
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt
          endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
            st' st'' caller _ _ hObj1 hMsg hInv1
          show dualQueueSystemInvariant (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_dualQueueSystemInvariant st'' caller executingCore hInv2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
          endpointId true st pair.2.2 pair.1 hObjInv hPop hInv
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
            pair.2.2 st2 pair.1 _ _ hObj1 hMsg hInv1
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hInvW := wakeThread_preserves_dualQueueSystemInvariant_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hInv2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hInv4 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS hInvW
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hInv5 := linkServerStashedReply_preserves_dualQueueSystemInvariant st4 st5 caller pair.1 hObjInv4 hLink hInv4
              show dualQueueSystemInvariant (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_dualQueueSystemInvariant st5 caller executingCore hInv5

-- ============================================================================
-- WS-SM SM6.D / IPC de-threading D8: cross-core RECEIVE bundle establishers.
-- `endpointReceiveDualOnCore` mirrors the single-core `endpointReceiveDual` (the
-- Call-rendezvous leg is identical; the Send-rendezvous swaps `ensureRunnable` →
-- the object-invisible `wakeThread`, and the block leg swaps `removeRunnable` →
-- `removeRunnableOnCore`).  These reuse the single-core per-step lemmas + the
-- cross-core scheduler-op frames above.
-- ============================================================================

-- (The `simp only [h…]` reductions mirror the single-core hyp-based template applied to the
-- goal; the per-branch `cases h…` already substitutes the scrutinee, so the named args are a
-- harmless redundancy — the linter is scoped off for this transcription rather than diverging
-- from the single-core structure.)
set_option linter.unusedSimpArgs false in
/-- Cross-core receive preserves `dualQueueSystemInvariant`. -/
theorem endpointReceiveDualOnCore_preserves_dualQueueSystemInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) (hInv : dualQueueSystemInvariant st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid)) :
    dualQueueSystemInvariant (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 := by
  unfold endpointReceiveDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only [hEp]; split <;> exact hInv
  | some ep =>
    simp only [hEp]
    cases hHead : ep.sendQ.head with
    | some sndr =>
      simp only [hHead]
      cases hPop : endpointQueuePopHead endpointId false st with
      | error e => simp only [hPop]; exact hInv
      | ok pair =>
        simp only [hPop]
        have hInv1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
          _ _ _ _ _ hObjInv hPop hInv
        have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
        cases hSenderIpc : pair.2.1.ipcState with
        | blockedOnCall epCall =>
          simp only [hSenderIpc, ite_true]
          cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1
              (.blockedOnReply endpointId (some receiver)) none with
          | error e => simp only [hStore]; exact hInv
          | ok st2 =>
            simp only [hStore]
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hStore
            have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hStore hInv1
            cases hReplyId : replyId with
            | none => simp only [hReplyId]; exact hInv
            | some rid =>
              simp only [hReplyId]
              cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
              | error e => simp only [hLink]; exact hInv
              | ok pLink =>
                obtain ⟨_, stLinked⟩ := pLink
                simp only [hLink]
                have hObjInvLink := linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInv2 hLink
                have hInvLink := linkCallerReply_preserves_dualQueueSystemInvariant
                  st2 stLinked pair.1 rid hObjInv2 hLink hInv2
                cases hMsg : storeTcbIpcStateAndMessage stLinked receiver .ready pair.2.1.pendingMessage with
                | error e => simp only [hMsg]; exact hInv
                | ok st3 =>
                  simp only [hMsg]
                  exact storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                    stLinked _ receiver .ready pair.2.1.pendingMessage hObjInvLink hMsg hInvLink
        | ready | blockedOnSend _ | blockedOnReceive _
          | blockedOnReply _ _ | blockedOnNotification _ =>
          simp only [hSenderIpc]
          cases hStore : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
          | error e => simp only [hStore]; exact hInv
          | ok st2 =>
            simp only [hStore]
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              pair.2.2 st2 pair.1 .ready none hObjInv1 hStore
            have hInv2 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
              pair.2.2 st2 pair.1 .ready none hObjInv1 hStore hInv1
            obtain ⟨tr, hTrGet, hTrReady⟩ :=
              storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready none hObjInv1 hStore
            have hInvW := wakeThread_preserves_dualQueueSystemInvariant_of_ready
              st2 pair.1 executingCore tr hTrGet hTrReady hObjInv2 hInv2
            have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObjInv2
            cases hMsg : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 receiver .ready
                pair.2.1.pendingMessage with
            | error e => simp only [hMsg]; exact hInv
            | ok st4 =>
              simp only [hMsg]
              exact storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant
                (wakeThread st2 pair.1 executingCore).1 _ receiver .ready pair.2.1.pendingMessage hObjW hMsg hInvW
    | none =>
      simp only [hHead]
      cases hChecked : cleanupPreReceiveDonationChecked st receiver with
      | error _ => simp only [hChecked]; exact hInv
      | ok stClean =>
        have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
          (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
        simp only [hChecked]
        rw [hBridge]
        have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
        have hInvClean := cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hInv
        have hFreshReceiverClean : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
            (cleanupPreReceiveDonation st receiver).objects[epId]? = some (.endpoint ep) →
            ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
            ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver :=
          fun epId ep hEp =>
            hFreshReceiver epId ep (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId ep hEp)
        have hRecvTailFreshClean : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
            (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep) →
            ep.receiveQ.tail = some tailTid →
            ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
              (cleanupPreReceiveDonation st receiver).objects[epId']? = some (.endpoint ep') →
              (epId' ≠ endpointId →
                ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
              (epId' = endpointId →
                ep'.sendQ.tail ≠ some tailTid) :=
          fun ep tailTid hEp hTail epId' ep' hEp' =>
            hRecvTailFresh ep tailTid
              (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv endpointId ep hEp) hTail
              epId' ep'
              (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId' ep' hEp')
        cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
        | error e => simp only [hEnq]; exact hInv
        | ok st1 =>
          simp only [hEnq]
          have hInv1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq hInvClean hObjInvClean
            hFreshReceiverClean hRecvTailFreshClean
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
          cases hStore : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp only [hStore]; exact hInv
          | ok st2 =>
            simp only [hStore]
            have hInv2 := storeTcbIpcState_preserves_dualQueueSystemInvariant st1 st2 receiver _ hObjInv1 hStore hInv1
            have hObjInv2 := storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInv1 hStore
            cases hGetR : st2.getTcb? receiver with
            | none =>
              simp only [hGetR]
              exact removeRunnableOnCore_preserves_dualQueueSystemInvariant _ receiver executingCore hInv2
            | some rTcb =>
              simp only [hGetR]
              cases hStash : storeObject receiver.toObjId
                  (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
              | error e => simp only [hStash]; exact hInv
              | ok pStash =>
                obtain ⟨_, stStashed⟩ := pStash
                simp only [hStash]
                have hTcbPre : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                  (SystemState.getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                exact removeRunnableOnCore_preserves_dualQueueSystemInvariant _ receiver executingCore
                  (storeObject_tcb_preserves_dualQueueSystemInvariant_of_queueAgree
                    st2 stStashed receiver.toObjId rTcb
                    { rTcb with pendingReceiveReply := replyId } rfl rfl
                    hTcbPre hObjInv2 hStash hInv2)

/-- IPC de-threading D8: `removeRunnableOnCore` preserves `endpointQueueNoDup`
(objects unchanged — pure scheduler op). -/
theorem removeRunnableOnCore_preserves_endpointQueueNoDup
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : endpointQueueNoDup st) :
    endpointQueueNoDup (removeRunnableOnCore st tid c) :=
  endpointQueueNoDup_of_objects_eq st _
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- IPC de-threading D8: the cross-core wake of an already-`.ready` thread preserves
`endpointQueueNoDup` — the wake's `ipcState := .ready` re-insert is object-lookup-invisible
(the §2 keystone), and the invariant is lookup-only. -/
theorem wakeThread_preserves_endpointQueueNoDup_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : endpointQueueNoDup st) :
    endpointQueueNoDup (wakeThread st tid ec).1 :=
  endpointQueueNoDup_of_objects_eq st _
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

/-- WS-SM SM6.A.1 / IPC de-threading D8: the cross-core endpoint call preserves
`endpointQueueNoDup`. Mirrors `endpointCallOnCore_preserves_dualQueueSystemInvariant`,
threading the noDup chain alongside the dual-queue side-conditions the per-step noDup
lemmas require (the enqueue/pop lemmas key K-1 self-loop-freedom off the post-state
`dualQueueSystemInvariant`). The receiver wake is object-invisible (`.ready`), the caller
deschedule is a scheduler op. -/
theorem endpointCallOnCore_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : endpointQueueNoDup st) (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    endpointQueueNoDup (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
      (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hDQ1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
          endpointId false caller st st' hEnq hDQSI hObjInv hFreshCaller hSendTailFresh
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt
          endpointId false caller st st' hObjInv hEnq
        have hND1 := endpointQueueEnqueue_preserves_endpointQueueNoDup
          endpointId false caller st st' hInv hDQ1 hObjInv
          (by
            intro ep' hEp'
            have hee : ep = ep' := by simpa using hEpObj.symm.trans hEp'
            subst hee; simpa using hHead) hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hND2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup
            st' st'' caller _ _ hND1 hObj1 hMsg
          show endpointQueueNoDup (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_endpointQueueNoDup st'' caller executingCore hND2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hDQ1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant
          endpointId true st pair.2.2 pair.1 hObjInv hPop hDQSI
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hND1 := endpointQueuePopHead_preserves_endpointQueueNoDup
          endpointId true st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQ1 hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hND2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup
            pair.2.2 st2 pair.1 _ _ hND1 hObj1 hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hNDW := wakeThread_preserves_endpointQueueNoDup_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hND2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hND4 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hNDW hObjW hCS
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hND5 := linkServerStashedReply_preserves_endpointQueueNoDup st4 st5 caller pair.1 hND4 hObjInv4 hLink
              show endpointQueueNoDup (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_endpointQueueNoDup st5 caller executingCore hND5

/-- IPC de-threading D8: `removeRunnableOnCore` preserves `ipcStateQueueMembershipConsistent`
(objects unchanged — pure scheduler op). -/
theorem removeRunnableOnCore_preserves_ipcStateQueueMembershipConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent (removeRunnableOnCore st tid c) :=
  ipcStateQueueMembershipConsistent_of_objects_eq st _
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- IPC de-threading D8: the cross-core wake of an already-`.ready` thread preserves
`ipcStateQueueMembershipConsistent` (object-lookup-invisible re-insert). -/
theorem wakeThread_preserves_ipcStateQueueMembershipConsistent_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent (wakeThread st tid ec).1 :=
  ipcStateQueueMembershipConsistent_of_objects_eq st _
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

/-- WS-SM SM6.A.1 / IPC de-threading D8: the cross-core endpoint call preserves
`ipcStateQueueMembershipConsistent`. Mirrors the single-core
`endpointCall_preserves_ipcStateQueueMembershipConsistent`: the rendezvous pop yields
membership-except-head (the head is the `.blockedOnReceive` receiveQ head by `hQHBC`), the
head is set `.ready` (its obligation collapses to `True`, restoring full membership), the wake
is object-invisible, the caller is set `.blockedOnCall` and its sendQ membership is recovered
from `endpointQueueEnqueue_thread_reachable`; the deschedule is a scheduler op. -/
theorem endpointCallOnCore_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInvFull : ipcInvariantFull st) (hObjInv : st.objects.invExt)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    ipcStateQueueMembershipConsistent (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    have hObj : st.objects[endpointId]? = some (.endpoint ep) :=
      (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
    cases hHead : ep.receiveQ.head with
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
        have hHeadBlocked : pair.2.1.ipcState = .blockedOnReceive endpointId := by
          have hRetH := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObj hPop
          have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep pair.1 pair.2.1 pair.2.2 hObj hPop
          exact (hQHBC endpointId ep pair.1 pair.2.1 hObj hPreTcb).1 hRetH
        have hPartialV3J := endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
          endpointId true st pair.2.2 pair.1 pair.2.1 ep hInv hObjInv hQNBC hObj
          (by simp only [↓reduceIte]; exact hHeadBlocked) hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg
          have hV3J2 := storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
            pair.2.2 st2 pair.1 .ready (some msg) hPartialV3J hObjInv1
            (fun epId h => absurd h (by simp))
            (fun epId h => absurd h (by simp))
            (fun epId h => absurd h (by simp)) hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg
          have hV3JW := wakeThread_preserves_ipcStateQueueMembershipConsistent_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObjInv2 hV3J2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObjInv2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hV3J4 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                _ st4 caller _ none hV3JW hObjW
                (fun _ h => absurd h (by simp))
                (fun _ h => absurd h (by simp))
                (fun _ h => absurd h (by simp)) hCS
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st4 caller _ none hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hV3J5 := linkServerStashedReply_preserves_ipcStateQueueMembershipConsistent st4 st5 caller pair.1 hV3J4 hObjInv4 hLink
              show ipcStateQueueMembershipConsistent (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_ipcStateQueueMembershipConsistent st5 caller executingCore hV3J5
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st1 =>
        simp only
        have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
          endpointId false caller st st1 hObjInv hEnq
        have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
          endpointId false caller st st1 hInv hObjInv hDQWF hEnq
        have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
          endpointId false caller st st1 hEnq hDQSI hObjInv hFreshCaller hSendTailFresh
        have hNotTail : ∀ ep', st.objects[endpointId]? = some (.endpoint ep') →
            (if false then ep'.receiveQ else ep'.sendQ).tail ≠ some caller := by
          intro ep' hEp'
          rw [hObj] at hEp'; cases hEp'
          exact (hFreshCaller endpointId ep hObj).2.1
        have hReach := endpointQueueEnqueue_thread_reachable
          endpointId false caller st st1 hObjInv hNotTail hEnq
        cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hNeCallerEp : endpointId ≠ caller.toObjId := by
            intro h; unfold endpointQueueEnqueue at hEnq
            rw [hObj] at hEnq; simp only at hEnq
            cases hL : lookupTcb st caller with
            | none => simp [hL] at hEnq
            | some tcb =>
              have := lookupTcb_some_objects st caller tcb hL
              rw [← h, hObj] at this; cases this
          show ipcStateQueueMembershipConsistent (removeRunnableOnCore st2 caller executingCore)
          exact removeRunnableOnCore_preserves_ipcStateQueueMembershipConsistent st2 caller executingCore <|
            storeTcbIpcStateAndMessage_general_preserves_ipcStateQueueMembershipConsistent
              st1 st2 caller (.blockedOnCall endpointId) (some msg) hV3J1 hObjInv1 hMsg
              (fun _ h => absurd h (by simp))
              (fun _ h => absurd h (by simp))
              (fun epId hEq => by
                cases hEq
                obtain ⟨ep', hEp1, hR⟩ := hReach
                have hEpFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
                  st1 st2 caller (.blockedOnCall endpointId) (some msg)
                  endpointId hNeCallerEp hObjInv1 hMsg
                rw [hEpFrame]
                exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                  refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                  have hNePrev : prev.toObjId ≠ caller.toObjId := by
                    intro h
                    have hPrevEq := ThreadId.toObjId_injective prev caller h
                    rw [hPrevEq] at hP
                    exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 caller prevTcb hP)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne
                    st1 st2 caller (.blockedOnCall endpointId) (some msg)
                    prev.toObjId hNePrev hObjInv1 hMsg]
                  exact hP⟩)

/-- IPC de-threading D4 Slice 2b: `removeRunnableOnCore` preserves
`queueNextBlockingConsistent` (object-store frame — `objects` unchanged). -/
theorem removeRunnableOnCore_preserves_queueNextBlockingConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (removeRunnableOnCore st tid c) :=
  queueNextBlockingConsistent_of_objects_eq st (removeRunnableOnCore st tid c)
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- IPC de-threading D4 Slice 2b: the cross-core wake of an already-`.ready` thread
preserves `queueNextBlockingConsistent` (the wake's `ipcState := .ready` re-insert is
object-lookup-invisible — the §2 keystone — and the invariant is lookup-only). -/
theorem wakeThread_preserves_queueNextBlockingConsistent_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (wakeThread st tid ec).1 :=
  queueNextBlockingConsistent_of_objects_eq st (wakeThread st tid ec).1
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

/-- IPC de-threading D4 Slice 2c: `removeRunnableOnCore` frames `queueHeadBlockedConsistent`
(object-store frame — `objects` unchanged). -/
theorem removeRunnableOnCore_preserves_queueHeadBlockedConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent (removeRunnableOnCore st tid c) :=
  queueHeadBlockedConsistent_of_endpoint_tcb_backward st (removeRunnableOnCore st tid c)
    (fun _ _ hEp => by rwa [removeRunnableOnCore_preserves_objects] at hEp)
    (fun _ _ hY => ⟨_, by rwa [removeRunnableOnCore_preserves_objects] at hY, rfl⟩) h

/-- IPC de-threading D4 Slice 2c: `removeRunnableOnCore` frames `queueNextTargetBlocked`
(object-store frame — `objects` unchanged). -/
theorem removeRunnableOnCore_preserves_queueNextTargetBlocked
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : queueNextTargetBlocked st) :
    queueNextTargetBlocked (removeRunnableOnCore st tid c) :=
  queueNextTargetBlocked_of_objects_eq st (removeRunnableOnCore st tid c)
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- IPC de-threading D4 Slice 2c: the cross-core wake of an already-`.ready` thread preserves
`queueHeadBlockedConsistent` (the wake's `ipcState := .ready` re-insert is object-lookup-invisible —
the §2 keystone — and the invariant is lookup-only). -/
theorem wakeThread_preserves_queueHeadBlockedConsistent_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent (wakeThread st tid ec).1 :=
  queueHeadBlockedConsistent_of_endpoint_tcb_backward st (wakeThread st tid ec).1
    (fun eid _ hEp => by
      rwa [wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv eid] at hEp)
    (fun y _ hY => ⟨_, by
      rwa [wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv y.toObjId] at hY,
      rfl⟩) h

/-- IPC de-threading D4 Slice 2c: the cross-core wake of an already-`.ready` thread preserves
`queueNextTargetBlocked` (object-lookup-invisible §2 keystone; lookup-only invariant). -/
theorem wakeThread_preserves_queueNextTargetBlocked_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : queueNextTargetBlocked st) :
    queueNextTargetBlocked (wakeThread st tid ec).1 :=
  queueNextTargetBlocked_of_objects_eq st (wakeThread st tid ec).1
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

open SeLe4n.Model.SystemState in
/-- IPC de-threading D4 Slice 2b: the cross-core endpoint call **establishes**
`queueNextBlockingConsistent`.  Mirrors the single-core
`endpointCall_preserves_queueNextBlockingConsistent` (block branch: sendQ enqueue +
`.blockedOnCall` block-store discharged via core (b)
`endpointQueueEnqueue_predecessor_blocked`; rendezvous branch: receiveQ pop + receiver
`.ready` store + caller `.blockedOnReply` store [`queueNextBlockingMatch` catch-all] +
`linkServerStashedReply`), with the receiver wake framed by
`wakeThread_preserves_queueNextBlockingConsistent_of_ready` (the receiver is `.ready`
after its message store, so the wake is object-invisible) and the caller deschedule by
`removeRunnableOnCore`'s object-store frame.  `hFreshCaller` / `hSendTailFresh` are the
no-receiver-enqueue side-conditions inherited from the dual-queue step. -/
theorem endpointCallOnCore_preserves_queueNextBlockingConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : queueNextBlockingConsistent st)
    (hDQSI : dualQueueSystemInvariant st)
    (hTail : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    queueNextBlockingConsistent (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    have hObjEp : st.objects[endpointId]? = some (.endpoint ep) :=
      (getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hInv1 := endpointQueueEnqueue_preserves_queueNextBlockingConsistent
          endpointId false caller st st' hObjInv hInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt
          endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent
            st' st'' caller (.blockedOnCall endpointId) (some msg) hInv1 hObj1 hMsg
            (by
              intro b tcbTid tcbB hSenderObj hSenderNext _
              obtain ⟨tcbS, hS, hSNext⟩ := endpointQueueEnqueue_enqueued_queueNext_none
                endpointId false caller st st' ep hObjInv hObjEp hEnq
              rw [hSenderObj] at hS
              obtain rfl : tcbTid = tcbS := by simpa using hS
              rw [hSNext] at hSenderNext; exact absurd hSenderNext (by simp))
            (by
              intro a tcbA _ hA hANext _
              rcases (endpointQueueEnqueue_predecessor_blocked endpointId false caller st st' ep
                hObjInv hObjEp hDQSI hTail hFreshCaller hSendTailFresh hEnq a tcbA hA hANext).2 rfl
                with h | h <;> rw [h] <;> rfl)
          show queueNextBlockingConsistent (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_queueNextBlockingConsistent st'' caller executingCore hInv2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := endpointQueuePopHead_preserves_queueNextBlockingConsistent
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent
            pair.2.2 st2 pair.1 (some msg) hInv1 hObj1 hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hInvW := wakeThread_preserves_queueNextBlockingConsistent_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hInv2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hInv4 := storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent
              (wakeThread st2 pair.1 executingCore).1 st4 caller
              (.blockedOnReply endpointId (some pair.1)) none hInvW hObjW hCS
              (fun _ _ _ _ _ _ => trivial)
              (fun _ tcbA _ _ _ _ => by cases tcbA.ipcState <;> trivial)
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hInv5 := linkServerStashedReply_preserves_queueNextBlockingConsistent
                st4 st5 caller pair.1 hObjInv4 hInv4 hLink
              show queueNextBlockingConsistent (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_queueNextBlockingConsistent st5 caller executingCore hInv5

open SeLe4n.Model.SystemState in
/-- IPC de-threading D4 Slice 2c: the cross-core endpoint call **establishes** `queueNextTargetBlocked`.
Block path: the fused sendQ enqueue+`.blockedOnCall` keystone + `removeRunnableOnCore`.  Rendezvous:
pop frame + popped receiver `.ready` store (no-incoming via the popped head) + cross-core `wakeThread`
(object-lookup-invisible) + caller `.blockedOnReply` store (non-queue-blocking; the running caller is
`.ready` — `hCallerReady` — so carries no blocked incoming link, `caller ≠ receiver` via
`hFreshCaller`) + `linkServerStashedReply` + `removeRunnableOnCore`. -/
theorem endpointCallOnCore_preserves_queueNextTargetBlocked
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hQNTB : queueNextTargetBlocked st)
    (hDQSI : dualQueueSystemInvariant st)
    (hTail : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hCallerReady : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        tcb.ipcState = .ready)
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
          ep'.receiveQ.tail ≠ some tailTid)) :
    queueNextTargetBlocked (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  have hReadyNotBlocked : (∀ ep, (ThreadIpcState.ready) ≠ .blockedOnReceive ep) ∧
      (∀ ep, (ThreadIpcState.ready) ≠ .blockedOnSend ep) ∧
      (∀ ep, (ThreadIpcState.ready) ≠ .blockedOnCall ep) :=
    ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hQNTB
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hQNTB
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hQNTB
  | some ep =>
    have hObjEp : st.objects[endpointId]? = some (.endpoint ep) :=
      (getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hQNTB
      | ok st' =>
        simp only
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hQNTB
        | ok st'' =>
          simp only
          show queueNextTargetBlocked (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_queueNextTargetBlocked st'' caller executingCore
            (endpointQueueEnqueue_blockStore_establishes_queueNextTargetBlocked endpointId false caller
              st st' st'' ep (.blockedOnCall endpointId) (some msg) hObjInv hObjEp hQNTB hTail hDQSI
              hFreshCaller hSendTailFresh (by simp) hEnq hMsg)
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hQNTB
      | ok pair =>
        simp only
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
        have hQNTB1 := endpointQueuePopHead_preserves_queueNextTargetBlocked
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hQNTB hPop
        have hNoIncPop := endpointQueuePopHead_popped_no_incoming endpointId true st pair.2.2 pair.1
          pair.2.1 hObjInv hDQSI hPop
        have hRetHead := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObjEp hPop
        have hHeadEq : ep.receiveQ.head = some pair.1 := by simpa using hRetHead
        have hCallerNeReceiver : caller.toObjId ≠ pair.1.toObjId := by
          intro h
          have hEq : caller = pair.1 := ThreadId.toObjId_injective caller pair.1 h
          exact (hFreshCaller endpointId ep hObjEp).2.2.1 (by rw [hHeadEq, hEq])
        have hNoIncPop' : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
            pair.2.2.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext = some pair.1 →
            (∀ ep, tcbA.ipcState ≠ .blockedOnReceive ep) ∧
            (∀ ep, tcbA.ipcState ≠ .blockedOnSend ep) ∧ (∀ ep, tcbA.ipcState ≠ .blockedOnCall ep) :=
          fun a tcbA hA hN => absurd hN (hNoIncPop a tcbA hA)
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hQNTB
        | ok st2 =>
          simp only
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ (some msg) hObj1 hMsg
          have hQNTB2 := storeTcbIpcStateAndMessage_no_incoming_nonQueueBlocked_preserves_queueNextTargetBlocked
            pair.2.2 st2 pair.1 .ready (some msg) hQNTB1 hObj1 hReadyNotBlocked hNoIncPop' hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hQNTBW := wakeThread_preserves_queueNextTargetBlocked_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hQNTB2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hQNTB
          | ok st4 =>
            simp only
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ none hObjW hCS
            -- caller's pre-store TCB at the wake state (without reducing the wake-state projection).
            obtain ⟨callerPost, hCallerPostGet, _⟩ := storeTcbIpcStateAndMessage_getTcb?_ipcState
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1))
              none hObjW hCS
            obtain ⟨callerTcbW, hCallerWGet, _, _⟩ := storeTcbIpcStateAndMessage_getTcb?_backward
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1))
              none hObjW hCS caller callerPost hCallerPostGet
            have hCallerMemW : (wakeThread st2 pair.1 executingCore).1.objects[caller.toObjId]? =
                some (.tcb callerTcbW) :=
              (SystemState.getTcb?_eq_some_iff _ caller callerTcbW).mp hCallerWGet
            have hCallerReadyW : callerTcbW.ipcState = .ready := by
              have hMem2 : st2.objects[caller.toObjId]? = some (.tcb callerTcbW) := by
                rw [← wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady
                  hObj2 caller.toObjId]; exact hCallerMemW
              have hMemPop : pair.2.2.objects[caller.toObjId]? = some (.tcb callerTcbW) := by
                rw [← storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ (some msg)
                  caller.toObjId hCallerNeReceiver hObj1 hMsg]; exact hMem2
              obtain ⟨stC, hStC, hIpcSt⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId true st
                pair.2.2 pair.1 caller callerTcbW hObjInv hPop hMemPop
              rw [← hIpcSt]; exact hCallerReady stC hStC
            have hCallerNotBlocked : (∀ ep, callerTcbW.ipcState ≠ .blockedOnReceive ep) ∧
                (∀ ep, callerTcbW.ipcState ≠ .blockedOnSend ep) ∧
                (∀ ep, callerTcbW.ipcState ≠ .blockedOnCall ep) :=
              ⟨fun ep => by rw [hCallerReadyW]; simp, fun ep => by rw [hCallerReadyW]; simp,
               fun ep => by rw [hCallerReadyW]; simp⟩
            have hQNTB4 := storeTcbIpcStateAndMessage_no_incoming_nonQueueBlocked_preserves_queueNextTargetBlocked
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1))
              none hQNTBW hObjW ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩
              (queueNextTargetBlocked_no_incoming_of_notQueueBlocked (wakeThread st2 pair.1 executingCore).1
                hQNTBW caller callerTcbW hCallerMemW hCallerNotBlocked) hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hQNTB
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hQNTB5 := linkServerStashedReply_preserves_queueNextTargetBlocked
                st4 st5 caller pair.1 hObjInv4 hQNTB4 hLink
              show queueNextTargetBlocked (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_queueNextTargetBlocked st5 caller executingCore hQNTB5

open SeLe4n.Model.SystemState in
/-- IPC de-threading D4 Slice 2c: the cross-core endpoint call **establishes** `queueHeadBlockedConsistent`.
Block path: the fused sendQ enqueue+`.blockedOnCall` keystone + `removeRunnableOnCore`.  Rendezvous:
pop frame (new head blocked via qNTB) + popped receiver `.ready` store (`…_popped_not_head`) +
cross-core `wakeThread` + caller `.blockedOnReply` store (`hNotHead` derived: the caller is no receiveQ
head via `hCallerNotRecv`, no sendQ head via `hFreshCaller`) + `linkServerStashedReply` +
`removeRunnableOnCore`. -/
theorem endpointCallOnCore_preserves_queueHeadBlockedConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hQHBC : queueHeadBlockedConsistent st)
    (hQNTB : queueNextTargetBlocked st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller) :
    queueHeadBlockedConsistent (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hQHBC
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hQHBC
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hQHBC
  | some ep =>
    have hObjEp : st.objects[endpointId]? = some (.endpoint ep) :=
      (getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hQHBC
      | ok st' =>
        simp only
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hQHBC
        | ok st'' =>
          simp only
          show queueHeadBlockedConsistent (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_queueHeadBlockedConsistent st'' caller executingCore
            (endpointQueueEnqueue_blockStore_establishes_queueHeadBlockedConsistent endpointId false caller
              st st' st'' ep (.blockedOnCall endpointId) (some msg) hObjInv hObjEp hQHBC hFreshCaller
              (by simp) hEnq hMsg)
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hQHBC
      | ok pair =>
        simp only
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
        have hQHBC1 := endpointQueuePopHead_preserves_queueHeadBlockedConsistent
          endpointId true st pair.2.2 pair.1 pair.2.1 ep hObjInv hObjEp hQHBC hQNTB hPop
        have hNotHeadPop := endpointQueuePopHead_popped_not_head endpointId true st pair.2.2 pair.1
          pair.2.1 ep hObjInv hObjEp hDQSI hQHBC hPop
        have hRetHead := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObjEp hPop
        have hHeadEq : ep.receiveQ.head = some pair.1 := by simpa using hRetHead
        have hCallerNeReceiver : caller.toObjId ≠ pair.1.toObjId := by
          intro h
          have hEq : caller = pair.1 := ThreadId.toObjId_injective caller pair.1 h
          exact (hFreshCaller endpointId ep hObjEp).2.2.1 (by rw [hHeadEq, hEq])
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hQHBC
        | ok st2 =>
          simp only
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ (some msg) hObj1 hMsg
          have hQHBC2 := storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
            pair.2.2 st2 pair.1 .ready (some msg) hQHBC1 hObj1 hMsg hNotHeadPop
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hQHBCW := wakeThread_preserves_queueHeadBlockedConsistent_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hQHBC2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          have hP1TcbW : ∃ t, (wakeThread st2 pair.1 executingCore).1.objects[pair.1.toObjId]? = some (.tcb t) := by
            rw [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2 pair.1.toObjId]
            exact ⟨tr, (SystemState.getTcb?_eq_some_iff st2 pair.1 tr).mp hTrGet⟩
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hQHBC
          | ok st4 =>
            simp only
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ none hObjW hCS
            obtain ⟨callerPost, hCallerPostGet, _⟩ := storeTcbIpcStateAndMessage_getTcb?_ipcState
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1))
              none hObjW hCS
            obtain ⟨callerTcbW, hCallerWGet, _, _⟩ := storeTcbIpcStateAndMessage_getTcb?_backward
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1))
              none hObjW hCS caller callerPost hCallerPostGet
            have hCallerMemW : (wakeThread st2 pair.1 executingCore).1.objects[caller.toObjId]? =
                some (.tcb callerTcbW) :=
              (SystemState.getTcb?_eq_some_iff _ caller callerTcbW).mp hCallerWGet
            -- caller's st-side TCB (transported backward through wake + receiver-store + pop).
            have hCallerStBack : ∃ stC, st.getTcb? caller = some stC ∧ stC.ipcState = callerTcbW.ipcState := by
              have hMem2 : st2.objects[caller.toObjId]? = some (.tcb callerTcbW) := by
                rw [← wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady
                  hObj2 caller.toObjId]; exact hCallerMemW
              have hMemPop : pair.2.2.objects[caller.toObjId]? = some (.tcb callerTcbW) := by
                rw [← storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ (some msg)
                  caller.toObjId hCallerNeReceiver hObj1 hMsg]; exact hMem2
              obtain ⟨stC, hStC, hIpcSt⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId true st
                pair.2.2 pair.1 caller callerTcbW hObjInv hPop hMemPop
              exact ⟨stC, (SystemState.getTcb?_eq_some_iff st caller stC).mpr hStC, hIpcSt⟩
            obtain ⟨stC, hStCMem, hStCIpc⟩ := hCallerStBack
            -- caller is not a head of any queue at the caller-store pre-state (the wake state).
            have hCallerNotHead : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                (wakeThread st2 pair.1 executingCore).1.objects[epId']? = some (.endpoint ep') →
                ep'.receiveQ.head ≠ some caller ∧ ep'.sendQ.head ≠ some caller := by
              intro epId' ep' hEpW
              refine ⟨fun hHd => ?_, fun hHd => ?_⟩
              · have hBlocked := (hQHBCW epId' ep' caller callerTcbW hEpW hCallerMemW).1 hHd
                rw [← hStCIpc] at hBlocked
                exact hCallerNotRecv stC hStCMem epId' hBlocked
              · rw [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady
                  hObj2 epId'] at hEpW
                have hEpNeP1 : epId' ≠ pair.1.toObjId := by
                  intro h; rw [h] at hEpW
                  obtain ⟨t, hP1⟩ := hP1TcbW
                  rw [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady
                    hObj2 pair.1.toObjId] at hP1
                  rw [hP1] at hEpW; cases hEpW
                have hEpPop : pair.2.2.objects[epId']? = some (.endpoint ep') := by
                  rw [← storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ (some msg)
                    epId' hEpNeP1 hObj1 hMsg]; exact hEpW
                by_cases hEpEq : epId' = endpointId
                · subst epId'
                  obtain ⟨epP, hEpP, _, hOtherHead⟩ :=
                    endpointQueuePopHead_post_endpoint_queues endpointId true st pair.2.2 pair.1 pair.2.1
                      ep hObjInv hObjEp hPop
                  rw [hEpPop] at hEpP
                  obtain rfl : ep' = epP := by simpa using hEpP
                  simp only [↓reduceIte] at hOtherHead
                  rw [hOtherHead] at hHd
                  exact (hFreshCaller endpointId ep hObjEp).1 hHd
                · have hEpSt := endpointQueuePopHead_endpoint_backward_ne endpointId true st pair.2.2 pair.1
                    epId' ep' hEpEq hObjInv hPop hEpPop
                  exact (hFreshCaller epId' ep' hEpSt).1 hHd
            have hQHBC4 := storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
              (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1))
              none hQHBCW hObjW hCS hCallerNotHead
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hQHBC
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hQHBC5 := linkServerStashedReply_preserves_queueHeadBlockedConsistent
                st4 st5 caller pair.1 hObjInv4 hQHBC4 hLink
              show queueHeadBlockedConsistent (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_queueHeadBlockedConsistent st5 caller executingCore hQHBC5

/-- IPC de-threading D4 Slice 2b: `removeRunnableOnCore` frames
`endpointQueueTailBlockedConsistent` (object-store frame — `objects` unchanged). -/
theorem removeRunnableOnCore_preserves_endpointQueueTailBlockedConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent (removeRunnableOnCore st tid c) :=
  endpointQueueTailBlockedConsistent_of_objects_eq
    (removeRunnableOnCore_preserves_objects st tid c) h

/-- IPC de-threading D4 Slice 2b: the cross-core wake of an already-`.ready` thread preserves
`endpointQueueTailBlockedConsistent` (the wake's `ipcState := .ready` re-insert is
object-lookup-invisible — the §2 keystone — and the invariant is lookup-only). -/
theorem wakeThread_preserves_endpointQueueTailBlockedConsistent_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent (wakeThread st tid ec).1 := by
  refine endpointQueueTailBlockedConsistent_of_endpoint_tcb_backward st (wakeThread st tid ec).1 ?_ ?_ h
  · intro eid ep hEp
    rwa [wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv eid] at hEp
  · intro y tcb' hY
    rw [wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv y.toObjId] at hY
    exact ⟨tcb', hY, rfl⟩

open SeLe4n.Model.SystemState in
/-- IPC de-threading D4 Slice 2b: the cross-core endpoint call **establishes**
`endpointQueueTailBlockedConsistent`.  Mirrors the single-core
`endpointCall_preserves_endpointQueueTailBlockedConsistent` (block branch: sendQ enqueue +
`.blockedOnCall` block-store discharged via core (c)
`endpointQueueEnqueue_blockStore_establishes_endpointQueueTailBlockedConsistent`; rendezvous
branch: receiveQ pop [popped head not a post-pop tail via core (a)
`endpointQueuePopHead_popped_not_tail`] + receiver `.ready` store + caller `.blockedOnReply`
store [caller fresh ⇒ not a post-pop tail] + `linkServerStashedReply`), with the receiver wake
framed by `wakeThread_preserves_endpointQueueTailBlockedConsistent_of_ready` (the receiver is
`.ready` after its message store, so the wake is object-invisible) and the caller deschedule by
`removeRunnableOnCore`'s object-store frame. -/
theorem endpointCallOnCore_preserves_endpointQueueTailBlockedConsistent
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hTail : endpointQueueTailBlockedConsistent st)
    (hDQSI : dualQueueSystemInvariant st)
    (hQHBC : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller) :
    endpointQueueTailBlockedConsistent (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hTail
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hTail
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hTail
  | some ep =>
    have hObjEp : st.objects[endpointId]? = some (.endpoint ep) :=
      (getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hTail
      | ok st' =>
        simp only
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hTail
        | ok st'' =>
          simp only
          show endpointQueueTailBlockedConsistent (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_endpointQueueTailBlockedConsistent st'' caller executingCore <|
            endpointQueueEnqueue_blockStore_establishes_endpointQueueTailBlockedConsistent
              endpointId false caller st st' st'' ep (.blockedOnCall endpointId) (some msg)
              hObjInv hObjEp hTail
              (fun epId e hE => ⟨(hFreshCaller epId e hE).2.1, (hFreshCaller epId e hE).2.2.2⟩)
              (by simp) hEnq hMsg
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hTail
      | ok pair =>
        simp only
        have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2
          pair.1 pair.2.1 hObjInv hPop
        have hTail1 := endpointQueuePopHead_preserves_endpointQueueTailBlockedConsistent endpointId true st
          pair.2.2 pair.1 pair.2.1 hObjInv hTail hPop
        have hRecvNotTail := endpointQueuePopHead_popped_not_tail endpointId true st pair.2.2 pair.1
          pair.2.1 ep hObjInv hObjEp hDQSI hQHBC hTail hPop
        have hCallerNotTailPop := endpointQueuePopHead_fresh_not_tail endpointId true st pair.2.2 pair.1
          pair.2.1 ep caller hObjInv hObjEp
          (fun epId e hE => ⟨(hFreshCaller epId e hE).2.2.2, (hFreshCaller epId e hE).2.1⟩) hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hTail
        | ok st2 =>
          simp only
          have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _
            (some msg) hObjInv1 hMsg
          have hTail2 := storeTcbIpcStateAndMessage_preserves_endpointQueueTailBlockedConsistent
            pair.2.2 st2 pair.1 .ready (some msg) hTail1 hObjInv1 hMsg hRecvNotTail
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg
          have hTailW := wakeThread_preserves_endpointQueueTailBlockedConsistent_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObjInv2 hTail2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObjInv2
          have hCallerNotTailW : ∀ (epId : SeLe4n.ObjId) (e : Endpoint),
              (wakeThread st2 pair.1 executingCore).1.objects[epId]? = some (.endpoint e) →
              e.receiveQ.tail ≠ some caller ∧ e.sendQ.tail ≠ some caller := by
            intro epId e hE
            rw [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObjInv2 epId] at hE
            exact hCallerNotTailPop epId e
              (storeTcbIpcStateAndMessage_endpoint_backward pair.2.2 st2 pair.1 .ready (some msg) epId e hObjInv1 hMsg hE)
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hTail
          | ok st4 =>
            simp only
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ none hObjW hCS
            have hTail4 := storeTcbIpcStateAndMessage_preserves_endpointQueueTailBlockedConsistent
              (wakeThread st2 pair.1 executingCore).1 st4 caller
              (.blockedOnReply endpointId (some pair.1)) none hTailW hObjW hCS hCallerNotTailW
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hTail
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hTail5 := linkServerStashedReply_preserves_endpointQueueTailBlockedConsistent
                st4 st5 caller pair.1 hObjInv4 hTail4 hLink
              show endpointQueueTailBlockedConsistent (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_endpointQueueTailBlockedConsistent st5 caller executingCore hTail5

-- ============================================================================
-- §7  SM6.A.1 — the remaining derivable conjuncts + full `ipcInvariantFull`
-- ============================================================================

/-! `allPendingMessagesBounded` and `badgeWellFormed` are likewise lookup-only,
so the cross-core scheduler steps frame them; the message stores reuse the
single-core per-step lemmas (the payload is bounded by the entry guards). -/

/-- Pointwise-lookup transport of pending-message boundedness. -/
theorem allPendingMessagesBounded_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : allPendingMessagesBounded s1) : allPendingMessagesBounded s2 := by
  intro tid tcb msg hObj hPend
  rw [hEq] at hObj
  exact h tid tcb msg hObj hPend

/-- Pointwise-lookup transport of badge well-formedness (notification + cap). -/
theorem badgeWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : badgeWellFormed s1) : badgeWellFormed s2 := by
  obtain ⟨hNtfn, hCap⟩ := h
  refine ⟨fun oid ntfn badge hObj hBadge => ?_, fun oid cn slot cap badge hObj hLk hBadge => ?_⟩
  · rw [hEq] at hObj; exact hNtfn oid ntfn badge hObj hBadge
  · rw [hEq] at hObj; exact hCap oid cn slot cap badge hObj hLk hBadge

/-- `removeRunnableOnCore` frames pending-message boundedness. -/
theorem removeRunnableOnCore_preserves_allPendingMessagesBounded
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded (removeRunnableOnCore st tid c) :=
  allPendingMessagesBounded_of_getElem_eq
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- `removeRunnableOnCore` frames badge well-formedness. -/
theorem removeRunnableOnCore_preserves_badgeWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : badgeWellFormed st) :
    badgeWellFormed (removeRunnableOnCore st tid c) :=
  badgeWellFormed_of_getElem_eq
    (fun _ => by rw [removeRunnableOnCore_preserves_objects]) h

/-- The ready-thread cross-core wake frames pending-message boundedness. -/
theorem wakeThread_preserves_allPendingMessagesBounded_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded (wakeThread st tid ec).1 :=
  allPendingMessagesBounded_of_getElem_eq
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

/-- The ready-thread cross-core wake frames badge well-formedness. -/
theorem wakeThread_preserves_badgeWellFormed_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (h : badgeWellFormed st) :
    badgeWellFormed (wakeThread st tid ec).1 :=
  badgeWellFormed_of_getElem_eq
    (fun oid => wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hObjInv oid) h

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves badge well-formedness.
The message stores write a TCB (never a notification/CNode), so they frame the
badge predicate via the single-core per-step lemmas; the wake/deschedule are
object-lookup frames. -/
theorem endpointCallOnCore_preserves_badgeWellFormed
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : badgeWellFormed st) (hObjInv : st.objects.invExt) :
    badgeWellFormed (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hInv1 := endpointQueueEnqueue_preserves_badgeWellFormed
          endpointId false caller st st' hObjInv hEnq hInv
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt
          endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
            st' st'' caller _ _ hInv1 hObj1 hMsg
          show badgeWellFormed (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_badgeWellFormed st'' caller executingCore hInv2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := endpointQueuePopHead_preserves_badgeWellFormed
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop hInv
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
            pair.2.2 st2 pair.1 _ _ hInv1 hObj1 hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hInvW := wakeThread_preserves_badgeWellFormed_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hInv2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hInv4 := storeTcbIpcStateAndMessage_preserves_badgeWellFormed
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hInvW hObjW hCS
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hInv5 := linkServerStashedReply_preserves_badgeWellFormed st4 st5 caller pair.1 hInv4 hObjInv4 hLink
              show badgeWellFormed (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_badgeWellFormed st5 caller executingCore hInv5

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves pending-message
boundedness.  The payload `msg` is bounded by the two entry guards (`hSz1`/`hSz2`
⇒ `msg.bounded`), so every store of `some msg` lands a bounded message; the
reply-block store lands `none`; the wake/deschedule are object frames. -/
theorem endpointCallOnCore_preserves_allPendingMessagesBounded
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : allPendingMessagesBounded st) (hObjInv : st.objects.invExt) :
    allPendingMessagesBounded (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  have hMsgBounded : msg.bounded := ⟨by omega, by omega⟩
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hInv1 := endpointQueueEnqueue_preserves_allPendingMessagesBounded
          endpointId false caller st st' hObjInv hEnq hInv
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt
          endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
            st' st'' caller _ _ (fun m hm => by cases hm; exact hMsgBounded) hObj1 hMsg hInv1
          show allPendingMessagesBounded (removeRunnableOnCore st'' caller executingCore)
          exact removeRunnableOnCore_preserves_allPendingMessagesBounded st'' caller executingCore hInv2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := endpointQueuePopHead_preserves_allPendingMessagesBounded
          endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop hInv
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt
          endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
            pair.2.2 st2 pair.1 _ _ (fun m hm => by cases hm; exact hMsgBounded) hObj1 hMsg hInv1
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt
            pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hInvW := wakeThread_preserves_allPendingMessagesBounded_of_ready
            st2 pair.1 executingCore tr hTrGet hTrReady hObj2 hInv2
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hInv4 := storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ none
              (fun _ h => by cases h) hObjW hCS hInvW
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hInv5 := linkServerStashedReply_preserves_allPendingMessagesBounded st4 st5 caller pair.1 hObjInv4 hLink hInv4
              show allPendingMessagesBounded (removeRunnableOnCore st5 caller executingCore)
              exact removeRunnableOnCore_preserves_allPendingMessagesBounded st5 caller executingCore hInv5

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.A.1 (D3): the cross-core endpoint call **preserves**
`pendingReceiveReplyWellFormed`.  The cross-core analogue of
`endpointCall_preserves_pendingReceiveReplyWellFormed`: the receiver wake is
object-invisible (the receiver is `.ready` post-deliver, so `wakeThread` reinserts
the same value — `wakeThread_objects_getElem_eq_of_ready`), and the per-core
deschedule frames objects, so the same object-level reasoning carries.  The
server-waiting branch routes through the shared
`linkServerStashedReply_preserves_pendingReceiveReplyWellFormed` crux frame, with
`hC1Other`/`hC2` discharged from the post-pop PRR by framing the deliver/block stores
(stash-preserving) and the object-invisible wake.  `hCallerNotRecv` prevents the
caller's block-store from stranding a stash. -/
theorem endpointCallOnCore_preserves_pendingReceiveReplyWellFormed
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep) :
    pendingReceiveReplyWellFormed (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      -- Blocking branch: caller enqueues then becomes `.blockedOnCall`.
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st1 =>
        simp only
        have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
        have hP1 := endpointQueueEnqueue_preserves_pendingReceiveReplyWellFormed endpointId false caller st st1 hObjInv hInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hP2 := storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
            st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInv1 hP1 ?_ hMsg
          · show pendingReceiveReplyWellFormed (removeRunnableOnCore st2 caller executingCore)
            exact pendingReceiveReplyWellFormed_of_objects_eq
              (removeRunnableOnCore_preserves_objects st2 caller executingCore) hP2
          · intro tcb' hTcb' ep' h
            obtain ⟨tcb0, hTcb0, hIpcEq⟩ := endpointQueueEnqueue_tcb_ipcState_backward
              endpointId false caller st st1 caller tcb' hObjInv hEnq
              ((getTcb?_eq_some_iff st1 caller tcb').mp hTcb')
            exact hCallerNotRecv tcb0 ((getTcb?_eq_some_iff st caller tcb0).mpr hTcb0) ep' (hIpcEq.trans h)
    | some _ =>
      -- Server-waiting branch.
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hP1 : pendingReceiveReplyWellFormed pair.2.2 :=
          endpointQueuePopHead_preserves_pendingReceiveReplyWellFormed endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
        have hCallerNotRecv1 : ∀ (tcb : TCB), pair.2.2.getTcb? caller = some tcb →
            ∀ ep', tcb.ipcState ≠ .blockedOnReceive ep' := by
          intro tcb hTcb ep' hBlk
          obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2.2 pair.1 caller tcb hObjInv hPop ((getTcb?_eq_some_iff pair.2.2 caller tcb).mp hTcb)
          exact hCallerNotRecv tcb0 ((getTcb?_eq_some_iff st caller tcb0).mpr hTcb0) ep' (hIpc0 ▸ hBlk)
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObjInv1 hMsg
          -- the receiver is `.ready` at `st2`, so the wake is object-invisible.
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg
          have hWakeObjEq : ∀ oid, (wakeThread st2 pair.1 executingCore).1.objects[oid]? = st2.objects[oid]? :=
            fun oid => wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObjInv2 oid
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObjInv2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              -- Back-frame TCB reads from `st4` to the post-pop state `pair.2.2`.
              have hBackTcb : ∀ (y : SeLe4n.ThreadId) (tcY : TCB), st4.getTcb? y = some tcY →
                  ∃ tc0, pair.2.2.getTcb? y = some tc0 ∧
                    tc0.pendingReceiveReply = tcY.pendingReceiveReply ∧
                    (y ≠ pair.1 → y ≠ caller → tc0.ipcState = tcY.ipcState) := by
                intro y tcY hY4
                -- st4 → wakeThread st2 (block store, target `caller`).
                obtain ⟨tcW, hTcW, hStashW, hIpcW⟩ :=
                  storeTcbIpcStateAndMessage_getTcb?_backward (wakeThread st2 pair.1 executingCore).1 st4 caller _ none hObjW hCS y tcY hY4
                -- wakeThread st2 → st2 (objects-invisible).
                have hTc2 : st2.getTcb? y = some tcW := by
                  unfold getTcb? at hTcW ⊢; rwa [hWakeObjEq] at hTcW
                -- st2 → pair.2.2 (deliver store, target `pair.1`).
                obtain ⟨tc0, hTc0, hStash0, hIpc0⟩ :=
                  storeTcbIpcStateAndMessage_getTcb?_backward pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg y tcW hTc2
                refine ⟨tc0, hTc0, hStash0.trans hStashW, ?_⟩
                intro hyP hyC
                rw [hIpc0 hyP, hIpcW hyC]
              -- The deliver/block stores' target slots each held a TCB pre-store.
              have hDelivTarget : ∃ t, pair.2.2.objects[pair.1.toObjId]? = some (.tcb t) := by
                unfold storeTcbIpcStateAndMessage at hMsg
                cases hL : lookupTcb pair.2.2 pair.1 with
                | none => simp [hL] at hMsg
                | some t => exact ⟨t, lookupTcb_some_objects pair.2.2 pair.1 t hL⟩
              have hBlockTarget : ∃ t, (wakeThread st2 pair.1 executingCore).1.objects[caller.toObjId]? = some (.tcb t) := by
                cases hL : lookupTcb (wakeThread st2 pair.1 executingCore).1 caller with
                | none => rw [storeTcbIpcStateAndMessage, hL] at hCS; simp at hCS
                | some t => exact ⟨t, lookupTcb_some_objects (wakeThread st2 pair.1 executingCore).1 caller t hL⟩
              -- `getReply?` frames from `pair.2.2` through the deliver/wake/block stores.
              have hReplyFrame : ∀ (r' : SeLe4n.ReplyId) (rr : Reply),
                  pair.2.2.getReply? r' = some rr → st4.getReply? r' = some rr := by
                intro r' rr hR
                have hRobj : pair.2.2.objects[r'.toObjId]? = some (.reply rr) := (getReply?_eq_some_iff pair.2.2 r' rr).mp hR
                have hNe2 : r'.toObjId ≠ pair.1.toObjId := by
                  intro hEq; obtain ⟨t1, ht1⟩ := hDelivTarget; rw [hEq, ht1] at hRobj; cases hRobj
                rw [getReply?_eq_some_iff]
                have hStep1 : st2.objects[r'.toObjId]? = pair.2.2.objects[r'.toObjId]? :=
                  storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ (some msg) r'.toObjId hNe2 hObjInv1 hMsg
                have hStep2 : (wakeThread st2 pair.1 executingCore).1.objects[r'.toObjId]? = st2.objects[r'.toObjId]? :=
                  hWakeObjEq r'.toObjId
                have hNe4 : r'.toObjId ≠ caller.toObjId := by
                  intro hEq; obtain ⟨tc0c, hcObj⟩ := hBlockTarget
                  have hRobj2 : (wakeThread st2 pair.1 executingCore).1.objects[r'.toObjId]? = some (.reply rr) := by
                    rw [hStep2, hStep1]; exact hRobj
                  rw [hEq, hcObj] at hRobj2; cases hRobj2
                have hStep3 : st4.objects[r'.toObjId]? = (wakeThread st2 pair.1 executingCore).1.objects[r'.toObjId]? :=
                  storeTcbIpcStateAndMessage_preserves_objects_ne (wakeThread st2 pair.1 executingCore).1 st4 caller _ none r'.toObjId hNe4 hObjW hCS
                rw [hStep3, hStep2, hStep1]; exact hRobj
              -- Apply the shared `linkServerStashedReply` crux frame from the post-pop PRR.
              have hP5 : pendingReceiveReplyWellFormed st5 := by
                refine linkServerStashedReply_preserves_pendingReceiveReplyWellFormed st4 st5 caller pair.1 hObjInv4 ?_ ?_ hLink
                · intro tid tcb ridX hTNeServer hT4 hStash4
                  obtain ⟨tc0, hTc0, hStash0, hIpc0⟩ := hBackTcb tid tcb hT4
                  have hStashX0 : tc0.pendingReceiveReply = some ridX := hStash0.trans hStash4
                  have hTNeCaller : tid ≠ caller := by
                    intro hEqC; subst hEqC
                    obtain ⟨hBlk0, _⟩ := hP1.1 tid tc0 ridX hTc0 hStashX0
                    obtain ⟨epx, hepx⟩ := hBlk0
                    exact hCallerNotRecv1 tc0 hTc0 epx hepx
                  obtain ⟨hBlk0, hFreeReply0⟩ := hP1.1 tid tc0 ridX hTc0 hStashX0
                  refine ⟨?_, ?_⟩
                  · rw [← hIpc0 hTNeServer hTNeCaller]; exact hBlk0
                  · obtain ⟨rr, hGetRR, hRRfree⟩ := hFreeReply0
                    exact ⟨rr, hReplyFrame ridX rr hGetRR, hRRfree⟩
                · intro tid₁ tid₂ tcb₁ tcb₂ ridX hT4₁ hT4₂ hStash4₁ hStash4₂
                  obtain ⟨tc0₁, hTc0₁, hStash0₁, _⟩ := hBackTcb tid₁ tcb₁ hT4₁
                  obtain ⟨tc0₂, hTc0₂, hStash0₂, _⟩ := hBackTcb tid₂ tcb₂ hT4₂
                  exact hP1.2 tid₁ tid₂ tc0₁ tc0₂ ridX hTc0₁ hTc0₂ (hStash0₁.trans hStash4₁) (hStash0₂.trans hStash4₂)
              show pendingReceiveReplyWellFormed (removeRunnableOnCore st5 caller executingCore)
              exact pendingReceiveReplyWellFormed_of_objects_eq
                (removeRunnableOnCore_preserves_objects st5 caller executingCore) hP5

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves the **full** IPC
invariant bundle.  Mirrors the single-core `endpointCall_preserves_ipcInvariantFull`
and *strengthens* it: where the single-core theorem derives three conjuncts
internally (`ipcInvariant`, `allPendingMessagesBounded`, `badgeWellFormed`) and
carries the rest as post-state hypotheses, this proof derives a **fourth**, the
structural `dualQueueSystemInvariant`, from the lookup-only congruence of §5–§6.
The remaining eleven conjuncts are carried on the post-state exactly as the
single-core theorem carries them — they are either scheduler-sensitive (e.g.
`passiveServerIdle`, which reads the per-core run queue and so is genuinely not
an object-store frame of this operation) or depend on cross-cutting queue-shape
facts the single-core proof also defers to its caller.  `hFreshCaller` /
`hSendTailFresh` are the no-receiver-enqueue side-conditions inherited from the
dual-queue step. -/
theorem endpointCallOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st st' : SystemState)
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
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
    (hStep : (endpointCallOnCore endpointId caller msg executingCore st).1 = st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    -- IPC de-threading D4 Slice 2c: the running syscall caller is `.ready` (establishes the strict
    -- `queueNextTargetBlocked` — a `.ready` thread carries no blocked incoming link; dischargeable at D8).
    (hCallerReady : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        tcb.ipcState = .ready)
    -- IPC de-threading D6: the syscall caller is running, not awaiting a reply.
    (hCallerNotReply : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    -- IPC de-threading D6: the running caller holds a SchedContext (own or donated).
    (hCallerNotUnbound : ∀ (tcb : TCB), st.objects[caller.toObjId]? = some (.tcb tcb) →
        tcb.schedContextBinding ≠ .unbound) :
    ipcInvariantFull st' := by
  subst hStep
  -- IPC de-threading D6: `donationOwnerValid` **established** from the pre-state via the
  -- backward `sameSchedContextBindings` + forward `donationOwnerFrame` halves.
  have hDOVest := donationOwnerValid_of_frames
    (endpointCallOnCore_sameSchedContextBindings endpointId caller msg executingCore st hObjInv)
    (endpointCallOnCore_donationOwnerFrame endpointId caller msg executingCore st hObjInv
      hInv.queueHeadBlockedConsistent hCallerNotReply)
    hInv.donationOwnerValid
  -- IPC de-threading D6: `passiveServerIdle` **established** — the block-path `.blockedOnCall`
  -- descheduled caller holds a SchedContext; per-core locality frames the boot-core run queue
  -- whether or not `executingCore` is the boot core.
  have hPSIest := endpointCallOnCore_preserves_passiveServerIdle endpointId caller msg executingCore st
    hObjInv hCallerNotUnbound hInv.passiveServerIdle
  exact ⟨endpointCallOnCore_preserves_ipcInvariant endpointId caller msg executingCore st hInv.1 hObjInv,
    endpointCallOnCore_preserves_dualQueueSystemInvariant endpointId caller msg executingCore st
      hInv.2.1 hObjInv hFreshCaller hSendTailFresh,
    endpointCallOnCore_preserves_allPendingMessagesBounded endpointId caller msg executingCore st
      hInv.2.2.1 hObjInv,
    endpointCallOnCore_preserves_badgeWellFormed endpointId caller msg executingCore st
      hInv.2.2.2.1 hObjInv,
    hWtpmn',
    -- IPC de-threading D8: endpointQueueNoDup **established** from the pre-state (cross-core
    -- enqueue/pop + the object-invisible wake + scheduler-op deschedule).
    endpointCallOnCore_preserves_endpointQueueNoDup endpointId caller msg executingCore st
      hInv.endpointQueueNoDup hInv.2.1 hObjInv hFreshCaller hSendTailFresh,
    -- IPC de-threading D8: ipcStateQueueMembershipConsistent **established** from the pre-state
    -- (rendezvous pop-except-head + head→.ready + object-invisible wake; block enqueue-reachable).
    endpointCallOnCore_preserves_ipcStateQueueMembershipConsistent endpointId caller msg executingCore st
      hInv hObjInv hFreshCaller hSendTailFresh,
    -- IPC de-threading D4 Slice 2b: queueNext **established** from the pre-state (cross-core enqueue-establish).
    endpointCallOnCore_preserves_queueNextBlockingConsistent endpointId caller msg executingCore st
      hInv.queueNextBlockingConsistent hInv.2.1 hInv.endpointQueueTailBlockedConsistent hObjInv
      hFreshCaller hSendTailFresh,
    -- IPC de-threading D4 Slice 2c: queueHeadBlockedConsistent **established** from the pre-state —
    -- the rendezvous pop's new head is blocked via qNTB; the block-path enqueue keystone blocks the caller.
    endpointCallOnCore_preserves_queueHeadBlockedConsistent endpointId caller msg executingCore st
      hInv.queueHeadBlockedConsistent hInv.queueNextTargetBlocked hInv.2.1 hObjInv hCallerNotRecv hFreshCaller,
    -- IPC de-threading D5: `blockedThreadTimeoutConsistent` **established** from `allTimeoutBudgetsNone`.
    endpointCallOnCore_preserves_blockedThreadTimeoutConsistent endpointId caller msg executingCore st hObjInv hAllBudgetsNone,
    -- IPC de-threading D7: derive `donationChainAcyclic` from the threaded post-state
    -- `donationOwnerValid` via the subsumption lemma.
    -- IPC de-threading D6 (donationBudgetTransfer): **establish** from the pre-state via the
    -- `sameSchedContextBindings` frame — `endpointCallOnCore` never writes any TCB's
    -- `schedContextBinding` (its store-ops are ipcState / queue-link / scheduler writes), so the
    -- post-state budget-transfer invariant holds whenever the pre-state one does.
    donationOwnerValid_implies_donationChainAcyclic _ hDOVest, hDOVest, hPSIest,
    donationBudgetTransfer_of_sameSchedContextBindings
      (endpointCallOnCore_sameSchedContextBindings endpointId caller msg executingCore st hObjInv)
      hInv.donationBudgetTransfer,
    endpointCallOnCore_establishes_blockedOnReplyHasTarget endpointId caller msg executingCore st hInv.blockedOnReplyHasTarget hObjInv,
    ⟨hRCLRecip', endpointCallOnCore_establishes_blockedOnReplyHasReplyObject endpointId caller msg
      executingCore st hInv.replyCallerLinkage.2 hObjInv⟩,
    -- IPC de-threading D3: **establish** PRR from the pre-state (was threaded `hPRR'`).
    endpointCallOnCore_preserves_pendingReceiveReplyWellFormed endpointId caller msg executingCore st
      hObjInv hInv.pendingReceiveReplyWellFormed hCallerNotRecv,
    donationOwnerUnique_of_sameSchedContextBindings
      (endpointCallOnCore_sameSchedContextBindings endpointId caller msg executingCore st hObjInv)
      hInv.donationOwnerUnique,
    -- IPC de-threading D4 Slice 2b: tail-blocked **established** from the pre-state (cross-core
    -- enqueue/pop-establish via cores (a)+(c); wake + deschedule are object-invisible frames).
    endpointCallOnCore_preserves_endpointQueueTailBlockedConsistent endpointId caller msg executingCore
      st hInv.endpointQueueTailBlockedConsistent hInv.2.1 hInv.queueHeadBlockedConsistent hObjInv
      hFreshCaller,
    -- IPC de-threading D4 Slice 2c: queueNextTargetBlocked **established** from the pre-state — the
    -- rendezvous pop frames qNTB, the no-incoming receiver/caller stores preserve it (wake is
    -- object-invisible), and the block leg is the fused enqueue+`.blockedOnCall` keystone.
    endpointCallOnCore_preserves_queueNextTargetBlocked endpointId caller msg executingCore st
      hInv.queueNextTargetBlocked hInv.2.1 hInv.endpointQueueTailBlockedConsistent hObjInv hCallerReady
      hFreshCaller hSendTailFresh⟩

end SeLe4n.Kernel
