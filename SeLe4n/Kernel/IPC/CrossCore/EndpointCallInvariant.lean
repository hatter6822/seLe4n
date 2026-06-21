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
congruence).  The one exception is `passiveServerIdle`, which reads the per-core
run queue and current thread, so it is genuinely scheduler-sensitive and is
carried on the post-state as a hypothesis — exactly as the single-core
`endpointCall_preserves_ipcInvariantFull` carries its structural conjuncts.
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
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hPRR' : pendingReceiveReplyWellFormed st') :
    ipcInvariantFull st' := by
  subst hStep
  exact ⟨endpointCallOnCore_preserves_ipcInvariant endpointId caller msg executingCore st hInv.1 hObjInv,
    endpointCallOnCore_preserves_dualQueueSystemInvariant endpointId caller msg executingCore st
      hInv.2.1 hObjInv hFreshCaller hSendTailFresh,
    endpointCallOnCore_preserves_allPendingMessagesBounded endpointId caller msg executingCore st
      hInv.2.2.1 hObjInv,
    endpointCallOnCore_preserves_badgeWellFormed endpointId caller msg executingCore st
      hInv.2.2.2.1 hObjInv,
    hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', hDCA', hDOV', hPSI', hDBT',
    endpointCallOnCore_establishes_blockedOnReplyHasTarget endpointId caller msg executingCore st hInv.blockedOnReplyHasTarget hObjInv,
    ⟨hRCLRecip', endpointCallOnCore_establishes_blockedOnReplyHasReplyObject endpointId caller msg
      executingCore st hInv.replyCallerLinkage.2 hObjInv⟩,
    hPRR'⟩

end SeLe4n.Kernel
