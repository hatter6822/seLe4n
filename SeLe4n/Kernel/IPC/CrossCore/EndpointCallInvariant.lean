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
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
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
    hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout',
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
      hInv.donationOwnerUnique⟩

end SeLe4n.Kernel
